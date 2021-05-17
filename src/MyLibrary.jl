module MyLibrary


greet() = println("HelloWorld")


"""
    bisect(f, a, b; iter_max=1000, rtol=1e-10, args=())

Bisection routine to find a zero of the function f between the arguments a and b. f(a) and f(b) cannot have the same signs.
"""
function bisect(f, a, b; iter_max=1000, rtol=1e-10, args=())
    @assert a < b 
    @assert f(a, args...)*f(b, args...) ≤ 0
    @assert rtol > 0
    
    x1 = a
    x2 = b
    xm = (x1 + x2)/2
    
    for iter in 1:iter_max
        if f(x1, args...)*f(xm, args...) ≤ 0
            x2 = xm
        else
            x1 = xm
        end
        xm = (x1 + x2)/2
        if abs((x1-x2)/x1) < rtol
            return x1
        end
    end
    error("no convergence!")
end
export bisect 


"""
    numerov(ir, rs, k², S, f_old, f; sign=1)

Solve second-order differential equations w.r.t f(r) having the form of
    d²f(r)/dx² + k²(r) f(r) = S(r)
by numerov's method.
"""
function numerov(ir, rs, k², S, f_old, f; sign=1) 
    @assert 2 ≤ ir ≤ length(rs)-1 && abs(sign) == 1
    
    h = rs[2]-rs[1] 
    
    f_new = 2(1 - (5h^2/12)*k²[ir])*f - (1 + (h^2/12)*k²[ir-sign])*f_old + (h^2/12)*(S[ir+1] + 10S[ir] + S[ir-1])
    f_new /= 1 + (h^2/12)*k²[ir+sign]
    
    return f_new
end


"""
Solve Poisson equation 
    -d²/dr² rϕ(r) = 4πrρ(r)   with   ∫ dr 4πr² ρ(r) = Z
by Numerov's method
"""
function solve_poisson(Z, rs, ρ)
    k² = zeros(Float64, length(rs)) 
    
    S = zeros(Float64, length(rs))
    @. S = -4π*rs*ρ
    
    ϕ = zeros(Float64, length(rs))
    ϕ[end-1] = Z
    ϕ[end] = Z
    
    for ir in length(rs)-1: -1:2
        ϕ[ir-1] = numerov(ir, rs, k², S, ϕ[ir+1], ϕ[ir], sign=-1)
    end
    @. ϕ = ϕ/rs
    
    return ϕ
end

    
    
"""
    clebsch(j₁, m₁, j₂, m₂, j, m)

Calculate Clebsch-Gordan coefficients.
All spins are expressed as double their actual values.
"""
function clebsch(j₁, m₁, j₂, m₂, j, m)
    @assert abs(m₁) ≤ j₁ && iseven(j₁ - m₁)
    @assert abs(m₂) ≤ j₂ && iseven(j₂ - m₂)
    @assert abs(m) ≤ j && iseven(j - m)
    
    # j = |j₁ - j₂|, |j₁ - j₂|+1, ..., j₁ + j₂
    if j < abs(j₁ - j₂) || j > j₁ + j₂ || isodd(j - j₁ - j₂)
        return 0.0
    end
    
    if m ≠ m₁ + m₂
        return 0.0
    end
    
    function f(n)
        @assert n ≥ 0
        s = 1.0
        for i in 2:div(n, 2)
            s *= i
        end
        return s
    end
    
    con = (j+1)*f(j₁+j₂-j)*f(j₁-j₂+j)*f(-j₁+j₂+j) / f(j₁+j₂+j+2)
    con *= f(j₁+m₁)*f(j₁-m₁)*f(j₂+m₂)*f(j₂-m₂)*f(j+m)*f(j-m)
    con = sqrt(con)
    
    sum = 0.0
    for z in max(0, -j+j₂-m₁, -j+j₁+m₂): 2: min(j₁+j₂-j, j₁-m₁, j₂+m₂)
        sum += (-1)^div(z,2)/( f(z)*f(j₁+j₂-j-z)*f(j₁-m₁-z)*f(j₂+m₂-z)*f(j-j₂+m₁+z)*f(j-j₁-m₂+z) )
    end
    
    return con*sum
end


"""
    clebsch2(l₁, m₁, l₂, m₂, l, m)

Calculate clebsch-gordan coefficient for integer spins.
"""
function clebsch2(l₁, m₁, l₂, m₂, l, m)
    clebsch(2l₁, 2m₁, 2l₂, 2m₂, 2l, 2m)
end


"""
    wigner3j(j₁, j₂, j₃, m₁, m₂, m₃)

Calculate wigner 3j symbol.
All spins are expressed as double their actual values.
"""
function wigner3j(j₁, j₂, j₃, m₁, m₂, m₃)
    return (-1)^div(j₁-j₂-m₃,2)/sqrt(j₃+1)*clebsch(j₁, m₁, j₂, m₂, j₃, -m₃)
end



function spherical_bessel(nu, x) 
    if nu < 0
        error("nu must be greater than or equal to 0.")
    elseif nu == 0 
        return sin(x)/x
    elseif nu == 1
        return sin(x)/(x*x) - cos(x)/x
    else
        return (2nu - 1)/x * spherical_bessel(nu-1, x) - spherical_bessel(nu-2, x)
    end
end

function spherical_neumann(nu, x)
    if nu < 0
        error("nu must be greater than or equal to 0.")
    elseif nu == 0
        return - cos(x)/x
    elseif nu == 1
        return - cos(x)/(x*x) - sin(x)/x
    else
        return (2nu - 1)/x * spherical_neumann(nu-1, x) - spherical_neumann(nu-2, x)
    end
end

function legendre(l, m, x)
    if m < 0
        return (-1)^m * factorial(l+m)/factorial(l+m) * legendre(l, -m, x)
    end
    
    P₀ = zero(x) 
    if l < m
        return P₀
    end
    
    P₁ = sqrt((1 - x^2)^m)
    for i in m+1:2m
        P₁ *= i/2
    end
    if l == m
        return P₁
    end
    
    P₂ = zero(x)
    for i in m+1:l
        P₂ = (2i - 1)/(i - m)*x*P₁ - (i + m - 1)/(i - m)*P₀
        P₀ = P₁
        P₁ = P₂
    end
    return P₂
end

function deriv_legendre(l, m, x)
    return legendre(l, m+1, x)/sqrt(1 - x^2) - m*x/(1-x^2)*legendre(l, m, x)
end

function spherical_harmonics(l, m, θ, ϕ) 
    return sqrt((2l+1)/4π* factorial(l-m)/factorial(l+m)) *
        legendre(l, m, cos(θ)) * exp(im*m*ϕ)
end


function laguerre(n, k, x)
    L₀ = one(x)
    if n == 0
        return L₀
    end
    
    L₁ = k + 1 - x
    if n == 1
        return L₁
    end
    
    L₂ = zero(x)
    for i in 2:n
        L₂ = (k + 2i - 1 - x)*L₁ - (i - 1 + k)*L₀
        L₂ /= i
        
        L₀ = L₁
        L₁ = L₂
    end
    
    return L₂
end

function deriv_laguerre(n, k, x)
    if n == 0
        return zero(x)
    end
    
    (n*laguerre(n, k, x) - (n+k)*laguerre(n-1, k, x))/x
end


function hermite(n, x)
    h₀ = one(x)
    if n == 0
        return h₀
    end
    
    h₁ = 2x
    if n == 1
        return h₁
    end
    
    h₂ = zero(x)
    for i in 2:n
        h₂ = 2x*h₁ - 2(i-1)*h₀ # i-th hermite polynomial
        h₀ = h₁
        h₁ = h₂
    end
    
    return h₂
end

function deriv_hermite(n, x)
    if n == 0
        return zero(x)
    end
    
    return 2n*hermite(n-1, x)
end




function calc_laguerre_coefficients(n; iter_max=30, rtol=1e-10)
    laposition = zeros(Float64, n)
    laweight = zeros(Float64, n)
    
    x₀ = zeros(Float64, n)
    for k in 1:n
        if (k < 4)
            x₀[k] = (π*(k - 1/4))^2/4n
        else
            x₀[k] = 3(x₀[k-1] - x₀[k-2]) + x₀[k-3]
        end
        
        x = x₀[k]
        converge = false
        for iter in 1:iter_max
            p = laguerre(n, 0, x)
            dp = deriv_laguerre(n, 0, x)
            
            x_new = x - p/dp
            if (abs(x_new - x)/x < rtol) 
                converge= true
                break
            end
            x = x_new
        end
        
        if !converge
            error("No convergence at k = $k")
        end
        
        p = laguerre(n-1, 0, x)
        w = x/(n*p)^2
        
        x₀[k] = x
        
        laposition[k] = x
        laweight[k] = w
    end
    
    return laposition, laweight
end


function calc_legendre_coefficients(n; iter_max=30, rtol=1e-10, xtol=1e-20)
    leposition = Float64[]
    leweight = Float64[]
    
    for k in 1:div(n+1, 2)
        x = sin((n + 1 - 2k)*π/(2n + 1))
        converge = false
        for iter in 1:iter_max
            p = legendre(n, 0, x)
            dp = deriv_legendre(n, 0, x)
            
            x_new = x - p/dp
            if (abs(x_new - x)/x < rtol || abs(x) < xtol)
                converge = true
                break
            end
            x = x_new
        end
        
        if !converge
            error("No convergence at k = $k, x = $x")
        end
        
        p = legendre(n-1, 0, x)
        w = 2(1-x^2)/(n*p)^2
        
        push!(leposition, x)
        push!(leweight, w)
    end
        
    return reverse(leposition), reverse(leweight)
end


function calc_hermite_coefficients(n; iter_max=30, rtol=1e-10, xtol=1e-20)
    heposition = Float64[]
    heweight = Float64[]
    
    fac = sqrt(π)/2
    for i in 1:n
        fac *= 2i
    end
    
    x₀ = zeros(Float64, div(n+1, 2))
    for k in 1:div(n+1, 2)
        if (k < 4)
            if iseven(n)
                x₀[k] = (2k-1)*π/(2*sqrt(2n+1))
            else
                x₀[k] = (k-1)*π/sqrt(2n+1)
            end
        else
            x₀[k] = 3(x₀[k-1] - x₀[k-2]) + x₀[k-3]
        end
        
        x = x₀[k]
        converge = false
        for iter in 1:iter_max
            p = hermite(n, x)
            dp = deriv_hermite(n, x)
            
            x_new = x - p/dp
            if (abs((x_new - x)/x) < rtol || abs(x_new - x) < xtol)
                converge = true
                break
            end
            x = x_new
        end
        
        if !converge
            error("No convergence at k = $k")
        end
        
        p = hermite(n-1, x)
        w = fac/(n*p)^2
        
        x₀[k] = x
        
        push!(heposition, x)
        push!(heweight, w)
    end
    
    return heposition, heweight
end



"""
    q_to_iq(q)

map isospin q = +1, -1 to iq = 1, 2, respectively.
"""
function q_to_iq(q)
    div(3-q, 2)
end
;
    
    
    

end # module
