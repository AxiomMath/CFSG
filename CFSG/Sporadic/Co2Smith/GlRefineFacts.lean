module

public import CFSG.Sporadic.Co2Smith.GlDataRefine
public import CFSG.Sporadic.Co2Cert.Cert

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert

structure GlOrbitFacts (arcs : List (Array ℕ)) (p₀ p₁ p₂ : List ℕ) (extra : List (ℕ × List ℕ)) :
    Prop where
  orb0 : ∀ σ ∈ co2P, (∀ p ∈ arcs, ArcComm σ p) → ((σ 80 : Fin 2300) : ℕ) ∈ p₀
  orb1 : ∀ σ ∈ co2P, (∀ p ∈ arcs, ArcComm σ p) → σ 80 = 80 → ((σ 1 : Fin 2300) : ℕ) ∈ p₁
  extra : ∀ σ ∈ co2P, (∀ p ∈ arcs, ArcComm σ p) → σ 80 = 80 → ∀ e ∈ extra,
    ∀ hx : e.1 < 2300, ((σ ⟨e.1, hx⟩ : Fin 2300) : ℕ) ∈ e.2
  orb2 : ∀ σ ∈ co2P, (∀ p ∈ arcs, ArcComm σ p) → σ 80 = 80 → σ 1 = 1 →
    ((σ 0 : Fin 2300) : ℕ) ∈ p₂
  triv : ∀ σ ∈ co2P, (∀ p ∈ arcs, ArcComm σ p) → σ 80 = 80 → σ 1 = 1 → σ 0 = 0 → σ = 1

end CFSG.Sporadic.Co2Smith
