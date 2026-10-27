module

public import CFSG.Sporadic.Schreier.Co1WeightStab
public import Certificates.Certificate2133
public import Certificates.Certificate2146
public import Certificates.Certificate2147
public import Certificates.Certificate2150
public import Certificates.Certificate3024
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import Certificates.Certificate16013
public import Certificates.Certificate16017
public import CFSG.Sporadic.Schreier.Co1SplitLocalSubgroup
public import CFSG.Sporadic.Schreier.Co1TernaryM12Cover

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

theorem natural_weight_stabilizer_perfect :
    orderOf ω = 3 ∧
    (∀ f b : Fin 6 → ZMod 3, charE f ⟨eProd b, eProd_mem b⟩ = ω ^ (∑ i, f i * b i).val) ∧
    (∀ (f : Fin 6 → ZMod 3) (x : GL24) (hx : x ∈ E), charV f x = charE f ⟨x, hx⟩) ∧
    (∀ c, c ∈ wStab ↔ c ∈ C ∧ ∀ e ∈ E, charV (γ 0) (c⁻¹ * e * c) = charV (γ 0) e) ∧
    Nat.card wStab = 7920 ∧ commutator wStab = ⊤ ∧
    ∀ (K : Type*) [Field K] (φ : wStab →* Kˣ), φ = 1 :=
  ⟨orderOf_ω, charE_eProd, fun f _ hx => charV_of_mem f hx, fun _ => Iff.rfl, card_wStab,
    commutator_wStab, fun _ _ φ => wStab_hom_eq_one φ⟩

end CFSG.Sporadic.Co1Schreier
