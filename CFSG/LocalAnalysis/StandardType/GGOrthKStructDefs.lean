module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] def InducesSigned {G : Type} [Group G] {Bs : Subgroup G} (K : Subgroup G) {n : ℕ}
    (ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (σ : MulAut ↥Bs) (h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3))) : Prop :=
  ∀ (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) (c : G)
    (hb : ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c ∈ Bs),
    c ∈ Subgroup.centralizer (K : Set G) →
      ((σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs) : G) =
        ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * c

@[expose] def IsTorusCoord (n : ℕ) (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) :
    Prop :=
  ∀ j : Fin ((n + 1) / 2),
    ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
      SpecialLinearGroup (Fin (n + 1)) F2) =
      omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩

end CFSG.StandardType

end
