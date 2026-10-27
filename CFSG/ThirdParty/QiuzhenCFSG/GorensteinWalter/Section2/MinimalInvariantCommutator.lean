module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

namespace CFSG
end CFSG
open CFSG

/-!
# Minimal invariant subgroups and coprime commutators

This is the source-facing form of the Fact 1.1(i) step used in
Gorenstein--Walter Theorem 2.6.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `P` is minimal among `H`-invariant subgroups on which `Q` acts
nontrivially, and the action is coprime, then `[P,Q] = P`. -/
public theorem commutator_eq_self_of_minimal_invariant_coprime
    {G : Type u} [Group G] [Finite G]
    (H P Q : Subgroup G)
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card P))
    (hnontriv : ⁅P, Q⁆ ≠ ⊥)
    (hmin : ∀ R : Subgroup G, R ≤ P →
      H ≤ Subgroup.normalizer (R : Set G) → ⁅R, Q⁆ ≠ ⊥ → P ≤ R) :
    ⁅P, Q⁆ = P := by
  let C : Subgroup G := ⁅P, Q⁆
  have hCleP : C ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    have hqnorm : q ∈ Subgroup.normalizer (P : Set G) := hQP hq
    have hconj : q * p⁻¹ * q⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hqnorm p⁻¹).1 (P.inv_mem hp)
    simpa [C, commutatorElement_def, mul_assoc] using P.mul_mem hp hconj
  have hHnormC : H ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C] using le_normalizer_commutator_of_le_normalizer H P Q hHP hHQ
  have hidem : ⁅C, Q⁆ = C := by
    simpa [C] using
      BenderSuzuki.ig1114_commutator_idempotent_of_coprime P Q hcop hQP
  have hCnontriv : ⁅C, Q⁆ ≠ ⊥ := by
    rw [hidem]
    exact hnontriv
  exact le_antisymm hCleP (hmin C hCleP hHnormC hCnontriv)

end CFSG.GorensteinWalter
