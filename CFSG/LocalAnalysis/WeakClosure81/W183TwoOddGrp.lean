module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddCF
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

theorem exists_oddClassGroup {Y : Type} [Group Y] [Finite Y] {a : Y} {Kk P : Subgroup Y}
    (ha : orderOf a = 2)
    (h132 : ∀ c d : Y, IsConj a c → IsConj a d →
      c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹)
    (hpc : CFSG.pCore 2 Y = ⊥) (hPn : P.Normal) (h2q : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ P)
    (hle : ∀ N : Subgroup Y, N.Normal → ¬ N ≤ Kk → P ≤ N) (haK : a ∉ Kk) :
    ∃ (X₁ : Subgroup Y) (haX : a ∈ X₁), X₁ ≤ Subgroup.normalClosure ({a} : Set Y) ∧
      orderOf (⟨a, haX⟩ : ↥X₁) = 2 ∧ IsOddTransp {x : ↥X₁ | IsConj (⟨a, haX⟩ : ↥X₁) x} ∧
      Subgroup.normalClosure ({(⟨a, haX⟩ : ↥X₁)} : Set ↥X₁) = ⊤ ∧ CFSG.pCore 2 ↥X₁ = ⊥ ∧
      ((∀ R : Subgroup Y, R.Normal → Group.IsSolvable ↥R → R = ⊥) → fusionOddCore ↥X₁ = ⊥) ∧
      (∀ (T : Type) [Group T], CFSG.Quasithin.E1.IsCompositionFactor Y T →
        (∃ u v : T, u * v ≠ v * u) → CFSG.Quasithin.E1.IsCompositionFactor ↥X₁ T) := by
  have hPN : P ≤ Subgroup.normalClosure ({a} : Set Y) :=
    hle _ inferInstance fun h => haK (h (Subgroup.subset_normalClosure (Set.mem_singleton a)))
  refine ⟨oddClassSub a, mem_oddClassSub a, oddClassSub_le_normalClosure a, ?_,
    isOddTransp_oddClassSub ha h132, normalClosure_oddClassSub h132,
    pCore_oddClassSub_eq_bot a hpc, fun hR => fusionOddCore_oddClassSub_eq_bot a hR,
    fun T _ hT hnab => isCompositionFactor_oddClassSub (fun y => ?_) hT hnab⟩
  · rw [orderOf_oddClassSub, ha]
  · obtain ⟨k, hk⟩ := h2q y
    exact ⟨k, hPN hk⟩

end CFSG.LocalAnalysis.WeakClosure81

end
