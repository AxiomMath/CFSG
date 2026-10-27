module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16ae_aSet_eq_empty {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)} {k : ℕ}
    (h : ∀ A : Subgroup (MulAut W), A ≤ X → A ≠ ⊥ → IsElemAbelian2 A →
      ∃ B : Subgroup (MulAut W), B ≤ A ∧ E3.mQuot A B < k ∧ fixV B ≠ fixV A) :
    E3.aSet k X = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hAX, hA1, hAel, hall⟩
  obtain ⟨B, hBA, hq, hne⟩ := h A hAX hA1 hAel
  exact hne (hall B hBA hq)

theorem s16ae_exists_index_two_ge {W : Type*} [CommGroup W] [Finite W]
    {A H : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hHA : H < A) :
    ∃ B : Subgroup (MulAut W), H ≤ B ∧ B ≤ A ∧ E3.mQuot A B = 1 := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hp : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥A := hp.isNilpotent
  have hlt : H.subgroupOf A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd htop (not_le_of_gt hHA)
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom (H.subgroupOf A)).resolve_left hlt.ne
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hp).1 hM
  refine ⟨M.map A.subtype, ?_, Subgroup.map_subtype_le M, ?_⟩
  · intro h hh
    have : (⟨h, hHA.le hh⟩ : ↥A) ∈ M := hHM (by simpa [Subgroup.mem_subgroupOf] using hh)
    exact ⟨_, this, rfl⟩
  · unfold E3.mQuot Subgroup.relIndex Subgroup.subgroupOf
    rw [Subgroup.comap_map_eq_self_of_injective A.subtype_injective, hidx]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
