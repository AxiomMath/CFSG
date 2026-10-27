module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreToral
import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem toralHolds_card_le {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} [Finite A] (hel : IsElemAbelian p A) {k : ℕ} (hk : Nat.card A < p ^ k) :
    Nat.card A ≤ p ^ (k - 1) := by
  haveI := Fact.mk hp
  have hpg : IsPGroup p A := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hel.2 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn] at hk ⊢
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hk
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem ggLieToralPosition_holds :
    GGLieToralPosition := by
  intro τ _ L _ _ _ halg f hf Φ hΦ hfin p hp hp2 A hAΦ hel hcard
  have hA : A ≤ adjointGroup τ L := hAΦ.trans inf_le_left
  have hAfin : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAΦ)
  by_cases h : nontoralMinRank τ p = 1000
  · refine isToralSubgroup_of_nonTorsion hp hp2 ?_ ?_ (ℓ := 2) hp2.symm halg hA hAfin hel
    · rintro hτ rfl
      rcases hτ with rfl | rfl | rfl | rfl <;> simp [nontoralMinRank] at h
    · rintro rfl rfl
      simp [nontoralMinRank] at h
  · have hle : nontoralMinRank τ p ≤ 3 := by
      cases τ <;> simp only [nontoralMinRank, not_true_eq_false] at h ⊢ <;>
        split_ifs at h ⊢ <;> omega
    refine isToralSubgroup_of_card_le_sq halg hp hp2 hA hAfin hel ?_ ?_
    · exact toralHolds_card_le hp hel (hcard.trans_le (Nat.pow_le_pow_right hp.pos hle))
    · rintro rfl rfl
      simpa using toralHolds_card_le hp hel (k := 2) hcard

end CFSG.StandardType.LieCore
