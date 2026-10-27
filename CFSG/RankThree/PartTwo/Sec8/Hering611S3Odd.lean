module

public import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

@[expose] def NoBig3 (G : Type*) [Group G] : Prop :=
  ∀ T E : Subgroup G, T ≠ ⊥ → IsPGroup 2 T → CFSG.Assembly.IsElemAbelian 3 E →
    E ≤ Subgroup.normalizer (T : Set G) → Nat.card E ≤ 27

theorem noBig3_of_evenRank {G : Type*} [Group G] [Finite G]
    (he : CFSG.Assembly.evenRank G = 3) : NoBig3 G :=
  fun _ _ hT hT2 hE hET => CFSG.RankThree.PartTwo.Sec5.card_le_of_le_normalizer he hT hT2 hE hET

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_two_subgroup_of_normalized (hbig : NoBig3 G) {A M Q : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : 27 < Nat.card A) (hM3 : ¬ 3 ∣ Nat.card M)
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hQM : Q ≤ M) (hQ2 : IsPGroup 2 Q) : Q = ⊥ := by
  by_contra hQ
  have h2M : 2 ∣ Nat.card M := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hQ2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hQ ((Subgroup.eq_bot_iff_card Q).mpr (by simpa using hk))
    have h2Q : 2 ∣ Nat.card Q := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact h2Q.trans (Subgroup.card_dvd_of_le hQM)
  obtain ⟨S, hAS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup
    Nat.prime_three Nat.prime_two (CFSG.Open.IsElemAbelian.isPGroup hA) hAM hM3
  have hT2 : IsPGroup 2 ((S : Subgroup M).map M.subtype) := S.isPGroup'.map M.subtype
  have hT : (S : Subgroup M).map M.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
    exact Sylow.ne_bot_of_dvd_card S h2M
  have hcard := hbig _ A hT hT2 hA hAS
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering611
