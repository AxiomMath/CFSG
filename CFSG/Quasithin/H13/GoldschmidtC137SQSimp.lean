module

public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
import CFSG.Foundations.KCoreClosure
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.SectionRank

theorem card_dvd_factorial_index {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {H : Subgroup Y} (hH : H ≠ ⊤) : Nat.card Y ∣ (H.index).factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have := H.index_normalCore_dvd_factorial_index
  rwa [hcore, Subgroup.index_bot] at this

theorem isKGroupCat_of_simple {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (hY : Catalog Y)
    (hprop : ∀ (H : Subgroup Y), H ≠ ⊤ → ∀ (N : Subgroup H) [N.Normal],
      IsSimpleGroup (H ⧸ N) → (∃ a b : H ⧸ N, a * b ≠ b * a) → Catalog (H ⧸ N)) :
    IsKGroupCat Y :=
  CFSG.KCore.KGroupAllSimple.of_isSimpleGroup CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hY hprop

theorem six_le_of_dvd_factorial {k : ℕ} (h : 360 ∣ k.factorial) : 6 ≤ k := by
  by_contra hk
  have : k ≤ 5 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

theorem seven_le_of_dvd_factorial {k : ℕ} (h : 168 ∣ k.factorial) : 7 ≤ k := by
  by_contra hk
  have : k ≤ 6 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

theorem nine_le_of_dvd_factorial {k : ℕ} (h : 6048 ∣ k.factorial) : 9 ≤ k := by
  by_contra hk
  have : k ≤ 8 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

theorem sixty_le_card_section {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hs : IsSimpleGroup (H ⧸ N)) (hnab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    60 ≤ Nat.card (H ⧸ N) ∧ Nat.card (H ⧸ N) ≤ Nat.card H := by
  refine ⟨CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hs hnab, ?_⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Nat.card N := Nat.card_pos
  rw [h]
  exact Nat.le_mul_of_pos_right _ hpos

theorem isKGroupCat_of_card_168 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 168) (hY : Catalog Y) : IsKGroupCat Y := by
  refine isKGroupCat_of_simple hY fun H hH N _ hs hnab => ?_
  exfalso
  have hdvd := card_dvd_factorial_index hH
  rw [hcard] at hdvd
  have h7 := seven_le_of_dvd_factorial hdvd
  have hmul := H.card_mul_index
  rw [hcard] at hmul
  obtain ⟨h60, hle⟩ := sixty_le_card_section N hs hnab
  have hH24 : Nat.card H ≤ 24 := by
    by_contra h
    have : 25 * 7 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h7
    omega
  omega

end CFSG.Quasithin.H13.U3.GC137.SQ
