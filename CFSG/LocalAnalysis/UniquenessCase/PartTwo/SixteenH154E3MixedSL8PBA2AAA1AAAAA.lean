module

public import
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA1AAAAAA
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_sl28_seven_rank_lbar_sup_kbar {X : Type} [Group X] [Finite X]
    {M L E : Subgroup X} (hLM : L ≤ M) (hL : IsSLn ↥L 2 3) (hE : IsElemAbelian 7 E)
    (hE3 : 7 ^ 3 ≤ Nat.card ↥E) (hEM : E ≤ M)
    (hEN : E ≤ Subgroup.normalizer (L : Set X)) :
    3 ≤ CFSG.Open.pRank 7 (L ⊔ (M ⊓ Subgroup.centralizer (L : Set X))) := by
  have hrankE : 3 ≤ CFSG.Open.pRank 7 E := by
    have hcard := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_seven hE
    have hle : (7 : ℕ) ^ 3 ≤ 7 ^ CFSG.Open.pRank 7 E := by rw [← hcard]; exact hE3
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp hle
  have hineq := s16h_sl28_seven_pRank_le_inf_centralizer_add_one hL hEN
  have hK : 2 ≤ CFSG.Open.pRank 7 (E ⊓ Subgroup.centralizer (L : Set X)) := by omega
  have hcomm : ∀ x ∈ (E ⊓ Subgroup.centralizer (L : Set X)), ∀ y ∈ L, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y hy).symm
  have hbot : (E ⊓ Subgroup.centralizer (L : Set X)) ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).2
    have hxC : x ∈ Subgroup.centralizer (L : Set X) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
    have hzc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : X) y.2)
    have hz1 : (⟨x, hxL⟩ : ↥L) = 1 :=
      Subgroup.mem_bot.mp (s16h_sl28_center_eq_bot_of_isSLn hL ▸ hzc)
    simpa using congrArg Subtype.val hz1
  have hcop : Nat.Coprime 7
      (Nat.card ↥((E ⊓ Subgroup.centralizer (L : Set X)) ⊓ L)) := by
    rw [hbot]
    simp
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 7) Nat.prime_seven
    (A := E ⊓ Subgroup.centralizer (L : Set X)) (B := L) hcomm hcop
  have h7dvd : 7 ∣ Nat.card ↥L := by
    rw [s16h_sl28_card_of_isSLn hL]
    norm_num
  have hLge : 1 ≤ CFSG.Open.pRank 7 L := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact CFSG.one_le_pRank_of_dvd_card (G := ↥L) Nat.prime_seven h7dvd
  have hmono : CFSG.Open.pRank 7 ((E ⊓ Subgroup.centralizer (L : Set X)) ⊔ L) ≤
      CFSG.Open.pRank 7 (L ⊔ (M ⊓ Subgroup.centralizer (L : Set X))) := by
    apply CFSG.SectionRank.pRank_mono (by norm_num : 1 < 7)
    refine sup_le ?_ le_sup_left
    exact (le_inf (inf_le_left.trans hEM) inf_le_right).trans le_sup_right
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo