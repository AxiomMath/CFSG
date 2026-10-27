module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcSchur
import CFSG.Quasithin.Vol2.Ch10SecI1Dual
import CFSG.RepresentationTheory.GF2.FiveSquaredOrderThree
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.Quasithin.Background.OddCoprimeFixV

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem one_lt_s15_of_cyclic_five_rank_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hL : IsCyclicOrd ↥(lBar V₀ V hV L) 5)
    (hrk : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
      (lBar V₀ V hV L)) = 4) :
    1 < s15 D.M V₀ V hV L := by
  classical
  by_contra hnot
  have hs1 : 1 ≤ s15 D.M V₀ V hV L :=
    Nat.succ_le_of_lt (s15_Eleven_pos_s D c.setting.hyp151 hV)
  have hs : s15 D.M V₀ V hV L = 1 := le_antisymm (by omega) hs1
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := hwT
  have hHcard : Nat.card ↥(lBar V₀ V hV L) = 5 := hL.2
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by rw [hHcard]; norm_num
  have hfixH : fixV (lBar V₀ V hV L) = ⊥ := by
    have h := commV_inf_fixV_eq_bot_of_odd_card (V := Vtil V₀ V hV)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) (lBar V₀ V hV L) hodd
    rw [commV_eq_commSub, hcomm, top_inf_eq] at h
    exact h
  have hQ : ∀ x : Vtil V₀ V hV, x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrkQ : rk (Vtil V₀ V hV) = 4 := by
    have h := hrk
    rw [hcomm, rk_top] at h
    exact h
  have hQcard : Nat.card (Vtil V₀ V hV) = 2 ^ 4 := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hQ), hrkQ]
  have hirr : ∀ B : Subgroup (Vtil V₀ V hV),
      (∀ l ∈ lBar V₀ V hV L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤ := by
    intro B hB
    letI : Module (ZMod 2) (Additive ↥B) :=
      AddCommGroup.zmodModule (fun x => by
        apply Additive.toMul.injective
        rw [two_nsmul, toMul_add, toMul_zero]
        exact Subtype.ext (by simpa [pow_two] using hQ (Additive.toMul x).1))
    let rB : ↥(lBar V₀ V hV L) →* MulAut ↥B :=
      CFSG.Quasithin.ASInputs.C10KH.restrictAut (lBar V₀ V hV L).subtype B
        (fun l b hb => hB l l.2 b hb)
    have hfixB : ∀ w : Additive ↥B,
        (∀ l : ↥(lBar V₀ V hV L),
          CFSG.Quasithin.ASInputs.C10KH.repOf rB l w = w) → w = 0 := by
      intro w hw
      have hmem : ((Additive.toMul w : ↥B) : Vtil V₀ V hV) ∈ fixV (lBar V₀ V hV L) := by
        rw [mem_fixV]
        intro l hl
        have h1 := hw ⟨l, hl⟩
        change Additive.ofMul (⟨l (Additive.toMul w).1,
          hB l hl (Additive.toMul w).1 (Additive.toMul w).2⟩ : ↥B) = w at h1
        exact Subtype.ext_iff.mp (congrArg Additive.toMul h1)
      rw [hfixH, Subgroup.mem_bot] at hmem
      simpa using congrArg Additive.ofMul hmem
    have hH5 : IsPGroup 5 ↥(lBar V₀ V hV L) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [hHcard]; norm_num⟩
    have h4 := CFSG.RepresentationTheory.GF2.four_dvd_finrank_of_fiveGroup_fixedPointFree
      (ρ := CFSG.Quasithin.ASInputs.C10KH.repOf rB) hH5 hfixB
    have hfin : Module.finrank (ZMod 2) (Additive ↥B) = rk ↥B := by
      apply Nat.pow_right_injective (by norm_num : 1 < 2)
      change 2 ^ Module.finrank (ZMod 2) (Additive ↥B) = 2 ^ rk ↥B
      have h1 : Nat.card (Additive ↥B) = 2 ^ Module.finrank (ZMod 2) (Additive ↥B) := by
        simpa using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥B)
      have h2 : Nat.card (Additive ↥B) = 2 ^ rk ↥B := by
        rw [Nat.card_congr (Additive.toMul : Additive ↥B ≃ ↥B)]
        exact card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one
          (fun b : ↥B => Subtype.ext (by simpa using hQ (b : Vtil V₀ V hV))))
      rw [← h1, h2]
    have hdvd : 4 ∣ rk ↥B := by
      rw [← hfin]
      exact h4
    have hrk_le : rk ↥B ≤ 4 := by
      have h := rk_mono (H := B) (K := ⊤) le_top
      rwa [rk_top, hrkQ] at h
    have hrkB : rk ↥B = 0 ∨ rk ↥B = 4 := by
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : k ≤ 1 := by
        have h : 4 * k ≤ 4 := by rw [← hk]; exact hrk_le
        omega
      interval_cases k
      · left; omega
      · right; omega
    rcases hrkB with h0 | h4rk
    · left
      exact (rk_eq_zero_iff (V := Vtil V₀ V hV) hQ).mp h0
    · right
      exact eq_of_le_of_rk_le (V := Vtil V₀ V hV) hQ le_top (by rw [rk_top, hrkQ, h4rk])
  have hle_one : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 1 := by
    intro p hp hp2
    have hN : ∀ n ∈ Mbar D.M V₀ V hV, ∀ l ∈ lBar V₀ V hV L, n * l * n⁻¹ ∈ lBar V₀ V hV L := by
      intro n hn l hl
      have hmap := lBar_conj_eq_of_s15_eq_one hs hn
      have hmem : (MulAut.conj n).toMonoidHom l ∈
          (lBar V₀ V hV L).map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hl
      rw [hmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    have h1 := s16k_pRank_le_of_normalizer (Q := Vtil V₀ V hV)
      (L' := lBar V₀ V hV L) (N := Mbar D.M V₀ V hV) hN hp
    have hcent : CFSG.Open.pRank p
        (Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) ≤ 1 := by
      have h2' := s16k_pRank_centralizer_le (Q := Vtil V₀ V hV)
        (L := lBar V₀ V hV L) hQ hirr (d := 4) hQcard hp hp2
      split_ifs at h2' <;> omega
    have hmono : CFSG.Open.pRank p
        (Mbar D.M V₀ V hV ⊓
          Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) ≤
        CFSG.Open.pRank p
          (Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) :=
      CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right
    have hAutCard : Nat.card (MulAut ↥(lBar V₀ V hV L)) = 4 := by
      haveI : IsCyclic ↥(lBar V₀ V hV L) := hL.1
      rw [IsCyclic.card_mulAut, hHcard, Nat.totient_prime (p := 5) (by norm_num)]
    have hAutRank : CFSG.Open.pRank p
        (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) = 0 := by
      refine CFSG.pRank_eq_zero_of_not_dvd_card hp ?_
      rw [hAutCard]
      intro h
      have h4 : p ∣ 2 ^ 2 := by simpa using h
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h4
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · exact hp.ne_one h1
      · exact hp2 h1
    rw [hAutRank] at h1
    omega
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have h2le := S168e3Ctx.two_le_pRank_mbar c hp
  have hle := hle_one p hpp hp2
  omega

theorem case162_3_of_cyclic_five_rank_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hL : IsCyclicOrd ↥(lBar V₀ V hV L) 5)
    (hrk : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV))
      (lBar V₀ V hV L)) = 4) :
    Case162_3 D V₀ V hV L := by
  have hs := one_lt_s15_of_cyclic_five_rank_four c hL hrk
  unfold Case162_3
  refine ⟨hL, ?_, by omega⟩
  show rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) = 4
  exact hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
