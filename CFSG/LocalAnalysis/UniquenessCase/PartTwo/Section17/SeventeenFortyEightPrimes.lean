module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.PermutingTorusLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutTwoCyclicBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarOutTwoCyclic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U5Cartan
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20w

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalInvolution CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem rkLin_five_false_of_sq_dvd {Q z : ℕ}
    (h : CFSG.LocalAnalysis.RankThreeUC.S15.eM Q 5 = 1) (h25 : 25 ∣ Q + 1) :
    rkLin 5 false Q 5 z = 4 := by
  have hQ : Q + 1 ≠ 0 := by omega
  have hval : 2 ≤ padicValNat 5 (Q + 1) :=
    (padicValNat_dvd_iff_le hQ).mp (by simpa using h25)
  have hcond : ¬ (¬ 5 ∣ z ∧ padicValNat 5 (Q + 1) ≤ 1) := by
    rintro ⟨-, hle⟩
    omega
  unfold rkLin
  simp [h, hcond]

theorem Ctx17_42.u5_exceptional_of_prime {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h1 : R17_1At D V₀ V ctx.hyp125) (h49 : R17_49At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (hK3 : Inputs1719.K_BorelTorusAbelian)
    (hK8a : Inputs1719.K_U5TorusRank) (hT : LieOddRankChev)
    (hN : uc22p20rNativeGriess) (hU5 : IsU5 (BarInf L) n)
    {s : ℕ} (hs : s.Prime) (hsdvd : s ∣ 2 ^ n + 1) :
    s = 5 ∧ Nat.card (center (Bar2 L)) = 1 ∧ ¬ 25 ∣ 2 ^ n + 1 := by
  classical
  by_contra hnex
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hadm : StatedLieAdmissible .PSU 5 2 n := hU5.admissible
  have hmodel : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSU 5 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hU5
  have hsm : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSU 5 2 n :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5L5U5.statedClassicalModel_of_lieModel_psu hmodel
  have hs2 : s ≠ 2 := by
    rintro rfl
    have hn0 : n ≠ 0 := by
      have h1n : 1 ≤ n := hadm.2.1
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hb : 2 ∣ 2 ^ (k + 1) := by
      rw [pow_succ]
      exact dvd_mul_left 2 (2 ^ k)
    obtain ⟨b, hb'⟩ := hb
    obtain ⟨c, hc⟩ := hsdvd
    omega
  have hrankEq := uc22p20w_pRank_psu hT hq hsm hs hs2
  have heM : CFSG.LocalAnalysis.RankThreeUC.S15.eM (2 ^ n) s = 1 :=
    uc22p20v_eM_of_dvd hsdvd
  have h4rk : 4 ≤ rkLin 5 false (2 ^ n) s (Nat.card (Subgroup.center (Bar2 L))) := by
    by_cases hs5 : s = 5
    · subst hs5
      by_cases hZ : Nat.card (Subgroup.center (Bar2 L)) = 1
      · have h25 : 25 ∣ 2 ^ n + 1 := by
          by_contra h25
          exact hnex ⟨rfl, hZ, h25⟩
        have h4 := rkLin_five_false_of_sq_dvd
          (z := Nat.card (Subgroup.center (Bar2 L))) heM h25
        omega
      · have hzdvd : Nat.card (Subgroup.center (Bar2 L)) ∣ 5 := by
          have hcc := uc22p20v_card_center_dvd hN hq hodd hmodel
          simp only [CFSG.Blueprint.Multiplier.genericOrders, Nat.mul_one] at hcc
          exact hcc.trans (Nat.gcd_dvd_left 5 (2 ^ n + 1))
        have hz5 : Nat.card (Subgroup.center (Bar2 L)) = 5 := by
          rcases (Nat.dvd_prime Nat.prime_five).mp hzdvd with h1 | h5
          · exact absurd h1 hZ
          · exact h5
        have h4 := uc22p20v_rkLin_five_false (Q := 2 ^ n)
          (z := Nat.card (Subgroup.center (Bar2 L))) heM (by rw [hz5])
        omega
    · have h4 := uc22p20v_four_le_rkLin_false_one (m := 5) (Q := 2 ^ n) (r := s) (z :=
        Nat.card (Subgroup.center (Bar2 L))) hs heM (by norm_num) (fun _ => hs5)
      omega
  have hrank4 : 4 ≤ CFSG.Open.pRank s (⊤ : Subgroup (Bar2 L)) := by
    rw [hrankEq]
    exact h4rk
  haveI : Fact s.Prime := ⟨hs⟩
  have hO2 : ¬ s ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)).exists_card_eq
    rw [hk]
    intro hd
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow hd))
  have hquot : CFSG.Open.pRank s (⊤ : Subgroup (Bar2 L)) =
      CFSG.Open.pRank s (⊤ : Subgroup ↥L) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hO2
  have hmono : CFSG.Open.pRank s (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank s D.M := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (L : Subgroup G)]
    exact CFSG.SectionRank.pRank_mono hs.one_lt hL.1.le
  have h4M : 4 ≤ CFSG.Open.pRank s D.M := by
    rw [hquot] at hrank4
    exact hrank4.trans hmono
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hrsig : s ∈ D.sig := hSg.four_mem s hs hs2 h4M
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded s D.M :=
    UC6S846.sp_of_mem_sig hSg hns hrsig
  let S : Subgroup (Bar2 L) :=
    ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := isSylowTwoOf_sylowBar2 hL
  have hKB := hK8a (Bar2 L) n hadm hmodel hq S hS s hs hsdvd hnex
  have hC2 : 2 ≤ CFSG.Open.pRank s C :=
    hKB.trans (pRank_normalizerQuotient_bar2_le_pRank_cartan hL ctx.cartan hs hs2)
  obtain ⟨E, hEXN, hEel, hperm, hCE⟩ := ctx.exists_permuting_elemAbelian_le hK3 hs hs2
  have hE2 : 2 ≤ CFSG.Open.pRank s E := hC2.trans hCE
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hle1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hs hcyc
    omega
  have hEX : E ≤ X := hEXN.trans inf_le_left
  have hEN : E ≤ normalizer ((D.T ⊓ X : Subgroup G) : Set G) := hEXN.trans inf_le_right
  have hXM : X ≤ D.M := by
    rw [ctx.X_eq]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) ctx.mem_calC.1.le
  have hEM : E ≤ D.M := hEX.trans hXM
  have hin : F11.InP11 D E :=
    inP11_of_strongly hs hs2 hsp hEM hEel.isPGroup hEel.2 hEnc hperm
  have hXL : L = X := h49 L X p n l C Dc Gamma ctx
  have hXcalC : X ∈ calC D.M := hXL ▸ hL
  have hMX : D.M ≤ normalizer (X : Set G) := by
    rw [ctx.X_eq]
    exact uc22p22v_le_normalizer_conjClosure D.M L
  have houtX : Nobq.OutTwoCyclic (Bar2 X) :=
    hXL ▸ CFSG.LocalAnalysis.UniquenessCase.PartTwo.outTwoCyclic_bar2_of_isU5 hL hU5
  have hPStar : InPStar D V₀ E :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.inPStar_of_le_normalizer_of_outTwoCyclic
      hXcalC hMX hEX hEN houtX hin
  exact h1.1 E hPStar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
