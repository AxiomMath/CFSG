module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gMParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3GapMVOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_rk_vtil_le_gen (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ s15 D.M V₀ V hV L * rk ↥(wTil V₀ V hV L) := by
  classical
  let K : D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun m => barSub V₀ V hV (conjSubgroup L (m : G))
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hspan : (⨆ m : D.M, wTil V₀ V hV (conjSubgroup L (m : G))) = ⊤ := by
    have h1 := iSup_wConj_eq D h1217 h hV hL
    rw [s15_Two_wConj_eq_range D.M V₀ V L hV, iSup_range] at h1
    have hle : ∀ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G) ≤ V := by
      intro m x hx
      rw [mem_conjSubgroup_iff] at hx
      exact (Subgroup.mem_normalizer_iff.1 (h.hyp125.pairFacts.le_normalizer m.2) x).2
        (preTil_le V₀ V hV _ hx)
    have h2 : (⨆ m : D.M, imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) (m : G))) = ⊤ := by
      have h := congrArg (imgTil V₀ V hV) h1
      rwa [s15_Core_imgTil_iSup V₀ V hV
          (fun m : D.M => conjSubgroup (wSub V₀ V hV L) (m : G)) hle,
        s15_Infra_imgTil_top] at h
    rw [← h2]
    refine iSup_congr fun m => ?_
    show wTil V₀ V hV (conjSubgroup L (m : G)) =
      imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) (m : G))
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2)]
    exact (imgTil_preTil V₀ V hV (wTil V₀ V hV (conjSubgroup L (m : G)))).symm
  haveI : Fintype ↥(Set.range K) := (Set.finite_range K).fintype
  have hsup : (⨆ b : ↥(Set.range K), commSub ⊤ (b : Subgroup (MulAut (Vtil V₀ V hV)))) = ⊤ := by
    rw [iSup_range' (fun b : Subgroup (MulAut (Vtil V₀ V hV)) => commSub ⊤ b) K]
    exact hspan
  have hrk : ∀ m : D.M, rk ↥(commSub ⊤ (K m)) = rk ↥(wTil V₀ V hV L) := by
    intro m
    have hwt : commSub ⊤ (K m) =
        (wTil V₀ V hV L).map ((actTil V₀ V hV ⟨(m : G), hMs m.2⟩)⁻¹).toMonoidHom :=
      s15_Infra_wTil_conjSubgroup V₀ V L hV (hMs m.2)
    rw [hwt, s15_Lin_rk_map]
  have hsum : (∑ b : ↥(Set.range K),
        rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil V₀ V hV))))) =
      s15 D.M V₀ V hV L * rk ↥(wTil V₀ V hV L) := by
    have hterm : ∀ b : ↥(Set.range K),
        rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil V₀ V hV)))) = rk ↥(wTil V₀ V hV L) := by
      intro b
      obtain ⟨m, hm⟩ := b.2
      rw [← hm]
      exact hrk m
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, Nat.card_coe_set_eq, smul_eq_mul]
    congr 1
    exact (s15_Core_s15_eq_ncard_range h).symm
  calc rk ↥(⊤ : Subgroup (Vtil V₀ V hV))
      = rk ↥(⨆ b : ↥(Set.range K), commSub ⊤ (b : Subgroup (MulAut (Vtil V₀ V hV)))) := by
        rw [hsup]
    _ ≤ ∑ b : ↥(Set.range K),
          rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil V₀ V hV)))) :=
        r1613g_rk_iSup_le _
    _ = s15 D.M V₀ V hV L * rk ↥(wTil V₀ V hV L) := hsum

theorem s16t_false_of_case153_3_gen (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case153_3 D V₀ V hV L) :
    False := by
  obtain ⟨hcard, hrk⟩ := r1613g_case153_3_summary D hc.conc h
  obtain ⟨hE, hrk8, -⟩ := r1613g_case168_eight_of_card_three D hcard hrk hc.concl168
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLp : IsPGroup 3 ↥(lBar V₀ V hV L) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcard)
  have hLE : lBar V₀ V hV L ≤ fstarBar D.M V₀ V hV :=
    (s16c13bc_lBar_le_pCoreOf D hV hc Nat.prime_three hLp hc.ne_bot).trans
      (s16t_pCoreOf_le_fstarBar D hV 3)
  have hE9 : Nat.card ↥(fstarBar D.M V₀ V hV) = 9 := by
    simpa using s16c167_card_isElemAbelianOfRank hE
  have hs := s16t_s15_le_two D hc.setting.hyp151 hV hc.ne_bot hE9
    (fun φ hφ x hx => s16t_fstarBar_conj_mem D hV hφ hx) hLE hcard
  have hb := s16t_rk_vtil_le_gen D h1217 hc.setting.hyp151 hV hc.ne_bot
  rw [hrk8] at hb
  have := Nat.mul_le_mul hs hrk
  omega

theorem s16t_one_lt_mBar_of_three (D : Data G) (h1217 : R1217 D) (h153 : R15_3Small D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) :
    1 < mBar D.M V₀ V hV := by
  by_contra hlt
  have hMne : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hbot
    apply hc.ne_bot
    exact le_bot_iff.mp
      ((barSub_mono V₀ V hV hc.setting.hyp151.le).trans (le_of_eq hbot))
  have hne : mBar D.M V₀ V hV ≠ 0 :=
    r1613g_mParam_ne_zero (s15_Infra_vtil_sq_eq_one V₀ V hV) hMne
  have hm1 : mBar D.M V₀ V hV = 1 := by omega
  rcases sixteen_one D h1217 h153 hc.setting.hyp151 hc.setting.hyp16.small hV hc.ne_bot hm1 with
    h1 | h2 | h3
  · exact s16t_false_of_case153_1_gen D h1217 hc h1
  · exact s16t_false_of_case153_2_gen D h1217 hc h2
  · exact s16t_false_of_case153_3_gen D h1217 hc h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
