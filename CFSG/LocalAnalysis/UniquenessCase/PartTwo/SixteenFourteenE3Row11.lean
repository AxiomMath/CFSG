module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row11T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Nu
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenGap
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem s1614e3_map_fixV_of_commute {T : Type} [CommGroup T] [Finite T]
    {s e : MulAut T} (h : e * s = s * e) :
    (fixV (Subgroup.zpowers s)).map e.toMonoidHom = fixV (Subgroup.zpowers s) := by
  haveI : Finite ↥(fixV (Subgroup.zpowers s)) := inferInstance
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    have hy' : s y = y := by
      have h1 : y ∈ fixV (Subgroup.zpowers s) := hy
      exact CFSG.Quasithin.mem_fixV_zpowers_iff_apply.1 h1
    calc s ((MulEquiv.toMonoidHom e) y) = (s * e) y := rfl
      _ = (e * s) y := by rw [← h]
      _ = e (s y) := rfl
      _ = e y := by rw [hy']
  · have hc : Nat.card ((fixV (Subgroup.zpowers s)).map e.toMonoidHom) =
        Nat.card (fixV (Subgroup.zpowers s)) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom)
        (K := fixV (Subgroup.zpowers s)) e.injective
    omega

theorem s1614e3_row11_noP (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1217 : R1217 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h11 : Case168_11 D ⊥ V hV L) {U : Subgroup G}
    (hU : Min1614 D V U) {s : MulAut (Vtil ⊥ V hV)} (hsM : s ∈ Mbar D.M ⊥ V hV)
    (hs2 : orderOf s = 2) (hUs : imgTil ⊥ V hV U = fixV (Subgroup.zpowers s)) : False := by
  classical
  obtain ⟨hcyc, hrk, hs, hσ⟩ := h11
  have hT := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hA7 : Nat.card ↥(barSub ⊥ V hV L) = 7 :=
    show Nat.card ↥(barSub ⊥ V hV L) = 7 from hcyc.2
  have hodd : Odd (Nat.card ↥(barSub ⊥ V hV L)) := by
    rw [hA7]; decide
  obtain ⟨g, hg⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd hs
  have hrkT : rk (Vtil ⊥ V hV) = 6 := s1614e3_row11_rk hT hg hrk
  have h7 : 7 ∈ D.sig := by rw [hσ]; exact Set.mem_singleton 7
  have hs2' : s * s = 1 := by rw [← pow_two, ← hs2]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs2
  have hC : rkIdx (fixV (Subgroup.zpowers s)) = 3 :=
    s1614e3_row11_rkIdx hT hg hrk hA7 hsM hs2' hs1
  refine s1614e3_false_of_lemmaP D hx h61 h127 hV hc hU h7
    (s1614e3_pRank_seven_le_two hT hrkT (Mbar D.M ⊥ V hV)) ?_
  intro E hEM hE
  obtain ⟨e, heE, he1, hes⟩ :=
    s1614e3_row11_commute hT hg hrk hA7 hrkT hsM hs2' hs1 E hEM hE
  refine ⟨e, heE, he1, imgTil ⊥ V hV U, ?_, le_rfl, ?_⟩
  · rw [hUs]
    intro hbot
    have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers s))
    rw [hC, hrkT] at h1
    rw [hbot, rk_bot] at h1
    omega
  · rw [hUs]
    exact s1614e3_map_fixV_of_commute hes

theorem s1614e3_row11_close (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1217 : R1217 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h11 : Case168_11 D ⊥ V hV L) {U : Subgroup G}
    (hU : Min1614 D V U) (hUΓ : U ∉ gammaEleven D.M V) :
    E3.mQuot V U = D.k + 2 ∧ Residual1614At D V L hV U := by
  classical
  have hP : PairFacts D.M ⊥ V := hc.setting.hyp16.hyp125.pairFacts
  have hT := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hk2 := s16c167_k_le_two D
  obtain ⟨hcyc, hrk, hs, hσ⟩ := h11
  have hodd : Odd (Nat.card ↥(barSub ⊥ V hV L)) := by
    rw [show Nat.card ↥(barSub ⊥ V hV L) = 7 from hcyc.2]
    decide
  obtain ⟨g, hg⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd hs
  have hrkT : rk (Vtil ⊥ V hV) = 6 := s1614e3_row11_rk hT hg hrk
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    have h1 := s1614_rkIdx_le D hV hU
    have h2 : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
      unfold imgTil intSub
      rw [Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    rw [h2] at h1
    have h3 := rk_add_rkIdx (⊥ : Subgroup (Vtil ⊥ V hV))
    rw [rk_bot] at h3
    omega
  obtain ⟨s, hsM, hs2, hUs⟩ :=
    s1614_exists_involution D hV hP.le_normalizer hU.1 hU0 hU.2.1 hUΓ
  have hs2' : s * s = 1 := by
    rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs2
  have hC := s1614e3_row11_rkIdx hT hg hrk hcyc.2 hsM hs2' hs1
  have hle := s1614_rkIdx_le D hV hU
  have hge : rkIdx (fixV (Subgroup.zpowers s)) ≤ rkIdx (imgTil ⊥ V hV U) := rkIdx_anti hUs
  by_cases h3 : rkIdx (imgTil ⊥ V hV U) = 3
  · exfalso
    have hEq : imgTil ⊥ V hV U = fixV (Subgroup.zpowers s) := by
      refine eq_of_le_of_rk_le hT hUs ?_
      have h1 := rk_add_rkIdx (imgTil ⊥ V hV U)
      have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s))
      omega
    exact s1614e3_row11_noP D hx h61 h127 h1217 hV hc ⟨hcyc, hrk, hs, hσ⟩ hU hsM hs2 hEq
  · have h4 : rkIdx (imgTil ⊥ V hV U) = 4 := by omega
    have hk : D.k = 2 := by omega
    have hmq : E3.mQuot V U = D.k + 2 := by
      rw [s1614e3_mQuot_eq_rkIdx_imgTil hV hU.1, h4, hk]
    refine ⟨hmq, Or.inr ⟨⟨hcyc, hrk, hs, hσ⟩, ?_⟩⟩
    obtain ⟨t, htM, ht2n, htnV, -, -, hmqt, hiff, -⟩ :=
      s1614e3_lift_involution D hV hP.le_normalizer hsM hs2
    exact ⟨t, htM, ht2n, htnV, (hiff U hU.1).1 hUs, by rw [hmqt]; exact hC⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
