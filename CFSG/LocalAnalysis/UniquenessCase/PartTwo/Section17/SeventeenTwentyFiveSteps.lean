module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.WeakClosure81.InFMulEquiv
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.Quasithin.SteinbergBKCentralCoreNormalizerReducedDualActor
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP4
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barSub_centSection_le_centralizer {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L) :
    barSub V₀ V h.isElemAbelian (centSection D.M L (pCoreOf 2 L)) ≤
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  classical
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff]
  intro ψ hψ
  rw [eq_comm]
  obtain ⟨c₀, hc, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian _ φ).1 hφ
  obtain ⟨x₀, hxL, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian _ ψ).1 hψ
  have hV := h.isElemAbelian
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hcstab : (c₀ : G) ∈ stabTil V₀ V := hMstab (centSection_le D.M L _ hc)
  have hxstab : (x₀ : G) ∈ stabTil V₀ V := hMstab (c.mem_calC.1.le hxL)
  have hcomm_mem : (c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹ ∈ stabTil V₀ V :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcstab hxstab)
      (Subgroup.inv_mem _ hcstab)) (Subgroup.inv_mem _ hxstab)
  have hcomm_act :
      actTil V₀ V hV ⟨(c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹, hcomm_mem⟩ = 1 := by
    have hmemC : (c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹ ∈ pCoreOf 2 L :=
      hc.2.2.2 x₀ hxL
    have hmem := actTil_mem_barSub V₀ V hV (X := pCoreOf 2 L) hmemC hcomm_mem
    rw [TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)] at hmem
    simpa using hmem
  change actTil V₀ V hV c₀ * actTil V₀ V hV x₀ =
    actTil V₀ V hV x₀ * actTil V₀ V hV c₀
  have h1 : (⟨(c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹, hcomm_mem⟩ : stabTil V₀ V) *
      ⟨(x₀ : G), hxstab⟩ * ⟨(c₀ : G), hcstab⟩ =
        ⟨(c₀ : G), hcstab⟩ * ⟨(x₀ : G), hxstab⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc actTil V₀ V hV ⟨(c₀ : G), hcstab⟩ * actTil V₀ V hV ⟨(x₀ : G), hxstab⟩
      = actTil V₀ V hV (⟨(c₀ : G), hcstab⟩ * ⟨(x₀ : G), hxstab⟩) :=
        (map_mul _ _ _).symm
    _ = actTil V₀ V hV ((⟨(c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹, hcomm_mem⟩ :
          stabTil V₀ V) * ⟨(x₀ : G), hxstab⟩ * ⟨(c₀ : G), hcstab⟩) := by rw [h1]
    _ = actTil V₀ V hV ⟨(c₀ : G) * (x₀ : G) * (c₀ : G)⁻¹ * (x₀ : G)⁻¹, hcomm_mem⟩ *
          actTil V₀ V hV ⟨(x₀ : G), hxstab⟩ * actTil V₀ V hV ⟨(c₀ : G), hcstab⟩ := by
        rw [map_mul, map_mul]
    _ = actTil V₀ V hV ⟨(x₀ : G), hxstab⟩ * actTil V₀ V hV ⟨(c₀ : G), hcstab⟩ := by
        rw [hcomm_act, one_mul]

@[expose] def Gap17_25_H2_hall (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  V₀ ≠ ⊥ → P17_24_1 D V₀ V L hV → IsSpor (Bar2 L) .J2 → D.sig = {5} →
    ∃ H₂ : Subgroup G, D.T ≤ H₂ ∧
      H₂ ≤ D.T ⊔ centSection D.M L (pCoreOf 2 L) ∧ D.T.relIndex H₂ = 5

@[expose] def Gap17_25_H1_shape (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  V₀ ≠ ⊥ → P17_24_1 D V₀ V L hV → IsSpor (Bar2 L) .J2 → D.sig = {5} →
    Nonempty (Bar2 (H17_25_one D V₀ V L hV) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Bar2 (H17_25_one D V₀ V L hV) ≃* Equiv.Perm (Fin 5))

theorem inFSq_two_alternating_five_perm
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 2
      (alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup (Equiv.Perm (Fin 5)) := alternatingGroup (Fin 5)
  let P : Sylow 2 ↥K := Classical.choice (Sylow.nonempty (p := 2) (G := ↥K))
  let T : Subgroup (Equiv.Perm (Fin 5)) := (P : Subgroup ↥K).map K.subtype
  have hTsyl2 : CFSG.QuasithinUnique.IsSylowTwoOf T K :=
    CFSG.Quasithin.A4.isSylowTwoOf_map K P
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 T K :=
    CFSG.Quasithin.E1.isSylowIn_two_iff.mpr hTsyl2
  have hpcore : CFSG.pCore 2 ↥K = ⊥ :=
    CFSG.Quasithin.SteinbergBK.pCore_two_alternatingGroup_five_eq_bot
  let ebar : Bar2 K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hpcore).trans QuotientGroup.quotientBot
  have hL2 : IsL2 (Bar2 K) 2 := CFSG.Quasithin.H13.A5.lieModel_of_alternating_five ebar
  have hKn : (K.subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hperf : ⁅K, K⁆ = K := by
    simpa [K] using (commutator_alternatingGroup_eq_self (α := Fin 5) (by simp))
  have hsup : K ⊔ T = K := sup_eq_left.mpr hTsyl.1
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.inFSq_of_isL2_of_normal_sup
    (H := K) (K := K) (T := T) (m := 2) le_rfl hKn hTsyl hsup hperf hL2 hKc

theorem inFSq_two_top_perm_five
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 2
      (⊤ : Subgroup (Equiv.Perm (Fin 5))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup (Equiv.Perm (Fin 5)) := alternatingGroup (Fin 5)
  let S : Sylow 2 (Equiv.Perm (Fin 5)) :=
    Classical.choice (Sylow.nonempty (p := 2) (G := Equiv.Perm (Fin 5)))
  let T : Subgroup (Equiv.Perm (Fin 5)) := S
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 T ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hTsyl2 : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_iff.mp hTsyl
  have hpcore : CFSG.pCore 2 ↥K = ⊥ :=
    CFSG.Quasithin.SteinbergBK.pCore_two_alternatingGroup_five_eq_bot
  let ebar : Bar2 K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hpcore).trans QuotientGroup.quotientBot
  have hL2 : IsL2 (Bar2 K) 2 := CFSG.Quasithin.H13.A5.lieModel_of_alternating_five ebar
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKn : (K.subgroupOf ⊤).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : K ≤ ⊤)).mpr ?_
    simpa using (Subgroup.normalizer_eq_top_iff.mpr hKnormal).ge
  have hperf : ⁅K, K⁆ = K := by
    simpa [K] using (commutator_alternatingGroup_eq_self (α := Fin 5) (by simp))
  have hsup : K ⊔ T = ⊤ := by
    change alternatingGroup (Fin 5) ⊔ T = ⊤
    rw [← CFSG.Quasithin.H13.twoResidual_perm5_cv, sup_comm]
    exact CFSG.Quasithin.sup_twoResidual_eq hTsyl2
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.inFSq_of_isL2_of_normal_sup
    (H := ⊤) (K := K) (T := T) (m := 2) le_top hKn hTsyl hsup hperf hL2 hKc

theorem inFSq_two_of_bar2_alt_five
    {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q)
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank)
    (h : Nonempty (Bar2 H ≃* alternatingGroup (Fin 5))) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H := by
  obtain ⟨e⟩ := h
  have hA5 := inFSq_two_alternating_five_perm (hKc := hKc)
  let ebar : Bar2 (alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) ≃*
      alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.Quasithin.SteinbergBK.pCore_two_alternatingGroup_five_eq_bot).trans
      QuotientGroup.quotientBot
  exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv
    (e.trans ebar.symm) 2).mpr hA5

theorem inFSq_two_of_bar2_sym_five
    {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q)
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank)
    (h : Nonempty (Bar2 H ≃* Equiv.Perm (Fin 5))) :
    CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H := by
  obtain ⟨e⟩ := h
  have hS5 := inFSq_two_top_perm_five (hKc := hKc)
  have hpcore : CFSG.pCore 2 ↥(⊤ : Subgroup (Equiv.Perm (Fin 5))) = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃* Equiv.Perm (Fin 5))
    rw [CFSG.Monster.B.TwoA.pCore_perm_five] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv).injective).mp hmap
  let ebar : Bar2 (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃* Equiv.Perm (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hpcore).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv
    (e.trans ebar.symm) 2).mpr hS5

theorem gap17_25_H2_of {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : Ctx17_17 D V₀ V L) (h : Hyp125 D V₀ V)
    (hgap : Gap17_25_H2_hall D V₀ V L hV) :
    Gap17_25_H2 D V₀ V L hV := by
  intro hV0 hP hJ2 hsig
  obtain ⟨H₂, hTH₂, hH₂Y, hidx⟩ := hgap hV0 hP hJ2 hsig
  have hCY : centSection D.M L (pCoreOf 2 L) ≤ D.M := centSection_le _ _ _
  have hH₂M : H₂ ≤ D.M := hH₂Y.trans (sup_le D.sylowM.le hCY)
  refine ⟨H₂, hTH₂, hH₂M, hidx, ?_⟩
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMstab
  have hCstab : centSection D.M L (pCoreOf 2 L) ≤ stabTil V₀ V := hCY.trans hMstab
  have hsup := s16c7_barSub_sup V₀ V h.isElemAbelian hTstab hCstab
  calc barSub V₀ V h.isElemAbelian H₂
      ≤ barSub V₀ V h.isElemAbelian (D.T ⊔ centSection D.M L (pCoreOf 2 L)) :=
        barSub_mono V₀ V h.isElemAbelian hH₂Y
    _ = barSub V₀ V h.isElemAbelian D.T ⊔
          barSub V₀ V h.isElemAbelian (centSection D.M L (pCoreOf 2 L)) := hsup
    _ ≤ barSub V₀ V h.isElemAbelian D.T ⊔
          Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
            Set (MulAut (Vtil V₀ V h.isElemAbelian))) :=
        sup_le_sup_left (barSub_centSection_le_centralizer h c) _

theorem gap17_25_max_of
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hgap : Gap17_25_H1_shape D V₀ V L hV)
    (hK : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank) :
    Gap17_25_max D V₀ V L hV := by
  intro hV0 hP hJ2 hsig
  rcases hgap hV0 hP hJ2 hsig with h | h
  · exact inFSq_two_of_bar2_alt_five _ hK h
  · exact inFSq_two_of_bar2_sym_five _ hK h

theorem seventeen_twentyfive_of_steps
    (D : Data G) (V₀ V : Subgroup G)
    (h17_24 : R17_24At D V₀ V) (h17_20 : R17_20At D V₀ V)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (hH2 : ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L),
      Gap17_25_H2_hall D V₀ V L c.hyp125.isElemAbelian)
    (hH1 : ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L),
      Gap17_25_H1_shape D V₀ V L c.hyp125.isElemAbelian)
    (hKc : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_L2SzAutRank)
    (hJ2center : K_J2_center_five) :
    R17_25At D V₀ V :=
  seventeen_twentyfive D V₀ V h17_24 h17_20 h17_22 h17_23 hSg h869 h127 hC117 hx h61
    h1114 h162 hTor h1482 h126 h111
    (fun L c => gap17_25_H2_of (c := c) (h := c.hyp125) (hgap := hH2 L c))
    (fun L c => gap17_25_max_of (hgap := hH1 L c) (hK := hKc))
    hJ2center

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
