module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NaturalO4PlusSU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3MinDegreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
public import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
public import CFSG.Quasithin.Background.B3ThreeBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubConjClosure
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_35CaseTwo (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n)
    (H : Subgroup (MulAut (Vtil V₀ V c.hyp125.isElemAbelian)))
    (I : Subgroup (Vtil V₀ V c.hyp125.isElemAbelian)),
    V₀ = ⊥ →
      H = ⨆ X ∈ conjSet (barSub V₀ V c.hyp125.isElemAbelian L)
        (Mbar D.M V₀ V c.hyp125.isElemAbelian), X →
      I ∈ irrSet (barSub V₀ V c.hyp125.isElemAbelian L) →
      (E3.mParam (autSub (autQuot (Mbar D.M V₀ V c.hyp125.isElemAbelian) (fixV H))
          (I.map (QuotientGroup.mk' (fixV H)))) : ℚ) *
        ((rk ↥(commV (autQuot (barSub V₀ V c.hyp125.isElemAbelian L) (fixV H))) : ℚ) /
          (rk ↥(I.map (QuotientGroup.mk' (fixV H))) : ℚ)) ≤
        mBar D.M V₀ V c.hyp125.isElemAbelian →
      NatSUn (autQuot (barSub V₀ V c.hyp125.isElemAbelian L) (fixV H)) ⊤ ⊥ 3 n ∧
        mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n

theorem isSU3_barSub {D : Data G} {V₀ V : Subgroup G} {L : Subgroup G} {n : ℕ}
    (h : Hyp125 D V₀ V) (hL : L ∈ calC D.M) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hshape : IsSU3 (Bar2 L) n) :
    IsSU3 ↥(barSub V₀ V h.isElemAbelian L) n := by
  have hLS : L ≤ stabTil V₀ V :=
    hL.1.le.trans (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V h.isElemAbelian (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.isElemAbelian hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  have hq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V h.isElemAbelian L) :=
    TwelveTwentyThree.isQuasisimple_barSub h.isElemAbelian hLS hL.2.2 h2 hL1
  obtain ⟨e⟩ := barSub_centerQuot_equiv_barInf h hL hL1
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hInf : IsU3 (BarInf L) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e1.symm hshape.2
  exact ⟨hq, CFSG.Blueprint.LieModel.of_mulEquiv e hInf⟩

@[expose] def Gap17_35_1_nTwo (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (c : Ctx17_33 D V₀ V L 2), V₀ ≠ ⊥ → D.k = 2 →
    mBar D.M V₀ V c.hyp125.isElemAbelian < 2 * 2 + 2

theorem seventeen_thirtyfive_one_at_of_fixV (D : Data G) {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D)
    (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (hNat : K_SU3NaturalModule) (hNat2 : Inputs1719.K_SU3NaturalModuleTwo)
    (hG2 : Gap17_35_1_nTwo D V₀ V)
    {L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (hfix : fixV (⨆ X ∈ conjSet (barSub V₀ V c.hyp125.isElemAbelian L)
      (Mbar D.M V₀ V c.hyp125.isElemAbelian), X) = ⊥) :
    CNatModSU3Sub (Vtil V₀ V c.hyp125.isElemAbelian)
        (CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V c.hyp125.isElemAbelian))
          (barSub V₀ V c.hyp125.isElemAbelian L))
        (barSub V₀ V c.hyp125.isElemAbelian L) n ∧
      mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := by
  let hV := c.hyp125.isElemAbelian
  let Kbar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
  have hLbar_ne : Kbar ≠ ⊥ := by
    by_cases h0 : V₀ = ⊥
    · subst h0
      exact barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC c.shape
    · exact barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
  have hcomp : Kbar ∈ compBar D.M V₀ V hV :=
    barSub_mem_compBar_of_ne_bot c.hyp125 c.mem_calC hLbar_ne
  have hSU : IsSU3 ↥Kbar n := isSU3_barSub c.hyp125 c.mem_calC hLbar_ne c.shape
  have hn2 : 2 ≤ n := UCK.u3Range Kbar n hSU
  have hO2 : ∀ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV → (P.subgroupOf (Mbar D.M V₀ V hV)).Normal →
        IsPGroup 2 P → P = ⊥ :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.hyp125 hP hN h2
  have hYne : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hbot
    exact hLbar_ne (le_bot_iff.1 (hbot ▸ hcomp.1))
  have hbasic : IsBasicModule (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 c.hyp125 hYne
  have hk : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split <;> norm_num
  have hm : E3.mParam (Mbar D.M V₀ V hV) ≤ 2 * n + 2 := by
    have h := h34.2.1 L n c
    change E3.mParam (Mbar D.M V₀ V hV) ≤ 2 * n + D.k at h
    omega
  have hWsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have hm5 : E3.mParam (Mbar D.M V₀ V hV) < 2 * 2 + 2 := by
      by_cases h0 : V₀ = ⊥
      · have h3 := h34.2.2 L 2 c h0
        change E3.mParam (Mbar D.M V₀ V hV) ≤ 2 + D.k at h3
        omega
      · by_cases hk2 : D.k = 2
        · exact hG2 L c h0 hk2
        · have h2 := h34.2.1 L 2 c
          change E3.mParam (Mbar D.M V₀ V hV) ≤ 2 * 2 + D.k at h2
          omega
    exact hNat2 (Vtil V₀ V hV) hWsq (Mbar D.M V₀ V hV) Kbar hcomp.1 hcomp hLbar_ne hSU hO2
      hbasic hfix hm5
  · exact hNat (Vtil V₀ V hV) hWsq (Mbar D.M V₀ V hV) Kbar n
      hcomp.1 hcomp hLbar_ne hSU hn3 hO2 hbasic hfix hm

theorem false_of_dMinDeg_le_mBar_S17 {D : Data G} {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hMin : K_SU3MinDegree)
    {L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (hKbar_ne : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥)
    (hle : dMinDeg ↥(barSub V₀ V c.hyp125.isElemAbelian L) ≤
      mBar D.M V₀ V c.hyp125.isElemAbelian) : False := by
  have hSU : IsSU3 ↥(barSub V₀ V c.hyp125.isElemAbelian L) n :=
    isSU3_barSub c.hyp125 c.mem_calC hKbar_ne c.shape
  have hn2 : 2 ≤ n := UCK.u3Range _ n hSU
  have hd : 6 * n ≤ dMinDeg ↥(barSub V₀ V c.hyp125.isElemAbelian L) :=
    hMin ↥(barSub V₀ V c.hyp125.isElemAbelian L) n hSU hn2
  have hm : E3.mParam (Mbar D.M V₀ V c.hyp125.isElemAbelian) ≤ 2 * n + 2 := by
    have h := h34.2.1 L n c
    have hk : D.k ≤ 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      split <;> norm_num
    change E3.mParam (Mbar D.M V₀ V c.hyp125.isElemAbelian) ≤ 2 * n + D.k at h
    omega
  change dMinDeg ↥(barSub V₀ V c.hyp125.isElemAbelian L) ≤
    E3.mParam (Mbar D.M V₀ V c.hyp125.isElemAbelian) at hle
  omega

theorem seventeen_thirtyfive_one
    (D : Data G) {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h869 : F08.R869 D)
    (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (hNat : K_SU3NaturalModule) (hNat2 : Inputs1719.K_SU3NaturalModuleTwo)
    (hH1 : K_SU3NaturalH1)
    (hGap : Gap17_35CaseTwo D V₀ V) (hG2 : Gap17_35_1_nTwo D V₀ V) :
    R17_35_1At D V₀ V := by
  have hMin : Inputs1719.K_SU3MinDegree := Inputs1719.k_SU3MinDegree_holds
  intro L n c
  let hV := c.hyp125.isElemAbelian
  let Kbar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ X ∈ conjSet Kbar (Mbar D.M V₀ V hV), X
  have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
  have hLbar_ne : Kbar ≠ ⊥ := by
    by_cases h0 : V₀ = ⊥
    · subst h0
      exact barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC c.shape
    · exact barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
  have hcomp : Kbar ∈ compBar D.M V₀ V hV :=
    barSub_mem_compBar_of_ne_bot c.hyp125 c.mem_calC hLbar_ne
  have hSU : IsSU3 ↥Kbar n := isSU3_barSub c.hyp125 c.mem_calC hLbar_ne c.shape
  have hn2 : 2 ≤ n := UCK.u3Range Kbar n hSU
  by_cases hfix : fixV H = ⊥
  · have hfix' : fixV (⨆ X ∈ conjSet (barSub V₀ V hV L)
        (Mbar D.M V₀ V hV), X) = ⊥ := hfix
    exact seventeen_thirtyfive_one_at_of_fixV D h34 hx h61 h127 h1214 h869 h117 hSyl hNat hNat2
      hG2 c hfix'
  ·
    have hKmem : Kbar ∈ conjSet Kbar (Mbar D.M V₀ V hV) := by
      refine ⟨1, (Mbar D.M V₀ V hV).one_mem, ?_⟩
      ext x
      simp [MulAut.conj_apply]
    have hKleH : Kbar ≤ H := le_iSup₂_of_le Kbar hKmem le_rfl
    have hHne : H ≠ ⊥ := fun h0 => hLbar_ne (le_bot_iff.1 (h0 ▸ hKleH))
    have hHL : barSub V₀ V hV (UC22.conjClosure D.M L) = H :=
      barSub_conjClosure_eq_iSup_conjSet c.hyp125 c.mem_calC.1.le
    have hYM0 : barSub V₀ V hV (UC22.conjClosure D.M L) ≤ Mbar D.M V₀ V hV :=
      barSub_mono V₀ V hV (TwelveTwentyThree.conjClosure_le c.mem_calC.1.le)
    have hYM : H ≤ Mbar D.M V₀ V hV := by rwa [hHL] at hYM0
    have hYn : (H.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
      rw [← hHL]
      rw [Subgroup.normal_subgroupOf_iff hYM0]
      intro y m hy hm
      exact TwelveEighteen.conj_mem_barSub hV
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L) m hm y hy
    have hV0 : V₀ = ⊥ := by
      by_contra hV0ne
      exact hfix (s15_Kbar_fixV_eq_bot_of_ne_bot c.hyp125 hV0ne hYM hYn hHne)
    rcases twelve_twentyFour D hx h61 h127 h1214 h128 c.hyp125 hcomp rfl with
      h1 | ⟨-, I, hI, hmn⟩ | ⟨Y, e, -, -, hsn, hnatY, -⟩
    · exact (false_of_dMinDeg_le_mBar_S17 h34 hMin c hLbar_ne h1).elim
    ·
      obtain ⟨hnat, hm⟩ := hGap L n c H I hV0 rfl hI hmn
      have hZstab : StableUnder Kbar (fixV H) := by
        intro x hx u hu
        rw [mem_fixV.1 hu x (hKleH hx)]
        exact hu
      have hZfix : fixV H ≤ fixV Kbar := by
        intro u hu
        exact mem_fixV.2 fun x hx => mem_fixV.1 hu x (hKleH hx)
      obtain ⟨W', hW'disj, hW'sup⟩ :=
        CFSG.Quasithin.B3.exists_complement (s15_Infra_vtil_sq_eq_one V₀ V hV) (fixV H)
      have hW'sup' : W' ⊔ fixV H = ⊤ := by rw [sup_comm]; exact hW'sup
      have hW'disj' : W' ⊓ fixV H = ⊥ := by rw [inf_comm]; exact hW'disj
      obtain ⟨W'', -, hdisj, hsup, hWeq, hnatW⟩ :=
        hH1 (Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV) Kbar n hSU hn2
          (fixV H) W' hZstab hZfix hW'sup' hW'disj' hnat
      refine ⟨?_, hm⟩
      rw [hWeq] at hnatW
      exact hnatW
    · exact (Inputs1719.false_of_isSubnormal_isNaturalO4Plus_of_isSU3 hSU hsn hnatY).elim

theorem exists_conjSet_list (D : Data G) (L : Subgroup G) :
    ∃ l : List (Subgroup G), l.Nodup ∧ (∀ K : Subgroup G, K ∈ l ↔ K ∈ UC22.conjSetOf D.M L) ∧
      (⨆ K ∈ l, K) = UC22.conjClosure D.M L := by
  classical
  let F : Finset (Subgroup G) := (Set.toFinite (UC22.conjSetOf D.M L)).toFinset
  have hF : ∀ K : Subgroup G, K ∈ F ↔ K ∈ UC22.conjSetOf D.M L := fun K => by simp [F]
  refine ⟨F.toList, F.nodup_toList, fun K => by simp [F, hF], ?_⟩
  rw [UC22.conjClosure]
  exact iSup_congr fun K => iSup_congr_Prop (by simp [F, hF]) fun _ => rfl

theorem isSU3_bar2_of_mem_conjSet {D : Data G} {L K : Subgroup G} {n : ℕ}
    (hK : K ∈ UC22.conjSetOf D.M L) (hshape : IsSU3 (Bar2 L) n) : IsSU3 (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hb : Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom) := UC6S846.bar2Equiv e
  have hqL : CFSG.IsQuasisimple (Bar2 L) :=
    Iff.mpr CFSG.Quasithin.A3.isQuasisimple_iff_open hshape.1
  have hqK : CFSG.IsQuasisimple (Bar2 (L.map (MulAut.conj g).toMonoidHom)) :=
    CFSG.IsQuasisimple.of_mulEquiv hb.symm hqL
  have hqK' : CFSG.Open.IsQuasisimple (Bar2 (L.map (MulAut.conj g).toMonoidHom)) :=
    Iff.mp CFSG.Quasithin.A3.isQuasisimple_iff_open hqK
  refine ⟨hqK', ?_⟩
  let e' : (Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      (Bar2 (L.map (MulAut.conj g).toMonoidHom) ⧸
        Subgroup.center (Bar2 (L.map (MulAut.conj g).toMonoidHom))) :=
    QuotientGroup.congr _ _ hb (Subgroup.map_center_eq hb)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e' hshape.2

theorem center_bar2_of_mem_conjSet {D : Data G} {L K : Subgroup G} (hZ : UCK.U3Center)
    (hK : K ∈ UC22.conjSetOf D.M L) (hshape : IsSU3 (Bar2 L) 2) (hC : K_U34ThreeCentralizer) :
    Subgroup.center (Bar2 K) = ⊥ := by
  obtain ⟨g, -, rfl⟩ := hK
  have h1 : Nat.card (Subgroup.center (Bar2 (L.map (MulAut.conj g).toMonoidHom))) = 1 := by
    rw [UC6S846.card_center_bar2_map (MulAut.conj g) L,
      center_eq_bot_of_isSU3_two hZ hC hshape, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem three_dvd_card_bar2_of_mem_conjSet {D : Data G} {L K : Subgroup G}
    (hK : K ∈ UC22.conjSetOf D.M L) (hshape : IsSU3 (Bar2 L) 2) :
    3 ∣ Nat.card (Bar2 K) :=
  three_dvd_card_of_isSU3_two (isSU3_bar2_of_mem_conjSet hK hshape)

theorem isStronglyPEmbedded_three_of_four_conj (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : IsSU3 (Bar2 L) 2) {l : List (Subgroup G)} (hnd : l.Nodup) (hlen : 4 ≤ l.length)
    (hmem : ∀ K ∈ l, K ∈ UC22.conjSetOf D.M L) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hnd4 : (l.take 4).Nodup := List.Nodup.sublist (List.take_sublist 4 l) hnd
  have hlen4 : (l.take 4).length = 4 := by rw [List.length_take]; omega
  have hmem4 : ∀ K ∈ l.take 4,
      K ∈ calC D.M ∧ 3 ∣ Nat.card (Bar2 K) ∧ Subgroup.center (Bar2 K) = ⊥ := by
    intro K hK
    have hK' : K ∈ l := List.mem_of_mem_take hK
    have hKL : K ∈ UC22.conjSetOf D.M L := hmem K hK'
    exact ⟨uc22p2214_calC_of_mem_conjSetOf hL hKL, three_dvd_card_bar2_of_mem_conjSet hKL hshape,
      center_bar2_of_mem_conjSet hZ hKL hshape hC⟩
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by
    have h := UC22.P2251c.length_le_pRank hnd4 hmem4
    rwa [hlen4] at h
  exact UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL)
    (hSg.four_mem 3 (by norm_num) (by norm_num) h4)


theorem inf_le_pCoreOf_of_center_bar2 {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : K ≠ L) (hZ : Subgroup.center (Bar2 L) = ⊥) :
    L ⊓ K ≤ pCoreOf 2 L := by
  classical
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxK : x ∈ K := hx.2
  have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 L := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.calC_commutator_le_of_ne hL hK
      (Ne.symm hne) hx).1
  have hcoe : ∀ y : ↥L, ((y : G) ∈ pCoreOf 2 L) ↔ y ∈ CFSG.pCore 2 ↥L := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
      have hzy' : z = y := Subtype.ext hzy
      rwa [hzy'] at hz
    · intro hy
      exact Subgroup.mem_map_of_mem (L.subtype) hy
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : π.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hcen : π ⟨x, hxL⟩ ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨⟨l, hlL⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    have hmem' : ⁅(⟨l, hlL⟩ : ↥L)⁻¹, (⟨x, hxL⟩ : ↥L)⁆ ∈ π.ker := by
      rw [hker, ← hcoe]
      exact hcomm (Subgroup.commutator_mem_commutator (L.inv_mem hlL) hxK)
    have hu : ((⟨l, hlL⟩ : ↥L) * (⟨x, hxL⟩ : ↥L))⁻¹ * ((⟨x, hxL⟩ : ↥L) * (⟨l, hlL⟩ : ↥L)) =
        (⟨x, hxL⟩ : ↥L)⁻¹ * ⁅(⟨l, hlL⟩ : ↥L)⁻¹, (⟨x, hxL⟩ : ↥L)⁆ * (⟨x, hxL⟩ : ↥L) := by
      group
    have hq : π (⟨l, hlL⟩ : ↥L) * π (⟨x, hxL⟩ : ↥L) =
        π (⟨x, hxL⟩ : ↥L) * π (⟨l, hlL⟩ : ↥L) := by
      rw [← map_mul, ← map_mul]
      apply QuotientGroup.eq.mpr
      rw [hu, ← hker]
      simpa using (inferInstance : π.ker.Normal).conj_mem _ hmem' (⟨x, hxL⟩ : ↥L)⁻¹
    exact hq
  have hx1 : π ⟨x, hxL⟩ = 1 := by
    have hmem := hcen
    rw [hZ] at hmem
    simpa using hmem
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hker, MonoidHom.mem_ker]
    exact hx1
  exact (hcoe ⟨x, hxL⟩).2 hx'

theorem factorization_three_card_of_isSU3_bar2 {L : Subgroup G}
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) (h : IsSU3 (Bar2 L) 2) :
    (Nat.card L).factorization 3 = 1 := by
  obtain ⟨k, hk⟩ := card_eq_pow_mul_of_isSU3_bar2 hZ hC h
  have h3pow : (2 ^ k).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd => by
      exact absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num))
  have h62400 : (62400 : ℕ).factorization 3 = 1 := by decide +kernel
  rw [hk, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply, h3pow,
    zero_add, h62400]

theorem card_sylow_three_of_isSU3_bar2 {L P : Subgroup G}
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) (h : IsSU3 (Bar2 L) 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) : Nat.card P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hP.card_eq, factorization_three_card_of_isSU3_bar2 hZ hC h, pow_one]

theorem not_nine_dvd_card_of_isSU3_bar2 {L : Subgroup G}
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) (h : IsSU3 (Bar2 L) 2) :
    ¬ 9 ∣ Nat.card L := by
  have hfac : (Nat.card L).factorization 3 = 1 :=
    factorization_three_card_of_isSU3_bar2 hZ hC h
  rintro ⟨m, hm⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have h9fac : (3 ^ 2 : ℕ).factorization 3 = 2 := by decide +kernel
  rw [hm, show 9 * m = 3 ^ 2 * m by norm_num, Nat.factorization_mul (by norm_num) hm0,
    Finsupp.add_apply, h9fac] at hfac
  omega

theorem card_le_three_of_isPGroup_three_le {L X : Subgroup G}
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) (h : IsSU3 (Bar2 L) 2)
    (hX : IsPGroup 3 X) (hXL : X ≤ L) : Nat.card X ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hX.exists_card_eq
  have hdvd : Nat.card X ∣ Nat.card L := Subgroup.card_dvd_of_le hXL
  rw [hj] at hdvd
  have h9 := not_nine_dvd_card_of_isSU3_bar2 hZ hC h
  rw [hj]
  by_contra hcon
  have hj2 : 2 ≤ j := by
    rcases j with _ | _ | j
    · simp at hcon
    · simp at hcon
    · omega
  exact h9 ((dvd_trans (by norm_num : 9 ∣ 3 ^ 2) (pow_dvd_pow 3 hj2)).trans hdvd)

theorem le_normalizer_of_conjSet_pair {R L K : Subgroup G}
    (hR : IsPGroup 3 R) (hne : K ≠ L)
    (hpair : ∀ r ∈ R, L.map (MulAut.conj r).toMonoidHom = L ∨
      L.map (MulAut.conj r).toMonoidHom = K) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hcon
  have hLr : L.map (MulAut.conj r).toMonoidHom = K := by
    rcases hpair r hr with h | h
    · exact absurd h hcon
    · exact h
  have hKr : K.map (MulAut.conj r).toMonoidHom = L := by
    have hcomp : K.map (MulAut.conj r).toMonoidHom =
        L.map (MulAut.conj (r * r)).toMonoidHom := by
      conv_lhs => rw [← hLr]
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    rcases hpair (r * r) (R.mul_mem hr hr) with h | h
    · exact h
    · exfalso
      have h1 : K.map (MulAut.conj r).toMonoidHom = L.map (MulAut.conj r).toMonoidHom := by
        rw [hcomp, h, hLr]
      exact hne (Subgroup.map_injective (MulAut.conj r).injective h1)
  have hstep : ∀ n : ℕ, L.map (MulAut.conj (r ^ (n + 1))).toMonoidHom =
      (L.map (MulAut.conj (r ^ n)).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
    intro n
    rw [pow_succ', Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hiter : ∀ n : ℕ, (Even n → L.map (MulAut.conj (r ^ n)).toMonoidHom = L) ∧
      (Odd n → L.map (MulAut.conj (r ^ n)).toMonoidHom = K) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
        rw [pow_zero]
        show L.map (MulAut.conj (1 : G)).toMonoidHom = L
        rw [show MulAut.conj (1 : G) = 1 by ext y; simp [MulAut.conj_apply]]
        exact Subgroup.map_id L
    | succ n ih =>
        refine ⟨fun hn => ?_, fun hn => ?_⟩
        · have ho : Odd n := by
            rcases hn with ⟨k, hk⟩
            exact ⟨k - 1, by omega⟩
          rw [hstep n, ih.2 ho, hKr]
        · have he : Even n := by
            rcases hn with ⟨k, hk⟩
            exact ⟨k, by omega⟩
          rw [hstep n, ih.1 he, hLr]
  obtain ⟨j, hj⟩ := hR ⟨r, hr⟩
  have hdvd : orderOf r ∣ 3 ^ j := by
    have hpow : r ^ (3 ^ j) = 1 := by simpa using hj
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hodd : Odd (orderOf r) := by
    rw [hi]
    exact (show Odd 3 by decide).pow
  have h1 : L.map (MulAut.conj (r ^ orderOf r)).toMonoidHom = K := (hiter _).2 hodd
  have h2 : L.map (MulAut.conj (r ^ orderOf r)).toMonoidHom = L := by
    rw [pow_orderOf_eq_one]
    show L.map (MulAut.conj (1 : G)).toMonoidHom = L
    rw [show MulAut.conj (1 : G) = 1 by ext y; simp [MulAut.conj_apply]]
    exact Subgroup.map_id L
  rw [h2] at h1
  exact hne h1.symm

theorem isStronglyPEmbedded_three_of_three_conj (D : Data G) (h82 : F08.R82 D)
    (hZ : UCK.U3Center) (hC : K_U34ThreeCentralizer) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : IsSU3 (Bar2 L) 2) {l : List (Subgroup G)} (hnd : l.Nodup) (hlen : l.length = 3)
    (hmem : ∀ K : Subgroup G, K ∈ l ↔ K ∈ UC22.conjSetOf D.M L)
    (hjoin : (⨆ K ∈ l, K) = UC22.conjClosure D.M L) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hlen
  have hcalc : ∀ K : Subgroup G, K ∈ [a, b, c] → K ∈ calC D.M :=
    fun K hK => uc22p2214_calC_of_mem_conjSetOf hL ((hmem K).1 hK)
  have hshape' : ∀ K : Subgroup G, K ∈ [a, b, c] → IsSU3 (Bar2 K) 2 :=
    fun K hK => isSU3_bar2_of_mem_conjSet ((hmem K).1 hK) hshape
  have hrk : ∀ K : Subgroup G, K ∈ [a, b, c] → CFSG.Open.pRank 3 K = 1 :=
    fun K hK => pRank_three_eq_one_of_isSU3_bar2 hZ hC (hshape' K hK)
  have hpair : ∀ A ∈ [a, b, c], ∀ B ∈ [a, b, c], A ≤ normalizer (B : Set G) := by
    intro A hA B hB
    by_cases hAB : A = B
    · rw [hAB]; exact Subgroup.le_normalizer
    · exact UC22.uc22p22u_calC_normalizes (X := D.M) (hcalc B hB) (hcalc A hA) (fun h => hAB h.symm)
  have hprod := UC22.uc22p22u_prod_list_eq_iSup [a, b, c] hpair
  have hset : (UC22.conjClosure D.M L : Set G) = (a : Set G) * b * c := by
    calc (UC22.conjClosure D.M L : Set G) = ((⨆ K ∈ [a, b, c], K : Subgroup G) : Set G) := by
          rw [hjoin]
      _ = ([a, b, c].map fun K : Subgroup G => (K : Set G)).prod := hprod.symm
      _ = (a : Set G) * b * c := by simp [List.prod, mul_assoc]
  have hgt : 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) := by
    obtain ⟨E, hEel, hEcard, hE⟩ := UC22.P2251c.exists_elemAbelian_of_list [a, b, c] hnd
      (fun K hK => ⟨hcalc K hK, three_dvd_card_bar2_of_mem_conjSet ((hmem K).1 hK) hshape,
        center_bar2_of_mem_conjSet hZ ((hmem K).1 hK) hshape hC⟩)
    rw [hjoin] at hE
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE hEel
      (by rw [hEcard])
    omega
  have hnorm : D.M ≤ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    (UC22.uc22p22u_conjClosure_isProd (X := D.M) le_rfl Subgroup.le_normalizer hL).2.1
  have hprodcalC : F08.IsProdOfCalC D.M (UC22.conjClosure D.M L) :=
    (UC22.uc22p22u_conjClosure_isProd (X := D.M) le_rfl Subgroup.le_normalizer hL).2.2
  have hML : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hL.1.le
  have hsub : CFSG.Open.IsSubnormal (UC22.conjClosure D.M L) D.M :=
    CFSG.Quasithin.A3.subnormal_of_normal hML
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hML).2 hnorm)
  have hle : ∀ K : Subgroup G, K ∈ [a, b, c] → K ≤ UC22.conjClosure D.M L := by
    intro K hK
    rw [← hjoin]
    exact le_iSup₂_of_le K hK le_rfl
  exact h82 (UC22.conjClosure D.M L)
    ⟨hsub, CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.perfect_of_isProdOfCalC hprodcalC, hgt,
      Or.inr ⟨a, b, c, hcalc a (by simp), hcalc b (by simp), hcalc c (by simp),
        hrk a (by simp), hrk b (by simp), hrk c (by simp),
        hle a (by simp), hle b (by simp), hle c (by simp), hset⟩⟩

theorem le_centralizer_of_isPGroup_three_card_three
    {R P : Subgroup G}
    (hR : IsPGroup 3 R) (hPR : P ≤ R) (hPN : R ≤ Subgroup.normalizer (P : Set G))
    (hPcard : Nat.card P = 3) :
    P ≤ Subgroup.centralizer (R : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPn : (P.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPR).2 hPN
  have hcardSub : Nat.card ↥(P.subgroupOf R) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv, hPcard]
  have hcyc : IsCyclic ↥(P.subgroupOf R) := isCyclic_of_prime_card hcardSub
  have hAut : Nat.card (MulAut ↥(P.subgroupOf R)) = 2 := by
    rw [IsCyclic.card_mulAut, hcardSub, Nat.totient_prime Nat.prime_three]
  have hRcard : ∃ k : ℕ, Nat.card R = 3 ^ k := hR.exists_card_eq
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  let rR : ↥R := ⟨r, hr⟩
  let φ : MulAut ↥(P.subgroupOf R) := MulAut.conjNormal rR
  have hφdvd : orderOf φ ∣ orderOf rR := orderOf_map_dvd _ rR
  have hr3 : orderOf rR ∣ Nat.card R := by simpa [rR] using Subgroup.orderOf_dvd_natCard R hr
  have hφ3 : orderOf φ ∣ 3 ^ (Classical.choose hRcard) := by
    rw [← Classical.choose_spec hRcard]
    exact hφdvd.trans hr3
  have hφ2 : orderOf φ ∣ 2 := by
    have h := Subgroup.orderOf_dvd_natCard
      (⊤ : Subgroup (MulAut ↥(P.subgroupOf R))) (Subgroup.mem_top φ)
    rwa [Subgroup.card_top, hAut] at h
  have hcop : Nat.Coprime 2 (3 ^ Classical.choose hRcard) := by
    have h23 : Nat.Coprime 2 3 := by norm_num
    simpa using h23.pow_right (Classical.choose hRcard)
  have hgcd : Nat.gcd 2 (3 ^ Classical.choose hRcard) = 1 := hcop.gcd_eq_one
  have h1 : orderOf φ = 1 := by
    have h := Nat.dvd_gcd hφ2 hφ3
    rw [hgcd] at h
    exact Nat.dvd_one.mp h
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp h1
  let pS : ↥(P.subgroupOf R) := ⟨⟨p, hPR hp⟩, by simpa [Subgroup.mem_subgroupOf] using hp⟩
  have hval : ((φ pS : ↥(P.subgroupOf R)) : ↥R) = (⟨p, hPR hp⟩ : ↥R) := by rw [hφ1]; rfl
  have hval' : r * p * r⁻¹ = p := by
    simpa [φ, rR, MulAut.conjNormal_apply, pS] using congrArg Subtype.val hval
  calc r * p = (r * p * r⁻¹) * r := by group
    _ = p * r := by rw [hval']

theorem two_le_pRank_five_centralizer_of_isSU3_pair (D : Data G) {L K P₀ P₁ R : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hshapeL : IsSU3 (Bar2 L) 2) (hshapeK : IsSU3 (Bar2 K) 2)
    (hZ : CFSG.LocalAnalysis.UniquenessCase.UCK.U3Center) (hC : K_U34ThreeCentralizer)
    (hR : IsPGroup 3 R) (hP0R : P₀ ≤ R) (hP1R : P₁ ≤ R)
    (hP0L : P₀ ≤ L) (hP1K : P₁ ≤ K)
    (hP0card : Nat.card P₀ = 3) (hP1card : Nat.card P₁ = 3) :
    2 ≤ CFSG.Open.pRank 5
      (D.M ⊓ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let E : Subgroup G := P₀ ⊔ P₁
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let Lb : Subgroup (Bar2 D.M) := barImage D.M L
  let Kb : Subgroup (Bar2 D.M) := barImage D.M K
  have hP0M : P₀ ≤ D.M := hP0L.trans hL.1.le
  have hP1M : P₁ ≤ D.M := hP1K.trans hK.1.le
  have hP0p : IsPGroup 3 P₀ := IsPGroup.of_card (n := 1) (by rw [hP0card]; norm_num)
  have hP1p : IsPGroup 3 P₁ := IsPGroup.of_card (n := 1) (by rw [hP1card]; norm_num)
  have hcommPP : ∀ a ∈ P₀, ∀ b ∈ P₁, a * b = b * a := by
    intro a ha b hb
    have hmemR : ⁅a, b⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem (hP0R ha) (hP1R hb))
        (R.inv_mem (hP0R ha))) (R.inv_mem (hP1R hb))
    have hmemO : ⁅a, b⁆ ∈ pCoreOf 2 L :=
      (calC_commutator_le_of_ne hL hK hne.symm
        (Subgroup.commutator_mem_commutator (hP0L ha) (hP1K hb))).1
    have h1 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
      Nat.prime_three (by norm_num) hR (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hmemR hmemO
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  have hP1norm : P₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
    refine (show P₁ ≤ Subgroup.centralizer (P₀ : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommPP a ha b hb
  have hE3 : IsPGroup 3 E :=
    IsPGroup.to_sup_of_normal_left' hP0p hP1p hP1norm
  have hEel : IsElemAbelian 3 E :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hP0card)
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hP1card) hcommPP
  obtain ⟨eL, _⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨eK, _⟩ := uc22p22l_barImage_equiv hK
  have hSULb : IsSU3 ↥Lb 2 := uc22p20p_isSU3_of_mulEquiv eL hshapeL
  have hSUKb : IsSU3 ↥Kb 2 := uc22p20p_isSU3_of_mulEquiv eK hshapeK
  obtain ⟨x0, hx0ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥P₀) 3 (by simp [hP0card])
  have hx0ordG : orderOf (x0 : G) = 3 := by
    rw [Subgroup.orderOf_coe, hx0ord]
  have hP0eq : P₀ = Subgroup.zpowers (x0 : G) := by
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x0.2)
      (by rw [Nat.card_zpowers, hx0ordG, hP0card])).symm
  have hx0M : (x0 : G) ∈ D.M := hP0M x0.2
  let x0M : ↥D.M := ⟨(x0 : G), hx0M⟩
  have hx0bar_mem : π x0M ∈ Lb := by
    rw [show Lb = barImage D.M L from rfl]
    exact uc22p21c_mem_barImage.2
      ⟨x0M, by simpa [x0M, Subgroup.mem_subgroupOf] using (hP0L x0.2), rfl⟩
  let x0b : ↥Lb := ⟨π x0M, hx0bar_mem⟩
  have hx0b_ne : (x0b : Bar2 D.M) ≠ 1 := by
    intro h1
    have hx0ker : x0M ∈ π.ker := h1
    rw [show π.ker = CFSG.pCore 2 ↥D.M from QuotientGroup.ker_mk' _] at hx0ker
    have hx0O : (x0 : G) ∈ pCoreOf 2 D.M :=
      Subgroup.mem_map.mpr ⟨x0M, hx0ker, rfl⟩
    have hx01 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
      Nat.prime_three (by norm_num) hP0p (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M) x0.2 hx0O
    rw [hx01] at hx0ordG
    exact absurd hx0ordG (by norm_num)
  have hx0b_ord : orderOf x0b = 3 := by
    have hdiv : orderOf (x0b : Bar2 D.M) ∣ orderOf x0M := orderOf_map_dvd π x0M
    have hx0Mord : orderOf x0M = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hx0ordG
    rw [← Subgroup.orderOf_coe x0b]
    have h3 : orderOf (x0b : Bar2 D.M) ∣ 3 := hx0Mord ▸ hdiv
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx0b_ne
    · exact h
  obtain ⟨hcyc0, hcentcard0⟩ := hC ↥Lb hSULb x0b hx0b_ord
  have h5dvd0 : 5 ∣ Nat.card ↥(Subgroup.centralizer ({x0b} : Set ↥Lb)) := by
    rw [hcentcard0]; norm_num
  obtain ⟨y0, hy0ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x0b} : Set ↥Lb))) 5 h5dvd0
  let q0 : ↥Lb := (y0 : ↥Lb)
  have hq0ord : orderOf q0 = 5 := by
    change orderOf ((y0 : ↥(Subgroup.centralizer ({x0b} : Set ↥Lb))) : ↥Lb) = 5
    rw [Subgroup.orderOf_coe, hy0ord]
  have hq0cent : q0 ∈ Subgroup.centralizer ({x0b} : Set ↥Lb) := y0.2
  obtain ⟨x1, hx1ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥P₁) 3 (by simp [hP1card])
  have hx1ordG : orderOf (x1 : G) = 3 := by
    rw [Subgroup.orderOf_coe, hx1ord]
  have hP1eq : P₁ = Subgroup.zpowers (x1 : G) := by
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x1.2)
      (by rw [Nat.card_zpowers, hx1ordG, hP1card])).symm
  have hx1M : (x1 : G) ∈ D.M := hP1M x1.2
  let x1M : ↥D.M := ⟨(x1 : G), hx1M⟩
  have hx1bar_mem : π x1M ∈ Kb := by
    rw [show Kb = barImage D.M K from rfl]
    exact uc22p21c_mem_barImage.2
      ⟨x1M, by simpa [x1M, Subgroup.mem_subgroupOf] using (hP1K x1.2), rfl⟩
  let x1b : ↥Kb := ⟨π x1M, hx1bar_mem⟩
  have hx1b_ne : (x1b : Bar2 D.M) ≠ 1 := by
    intro h1
    have hx1ker : x1M ∈ π.ker := h1
    rw [show π.ker = CFSG.pCore 2 ↥D.M from QuotientGroup.ker_mk' _] at hx1ker
    have hx1O : (x1 : G) ∈ pCoreOf 2 D.M :=
      Subgroup.mem_map.mpr ⟨x1M, hx1ker, rfl⟩
    have hx11 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
      Nat.prime_three (by norm_num) hP1p (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M) x1.2 hx1O
    rw [hx11] at hx1ordG
    exact absurd hx1ordG (by norm_num)
  have hx1b_ord : orderOf x1b = 3 := by
    have hdiv : orderOf (x1b : Bar2 D.M) ∣ orderOf x1M := orderOf_map_dvd π x1M
    have hx1Mord : orderOf x1M = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hx1ordG
    rw [← Subgroup.orderOf_coe x1b]
    have h3 : orderOf (x1b : Bar2 D.M) ∣ 3 := hx1Mord ▸ hdiv
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1b_ne
    · exact h
  obtain ⟨hcyc1, hcentcard1⟩ := hC ↥Kb hSUKb x1b hx1b_ord
  have h5dvd1 : 5 ∣ Nat.card ↥(Subgroup.centralizer ({x1b} : Set ↥Kb)) := by
    rw [hcentcard1]; norm_num
  obtain ⟨y1, hy1ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x1b} : Set ↥Kb))) 5 h5dvd1
  let q1 : ↥Kb := (y1 : ↥Kb)
  have hq1ord : orderOf q1 = 5 := by
    change orderOf ((y1 : ↥(Subgroup.centralizer ({x1b} : Set ↥Kb))) : ↥Kb) = 5
    rw [Subgroup.orderOf_coe, hy1ord]
  have hq1cent : q1 ∈ Subgroup.centralizer ({x1b} : Set ↥Kb) := y1.2
  have hcommLK : ∀ a ∈ Lb, ∀ b ∈ Kb, a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hL hK hne.symm a ha b hb
  have hLKbot : Lb ⊓ Kb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzK⟩ := Subgroup.mem_inf.mp hz
    have hzcen : (⟨z, hzL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcommLK (w : Bar2 D.M) w.2 z hzK)
    have hcenter : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_isSU3_two hZ hC hSULb
    rw [hcenter] at hzcen
    simpa using congrArg Subtype.val hzcen
  let q0B : Bar2 D.M := (q0 : Bar2 D.M)
  let q1B : Bar2 D.M := (q1 : Bar2 D.M)
  have hq0Bord : orderOf q0B = 5 := by
    change orderOf (q0 : Bar2 D.M) = 5
    rw [Subgroup.orderOf_coe, hq0ord]
  have hq1Bord : orderOf q1B = 5 := by
    change orderOf (q1 : Bar2 D.M) = 5
    rw [Subgroup.orderOf_coe, hq1ord]
  have hq0centB : q0B ∈ Subgroup.centralizer ({(x0b : Bar2 D.M)} : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhx : h = (x0b : Bar2 D.M) := by simpa using hh
    subst hhx
    have hc := (Subgroup.mem_centralizer_iff.mp hq0cent) x0b (by simp)
    exact congrArg Subtype.val hc
  have hq1centB : q1B ∈ Subgroup.centralizer ({(x1b : Bar2 D.M)} : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhx : h = (x1b : Bar2 D.M) := by simpa using hh
    subst hhx
    have hc := (Subgroup.mem_centralizer_iff.mp hq1cent) x1b (by simp)
    exact congrArg Subtype.val hc
  have hcommLK : ∀ a ∈ Lb, ∀ b ∈ Kb, a * b = b * a := by
    intro a ha b hb
    exact uc22p22l_barImage_commute hL hK hne.symm a ha b hb
  have hLKbot : Lb ⊓ Kb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzK⟩ := Subgroup.mem_inf.mp hz
    have hzcen : (⟨z, hzL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcommLK (w : Bar2 D.M) w.2 z hzK)
    have hcenter : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_isSU3_two hZ hC hSULb
    rw [hcenter] at hzcen
    simpa using congrArg Subtype.val hzcen
  have hq01comm : q0B * q1B = q1B * q0B := hcommLK q0 q0.2 q1 q1.2
  have hP0b_cent0 : barImage D.M P₀ ≤
      Subgroup.centralizer ({q0B} : Set (Bar2 D.M)) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := uc22p21c_mem_barImage.1 hz
    have hpz : (p : G) ∈ Subgroup.zpowers (x0 : G) := by
      rw [← hP0eq]
      exact hp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpz
    have hp_eq : p = x0M ^ k := by
      apply Subtype.ext
      change (p : G) = (x0 : G) ^ k
      rw [hk]
    have hz_eq : π p = (x0b : Bar2 D.M) ^ k := by
      rw [hp_eq]
      exact map_zpow π x0M k
    rw [hz_eq, Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : h = q0B := by simpa using hh
    subst hhq
    have hc : Commute (x0b : Bar2 D.M) q0B :=
      (Subgroup.mem_centralizer_iff.mp hq0centB) (x0b : Bar2 D.M) (by simp)
    exact hc.symm.zpow_right k
  have hP1b_cent0 : barImage D.M P₁ ≤
      Subgroup.centralizer ({q0B} : Set (Bar2 D.M)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : h = q0B := by simpa using hh
    subst hhq
    have hzK : z ∈ Kb := barImage_mono hP1K hz
    exact hcommLK q0 q0.2 z hzK
  have hP0b_cent1 : barImage D.M P₀ ≤
      Subgroup.centralizer ({q1B} : Set (Bar2 D.M)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : h = q1B := by simpa using hh
    subst hhq
    have hzL : z ∈ Lb := barImage_mono hP0L hz
    exact (hcommLK z hzL q1 q1.2).symm
  have hP1b_cent1 : barImage D.M P₁ ≤
      Subgroup.centralizer ({q1B} : Set (Bar2 D.M)) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := uc22p21c_mem_barImage.1 hz
    have hpz : (p : G) ∈ Subgroup.zpowers (x1 : G) := by
      rw [← hP1eq]
      exact hp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpz
    have hp_eq : p = x1M ^ k := by
      apply Subtype.ext
      change (p : G) = (x1 : G) ^ k
      rw [hk]
    have hz_eq : π p = (x1b : Bar2 D.M) ^ k := by
      rw [hp_eq]
      exact map_zpow π x1M k
    rw [hz_eq, Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : h = q1B := by simpa using hh
    subst hhq
    have hc : Commute (x1b : Bar2 D.M) q1B :=
      (Subgroup.mem_centralizer_iff.mp hq1centB) (x1b : Bar2 D.M) (by simp)
    exact hc.symm.zpow_right k
  have hEbar_eq : barImage D.M E = barImage D.M P₀ ⊔ barImage D.M P₁ := by
    unfold E barImage
    rw [Subgroup.subgroupOf_sup hP0M hP1M, Subgroup.map_sup]
  have hEbar_cent0 : barImage D.M E ≤ Subgroup.centralizer ({q0B} : Set (Bar2 D.M)) := by
    rw [hEbar_eq]
    exact sup_le hP0b_cent0 hP1b_cent0
  have hEbar_cent1 : barImage D.M E ≤ Subgroup.centralizer ({q1B} : Set (Bar2 D.M)) := by
    rw [hEbar_eq]
    exact sup_le hP0b_cent1 hP1b_cent1
  have hq0_cent_E : q0B ∈ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h := (Subgroup.mem_centralizer_iff.mp (hEbar_cent0 he)) q0B (by simp)
    exact h.symm
  have hq1_cent_E : q1B ∈ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h := (Subgroup.mem_centralizer_iff.mp (hEbar_cent1 he)) q1B (by simp)
    exact h.symm
  let Qb : Subgroup (Bar2 D.M) := Subgroup.zpowers q0B ⊔ Subgroup.zpowers q1B
  have hcommQ : ∀ a ∈ Subgroup.zpowers q0B, ∀ b ∈ Subgroup.zpowers q1B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute q0B q1B from hq01comm).zpow_left m |>.zpow_right n
  have hQbel : IsElemAbelian 5 Qb := by
    unfold Qb
    exact IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (by simpa [hq0Bord] using pow_orderOf_eq_one q0B))
      (CFSG.Open.isElemAbelian_zpowers (by simpa [hq1Bord] using pow_orderOf_eq_one q1B)) hcommQ
  have hQb5 : IsPGroup 5 Qb := hQbel.isPGroup
  have hdisjQ : Disjoint (Subgroup.zpowers q0B) (Subgroup.zpowers q1B) := by
    rw [Subgroup.disjoint_def]
    intro x hx0 hx1
    have hxL : x ∈ Lb := Subgroup.zpowers_le.mpr (show q0B ∈ Lb from q0.2) hx0
    have hxK : x ∈ Kb := Subgroup.zpowers_le.mpr (show q1B ∈ Kb from q1.2) hx1
    have hxbot : x ∈ Lb ⊓ Kb := Subgroup.mem_inf.mpr ⟨hxL, hxK⟩
    rw [hLKbot] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  have hnormQ : Subgroup.zpowers q1B ≤
      Subgroup.normalizer (Subgroup.zpowers q0B : Set (Bar2 D.M)) := by
    refine (show Subgroup.zpowers q1B ≤
        Subgroup.centralizer (Subgroup.zpowers q0B : Set (Bar2 D.M)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommQ a ha b hb
  have hQbcard : Nat.card Qb = 25 := by
    unfold Qb
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormQ hdisjQ,
      Nat.card_zpowers, Nat.card_zpowers, hq0Bord, hq1Bord]
  have hQb_le : Qb ≤ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M)) := by
    unfold Qb
    exact sup_le (Subgroup.zpowers_le.mpr hq0_cent_E) (Subgroup.zpowers_le.mpr hq1_cent_E)
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    rw [hk]
    exact fun hd => absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  have hEM : E ≤ D.M := sup_le hP0M hP1M
  have hE3sub : IsPGroup 3 (E.subgroupOf D.M) := by
    rw [← Subgroup.comap_subtype E D.M]
    exact hE3.comap_subtype
  have hmapC := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3
    (CFSG.pCore 2 ↥D.M) hN3 (E.subgroupOf D.M) hE3sub
  let CM : Subgroup ↥D.M := Subgroup.centralizer (E.subgroupOf D.M : Set ↥D.M)
  let Cbar : Subgroup (Bar2 D.M) := Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M))
  have hCMmap : CM.map π = Cbar := by
    simpa [CM, Cbar, barImage] using hmapC
  let f : ↥CM →* ↥Cbar :=
    { toFun := fun x => ⟨π x.1, by
        have hx : π x.1 ∈ CM.map π := Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
        rwa [hCMmap] at hx⟩
      map_one' := by ext; simp [CM]
      map_mul' := by intro a b; ext; simp }
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : Bar2 D.M) ∈ CM.map π := by rw [hCMmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hf_ker : IsPGroup 2 ↥f.ker := by
    have hkerp : IsPGroup 2 ↥π.ker := by
      rw [show π.ker = CFSG.pCore 2 ↥D.M from QuotientGroup.ker_mk' _]
      exact CFSG.pCore_isPGroup
    let h : ↥f.ker →* ↥D.M := CM.subtype.comp f.ker.subtype
    have hh : ∀ x, h x ∈ π.ker := by
      intro x
      have hx : f x.1 = 1 := x.2
      have hx1 : π x.1.1 = 1 := congrArg Subtype.val hx
      exact hx1
    let g : ↥f.ker →* ↥π.ker := h.codRestrict π.ker hh
    refine hkerp.of_injective g ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥π.ker => (z : ↥D.M)) hab
  have hQbC_le : Qb ≤ Cbar := hQb_le
  have hQbC5 : IsPGroup 5 (Qb.subgroupOf Cbar) := by
    rw [← Subgroup.comap_subtype Qb Cbar]
    exact hQb5.comap_subtype
  have hQbCel : IsElemAbelian 5 (Qb.subgroupOf Cbar) := by
    rw [← Subgroup.comap_subtype Qb Cbar]
    exact hQbel.comap Cbar.subtype_injective
  obtain ⟨Q, hQ5, hQmap, hQdisj⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_lift_pGroup
    f hf_surj hf_ker (by norm_num : Nat.Prime 5) (by norm_num) (Qb.subgroupOf Cbar) hQbC5
  have hQel : IsElemAbelian 5 Q :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isElemAbelian_of_disjoint_ker f Q hQdisj (by
      rw [hQmap]; exact hQbCel)
  let gGD : ↥CM →* G := D.M.subtype.comp CM.subtype
  have hgGDinj : Function.Injective gGD := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hQcard : Nat.card ↥(Q.map gGD) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective hgGDinj]
    have h1 : Nat.card ↥Q = Nat.card ↥(Q.map f) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker f Q hQdisj).symm
    rw [h1, hQmap,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbC_le).toEquiv, hQbcard]
    norm_num
  have hQleM : Q.map gGD ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact q.1.2
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hqcent : q.1 ∈ Subgroup.centralizer (E.subgroupOf D.M : Set ↥D.M) := q.2
      let eM : ↥D.M := ⟨e, hEM he⟩
      have hesub : eM ∈ E.subgroupOf D.M := by
        simpa [eM, Subgroup.mem_subgroupOf] using he
      have hcomm := (Subgroup.mem_centralizer_iff.mp hqcent) eM hesub
      simpa [eM, gGD] using congrArg Subtype.val hcomm
  exact CFSG.SectionRank.le_pRank (by norm_num) hQleM (hQel.map gGD) hQcard

theorem conjClosure_eq_sup_of_list_two (D : Data G) {L : Subgroup G} {l : List (Subgroup G)}
    (hnd : l.Nodup) (hlen : l.length = 2)
    (hmem : ∀ K : Subgroup G, K ∈ l ↔ K ∈ UC22.conjSetOf D.M L) :
    ∃ K : Subgroup G, K ≠ L ∧ (∀ X : Subgroup G, X ∈ l ↔ X = L ∨ X = K) ∧
      UC22.conjClosure D.M L = L ⊔ K := by
  classical
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have hnd' : a ≠ b := by
    have h := List.nodup_cons.mp hnd
    exact fun hab => h.1 (hab ▸ List.mem_singleton_self b)
  have hcl : UC22.conjClosure D.M L = ⨆ X ∈ [a, b], X := by
    rw [UC22.conjClosure]
    exact iSup_congr fun X => iSup_congr_Prop (hmem X).symm (fun _ => rfl)
  have hsup : (⨆ X ∈ [a, b], X) = a ⊔ b := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun X hX => ?_
      rcases (by simpa using hX) with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup₂_of_le a (by simp) le_rfl) (le_iSup₂_of_le b (by simp) le_rfl)
  have hLa : L = a ∨ L = b := by
    have : L ∈ [a, b] := (hmem L).2 ⟨1, D.M.one_mem, by
      ext x
      simp [MulAut.conj_apply]⟩
    simpa using this
  rcases hLa with hLa | hLb
  · refine ⟨b, fun h => hnd' (hLa.symm.trans h.symm), ?_, ?_⟩
    · intro X; simp [hLa]
    · rw [hcl, hsup, hLa]
  · refine ⟨a, fun h => hnd' (by rw [h, hLb]), ?_, ?_⟩
    · intro X; simp [hLb, or_comm]
    · rw [hcl, hsup, hLb, sup_comm]

theorem seventeen_thirtyfive_two_L0 (D : Data G) {V₀ V : Subgroup G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h846 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R846 D)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.UC22.F07.R76 D)
    (h614 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_14 D)
    (hZ : CFSG.LocalAnalysis.UniquenessCase.UCK.U3Center) (hC : K_U34ThreeCentralizer) :
    ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n) (l : List (Subgroup G)),
      V₀ = ⊥ → n = 2 → mBar D.M V₀ V c.hyp125.isElemAbelian = 4 → D.k = 2 →
      l.Nodup → (∀ K : Subgroup G, K ∈ l ↔ K ∈ UC22.conjSetOf D.M L) → l.length ≤ 2 →
      L = UC22.conjClosure D.M L := by
  intro L n c l hV0 hn hm4 hk hnd hmem hlen
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : ∀ H K : Subgroup G, H.IsFiniteRelIndex K :=
    fun H K => Subgroup.isFiniteRelIndex_of_finiteIndex
  have hshapeL : IsSU3 (Bar2 L) 2 := hn ▸ c.shape
  have h3L : (Nat.card L).factorization 3 = 1 :=
    factorization_three_card_of_isSU3_bar2 hZ hC hshapeL
  by_cases hlen1 : l.length = 1
  ·
    have hl : l = [L] := by
      cases l with
      | nil => simp at hlen1
      | cons a t =>
        cases t with
        | nil =>
          have hLa : L = a := by
            have : L ∈ [a] := (hmem L).2 ⟨1, D.M.one_mem, by
              ext x
              simp [MulAut.conj_apply]⟩
            simpa using this
          simp [hLa]
        | cons b t => simp at hlen1
    rw [hl] at hmem
    have hcl : UC22.conjClosure D.M L = ⨆ X ∈ [L], X := by
      rw [UC22.conjClosure]
      exact iSup_congr fun X => iSup_congr_Prop (hmem X).symm (fun _ => rfl)
    show L = UC22.conjClosure D.M L
    rw [hcl]
    simp
  ·
    have hLmem : L ∈ l := (hmem L).2 ⟨1, D.M.one_mem, by
      ext x
      simp [MulAut.conj_apply]⟩
    have hlen0 : l.length ≠ 0 := by
      intro h0
      have hnil : l = [] := List.length_eq_zero_iff.mp h0
      simp [hnil] at hLmem
    have hlen2 : l.length = 2 := by omega
    obtain ⟨K, hKne, hmemLK, hjoinLK⟩ :=
      conjClosure_eq_sup_of_list_two D hnd hlen2 hmem
    have hKl : K ∈ l := (hmemLK K).2 (Or.inr rfl)
    have hKconj : K ∈ UC22.conjSetOf D.M L := (hmem K).1 hKl
    have hKcalC : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf c.mem_calC hKconj
    have hshapeK : IsSU3 (Bar2 K) 2 := isSU3_bar2_of_mem_conjSet hKconj hshapeL
    have hKconj' : K ∈ UC22.conjSetOf D.M L := hKconj
    obtain ⟨gK, hgKM, hgKK⟩ := hKconj
    have hcardK : Nat.card K = Nat.card L := by
      rw [hgKK, Subgroup.card_map_of_injective (MulAut.conj gK).injective]
    have h3K : (Nat.card K).factorization 3 = 1 := by rw [hcardK]; exact h3L
    have hcenterL : Subgroup.center (Bar2 L) = ⊥ := center_eq_bot_of_isSU3_two hZ hC hshapeL
    have hinfO : L ⊓ K ≤ pCoreOf 2 L :=
      inf_le_pCoreOf_of_center_bar2 c.mem_calC hKcalC hKne hcenterL
    have hI2 : IsPGroup 2 ↥(L ⊓ K) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hinfO
    have h3I : (Nat.card ↥(L ⊓ K)).factorization 3 = 0 := by
      obtain ⟨m, hm⟩ := hI2.exists_card_eq
      rw [hm]
      exact Nat.factorization_eq_zero_of_not_dvd (fun hd => absurd
        (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num))
    have hcardProd := card_sup_mul_card_inf_of_le_normalizer (A := L) (C := K)
      (calC_le_normalizer_of_ne c.mem_calC hKcalC hKne.symm)
    let L0 : Subgroup G := L ⊔ K
    have hL0fac : (Nat.card L0).factorization 3 = 2 := by
      have hfac := congrArg (fun t : ℕ => t.factorization 3) hcardProd
      rw [show K ⊔ L = L0 by rw [sup_comm]] at hfac
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, h3L, h3K, h3I] at hfac
      omega
    obtain ⟨P0, hP0syl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
    have hP0card : Nat.card P0 = 3 :=
      card_sylow_three_of_isSU3_bar2 hZ hC hshapeL hP0syl
    have hP0L : P0 ≤ L := hP0syl.le
    have hP0M : P0 ≤ D.M := hP0L.trans c.mem_calC.1.le
    have hP0p : IsPGroup 3 P0 := hP0syl.isPGroup
    obtain ⟨R, hRsyl, hP0R⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (K := D.M) hP0M hP0p
    have hpairL : ∀ r ∈ R, L.map (MulAut.conj r).toMonoidHom = L ∨
        L.map (MulAut.conj r).toMonoidHom = K := by
      intro r hr
      have hrM : r ∈ D.M := hRsyl.le hr
      have hconj : L.map (MulAut.conj r).toMonoidHom ∈ UC22.conjSetOf D.M L :=
        ⟨r, hrM, rfl⟩
      exact (hmemLK _).1 ((hmem _).2 hconj)
    have hpairK : ∀ r ∈ R, K.map (MulAut.conj r).toMonoidHom = K ∨
        K.map (MulAut.conj r).toMonoidHom = L := by
      intro r hr
      have hrM : r ∈ D.M := hRsyl.le hr
      have hconj : K.map (MulAut.conj r).toMonoidHom ∈ UC22.conjSetOf D.M L :=
        UC22.uc22r899_map_conj_mem hrM hKconj'
      exact Or.symm ((hmemLK _).1 ((hmem _).2 hconj))
    have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_conjSet_pair hRsyl.isPGroup hKne hpairL
    have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_conjSet_pair hRsyl.isPGroup hKne.symm hpairK
    have hD'syl : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ L0) L0 := by
      have h := hRsyl.inf_of_le_normalizer (N := L0)
        (sup_le c.mem_calC.1.le hKcalC.1.le) ?_
      · simpa [L0] using h
      · rw [show L0 = UC22.conjClosure D.M L from hjoinLK.symm]
        exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
    have hD'card : Nat.card ↥(R ⊓ L0) = 9 := by
      rw [hD'syl.card_eq, hL0fac]
      norm_num
    have hKleL0 : K ≤ L0 := le_sup_right
    have hP1le3 : Nat.card ↥(R ⊓ K) ≤ 3 :=
      card_le_three_of_isPGroup_three_le hZ hC hshapeK (hRsyl.isPGroup.to_le inf_le_left)
        inf_le_right
    have hD'K : (R ⊓ L0) ⊓ K = R ⊓ K := by
      ext x
      constructor
      · rintro ⟨⟨hxR, hxL0⟩, hxK⟩; exact ⟨hxR, hxK⟩
      · rintro ⟨hxR, hxK⟩; exact ⟨⟨hxR, hKleL0 hxK⟩, hxK⟩
    have hP1leD' : R ⊓ K ≤ R ⊓ L0 := le_inf inf_le_left (inf_le_right.trans hKleL0)
    have hrel := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := R ⊓ L0) (K := K) (inf_le_left.trans hRK)
    have hEq : (R ⊓ K).relIndex (R ⊓ L0) = K.relIndex ((R ⊓ L0) ⊔ K) := by
      rw [hrel.2]
      rw [hD'K]
    have hrelcard : K.relIndex L0 * Nat.card ↥(K ⊓ L0) = Nat.card L0 :=
      Subgroup.relIndex_mul_card K L0
    rw [inf_eq_left.mpr hKleL0] at hrelcard
    have hKL0rel_ne : K.relIndex L0 ≠ 0 := Subgroup.relIndex_ne_zero
    have hfacKL0 : (K.relIndex L0).factorization 3 = 1 := by
      have hfac := congrArg (fun t : ℕ => t.factorization 3) hrelcard
      rw [Nat.factorization_mul hKL0rel_ne (Nat.card_pos.ne'), Finsupp.add_apply,
        hL0fac, h3K] at hfac
      omega
    have hleDK : (R ⊓ L0) ⊔ K ≤ L0 := sup_le inf_le_right hKleL0
    have hdvd : K.relIndex ((R ⊓ L0) ⊔ K) ∣ K.relIndex L0 := by
      rw [← Subgroup.relIndex_mul_relIndex K ((R ⊓ L0) ⊔ K) L0 le_sup_right hleDK]
      exact dvd_mul_right _ _
    have hfacD'le : ((R ⊓ K).relIndex (R ⊓ L0)).factorization 3 ≤ 1 := by
      rw [hEq]
      have hle := (Nat.factorization_le_iff_dvd (Subgroup.relIndex_ne_zero)
        hKL0rel_ne).2 hdvd
      have := hle 3
      omega
    have hdvd9 : (R ⊓ K).relIndex (R ⊓ L0) ∣ 9 := by
      have h := Subgroup.relIndex_mul_card (R ⊓ K) (R ⊓ L0)
      rw [inf_eq_left.mpr hP1leD', hD'card] at h
      exact ⟨Nat.card ↥(R ⊓ K), h.symm⟩
    have hrel_le3 : (R ⊓ K).relIndex (R ⊓ L0) ≤ 3 := by
      have hdvd9' : (R ⊓ K).relIndex (R ⊓ L0) ∣ 3 ^ 2 := by simpa using hdvd9
      obtain ⟨j, hjle, hjEq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9' 
      have hj1 : j ≤ 1 := by
        by_contra hcon
        have hj2 : 2 ≤ j := by omega
        have h9 : 9 ∣ K.relIndex L0 := by
          have hdiv1 : 3 ^ 2 ∣ (R ⊓ K).relIndex (R ⊓ L0) := by
            rw [hjEq]
            exact pow_dvd_pow 3 hj2
          have hdiv2 : (R ⊓ K).relIndex (R ⊓ L0) ∣ K.relIndex L0 := by
            rw [hEq]
            exact hdvd
          have h9' : 3 ^ 2 ∣ K.relIndex L0 := hdiv1.trans hdiv2
          simpa using h9'
        have hfac2 : 2 ≤ (K.relIndex L0).factorization 3 := by
          have hle := (Nat.factorization_le_iff_dvd (by norm_num : (9 : ℕ) ≠ 0)
            hKL0rel_ne).2 h9
          have h3 := hle 3
          have h9fac : (Nat.factorization 9) 3 = 2 := by decide +kernel
          rw [h9fac] at h3
          exact h3
        omega
      rw [hjEq]
      exact Nat.pow_le_pow_right (by norm_num) hj1
    have hmul := Subgroup.relIndex_mul_card (R ⊓ K) (R ⊓ L0)
    rw [inf_eq_left.mpr hP1leD', hD'card] at hmul
    have hP1ge3 : 3 ≤ Nat.card ↥(R ⊓ K) := by
      by_contra hcon
      have hlt : Nat.card ↥(R ⊓ K) ≤ 2 := by omega
      have hle := Nat.mul_le_mul hrel_le3 hlt
      omega
    have hP1card : Nat.card ↥(R ⊓ K) = 3 := le_antisymm hP1le3 hP1ge3
    have hP0eqR : P0 = R ⊓ L := by
      have hle3 : Nat.card ↥(R ⊓ L) ≤ 3 :=
        card_le_three_of_isPGroup_three_le hZ hC hshapeL
          (hRsyl.isPGroup.to_le inf_le_left) inf_le_right
      exact Subgroup.eq_of_le_of_card_ge (le_inf hP0R hP0L)
        (by rw [hP0card]; exact hle3)
    have hRnormP0 : R ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hRL).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hRnormP1 : R ≤ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hRK).trans Subgroup.inf_normalizer_le_normalizer_inf
    let P1 : Subgroup G := R ⊓ K
    have hP1R : P1 ≤ R := inf_le_left
    have hP1K : P1 ≤ K := inf_le_right
    have hP1p : IsPGroup 3 P1 := hRsyl.isPGroup.to_le inf_le_left
    have hP1card' : Nat.card P1 = 3 := hP1card
    have hP0cent : P0 ≤ Subgroup.centralizer (R : Set G) := by
      rw [hP0eqR]
      exact le_centralizer_of_isPGroup_three_card_three hRsyl.isPGroup inf_le_left
        hRnormP0 (by rw [← hP0eqR]; exact hP0card)
    have hP1cent : P1 ≤ Subgroup.centralizer (R : Set G) :=
      le_centralizer_of_isPGroup_three_card_three hRsyl.isPGroup inf_le_left hRnormP1
        hP1card'
    have hcommPP : ∀ a ∈ P0, ∀ b ∈ P1, a * b = b * a := by
      intro a ha b hb
      have hmemR : ⁅a, b⁆ ∈ R := by
        rw [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem (hP0R ha) (hP1R hb))
          (R.inv_mem (hP0R ha))) (R.inv_mem (hP1R hb))
      have hmemO : ⁅a, b⁆ ∈ pCoreOf 2 L :=
        (calC_commutator_le_of_ne c.mem_calC hKcalC hKne.symm
          (Subgroup.commutator_mem_commutator (hP0L ha) (hP1K hb))).1
      have h1 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
        Nat.prime_three (by norm_num) hRsyl.isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hmemR hmemO
      rwa [commutatorElement_eq_one_iff_mul_comm] at h1
    let E : Subgroup G := P0 ⊔ P1
    have hdisj : Disjoint P0 P1 := by
      rw [Subgroup.disjoint_def]
      intro x hx0 hx1
      have hxR : x ∈ R := hP0R hx0
      have hxL : x ∈ L := hP0L hx0
      have hxK : x ∈ K := hP1K hx1
      have hxO : x ∈ pCoreOf 2 L :=
        hinfO (Subgroup.mem_inf.mpr ⟨hxL, hxK⟩)
      exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup
        Nat.prime_three (by norm_num) hRsyl.isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hxR hxO
    have hEcard : Nat.card E = 9 := by
      have hnormal : P1 ≤ Subgroup.normalizer (P0 : Set G) := by
        refine (show P1 ≤ Subgroup.centralizer (P0 : Set G) from ?_).trans
          (Subgroup.centralizer_le_normalizer _)
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hcommPP a ha b hb
      rw [show E = P0 ⊔ P1 from rfl,
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P0 P1
          hnormal hdisj, hP0card, hP1card']
    have hEel : IsElemAbelian 3 E :=
      CFSG.Open.IsElemAbelian.sup_of_commute
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hP0card)
        (CFSG.GroupTheory.isElemAbelian_of_card_prime hP1card') hcommPP
    have hER : E ≤ R := sup_le hP0R hP1R
    have hEcent : E ≤ Subgroup.centralizer (R : Set G) :=
      sup_le hP0cent hP1cent
    have hEM : E ≤ D.M := hER.trans hRsyl.le
    have hrank2 : 2 ≤ CFSG.Open.pRank 5
        (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
      two_le_pRank_five_centralizer_of_isSU3_pair D
        c.mem_calC hKcalC hKne hshapeL hshapeK hZ hC hRsyl.isPGroup
        hP0R hP1R hP0L hP1K hP0card hP1card'
    have hsp5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
      h846 L c.mem_calC 2 hshapeL 5 (by norm_num) (by norm_num)
        (by norm_num : 5 ∣ 2 ^ 2 + 1)
    have hgamma : rankThreeGamma 1 3 E ≤ D.M := by
      refine h76 5 (by norm_num) (by norm_num) hsp5 3 (by norm_num) E hEM hEel ?_ ?_ ?_
      · rw [hEcard]; norm_num
      · omega
      · intro X hXE hXcard
        have hcent : Subgroup.centralizer (E : Set G) ≤
            Subgroup.centralizer (X : Set G) :=
          Subgroup.centralizer_le (by
            intro x hx
            exact hXE hx)
        have hle : D.M ⊓ Subgroup.centralizer (E : Set G) ≤
            D.M ⊓ Subgroup.normalizer (X : Set G) :=
          inf_le_inf_left _ (hcent.trans (Subgroup.centralizer_le_normalizer _))
        exact lt_of_lt_of_le (by omega)
          (CFSG.SectionRank.pRank_mono (by norm_num) hle)
    by_cases h3sig : 3 ∈ D.sig
    · have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
        CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg
          (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC c.mem_calC) h3sig
      have hk1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded
        D hsp3
      omega
    · have hsigsub := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC c.mem_calC)
      have hEcentR : E ≤ R ⊓ Subgroup.centralizer (R : Set G) := le_inf hER hEcent
      have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
        h614 hsigsub 3 (by norm_num) (by norm_num) h3sig R hRsyl E hEcentR hEel
          (by rw [hEcard]; norm_num) hgamma
      have hk1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded
        D hsp3
      omega

theorem seventeen_thirtyfive_two
    (D : Data G) {V₀ V : Subgroup G}
    (h35 : R17_35_1At D V₀ V) (h34 : R17_34At D V₀ V)
    (h869 : F08.R869 D) (h127 : R127 D) (hSyl : UCK.U3Syl)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D) (hZ : UCK.U3Center)
    (hC : K_U34ThreeCentralizer)
    (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) :
    R17_35_2At D V₀ V := by
  intro L n c hV0
  have hnat := h35 L n c
  have hm : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := hnat.2
  have hmle : mBar D.M V₀ V c.hyp125.isElemAbelian ≤ n + D.k := h34.2.2 L n c hV0
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split <;> norm_num
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 c.shape.2
  have hn : n = 2 := by omega
  have hm4 : mBar D.M V₀ V c.hyp125.isElemAbelian = 4 := by omega
  have hk : D.k = 2 := by omega
  have hshape : IsSU3 (Bar2 L) 2 := hn ▸ c.shape
  have hL : L = UC22.conjClosure D.M L := by
    by_contra hne
    obtain ⟨l, hnd, hmem, hjoin⟩ := exists_conjSet_list D L
    rcases Nat.lt_or_ge l.length 4 with h4 | h4
    · rcases Nat.lt_or_ge l.length 3 with h3 | h3
      · exact hne (seventeen_thirtyfive_two_L0 D hSg h846 h76 h614 hZ hC L n c l hV0 hn hm4 hk
        hnd hmem (by omega))
      · have hlen3 : l.length = 3 := by omega
        have hsp := isStronglyPEmbedded_three_of_three_conj D h82 hZ hC c.mem_calC hshape hnd
          hlen3 hmem hjoin
        have hk1 :=
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hsp
        omega
    · have hsp := isStronglyPEmbedded_three_of_four_conj D hSg hZ hC c.mem_calC hshape hnd h4
        (fun K hK => (hmem K).1 hK)
      have hk1 :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hsp
      omega
  refine ⟨?_, hk, hm4, hL⟩
  rw [← hL]
  have hLbar_ne : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ := by
    subst hV0
    exact barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC
      (hn ▸ c.shape)
  have hSU : IsSU3 ↥(barSub V₀ V c.hyp125.isElemAbelian L) 2 :=
    isSU3_barSub c.hyp125 c.mem_calC hLbar_ne (hn ▸ c.shape)
  exact uc22s13xc_isU3_of_isSU3 (by norm_num : Even 2) hSU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
