module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem pCoreInfCentralizer_normal' (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} {x : G} (hx : x ∈ zSub P c.L) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    PCoreInfCentralizerNormal c x := by
  set W : Subgroup G := Subgroup.centralizer ({x} : Set G) with hW
  have hWNL : W ≤ Subgroup.normalizer (c.L : Set G) := hC.trans c.le_normalizer_L
  have hWNQ : W ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    normalizer_pCoreOf_le hWNL
  have hWNW : W ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer
  have hnorm : W ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 c.L ⊓ W : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.le_normalizer_inf_of_le_normalizer hWNQ hWNW
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnorm

theorem thetaComponent_le_C_of_ne_Lz_core'
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 x) (hJne : J ≠ Lz c x) :
    J ≤ Cbar c := by
  classical
  set W : Subgroup G := Subgroup.centralizer ({x} : Set G) with hW
  have hJW : J ≤ W := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ |>.1
  have hJsn : (J.subgroupOf W).IsSubnormal :=
    CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hJ |>.2.2.1
  have hJperf : Group.IsPerfect J := CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt hJ
  have hJperf' : Group.IsPerfect ↥(J.subgroupOf W) := by
    have eJW : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
    exact Group.IsPerfect.ofSurjective (f := eJW.symm.toMonoidHom) eJW.symm.surjective
  haveI : Group.IsPerfect ↥(J.subgroupOf W) := hJperf' 
  let φ : W →* MulAut c.Lbar :=
    (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).comp (Subgroup.inclusion hC)
  let Pbar : Subgroup (MulAut c.Lbar) := (J.subgroupOf W).map φ
  have hPperf : Group.IsPerfect Pbar := by
    have hP_eq : Pbar = (φ.comp (J.subgroupOf W).subtype).range := by
      dsimp only [Pbar]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hP_eq]
    exact Group.IsPerfect.range _
  have hOutX : Group.IsSolvable
      (Outer (c.Lbar ⧸ Subgroup.center c.Lbar)) := by
    obtain ⟨eX⟩ := hON.2.2
    have hONsolv : Group.IsSolvable
        (Outer (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) :=
      CFSG.ONSchreier.at_on_schreier
    exact (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eX).2.mpr hONsolv
  haveI : Group.IsPerfect c.Lbar := Group.isPerfect_def.mpr hON.1.1
  have hOutL : Group.IsSolvable (Outer c.Lbar) :=
    (CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier c.Lbar).2.2 hOutX
  haveI : Group.IsSolvable (Outer c.Lbar) := hOutL
  haveI : Group.IsPerfect Pbar := hPperf
  have hPInn : Pbar ≤ c.lbarInn := by
    intro p hp
    obtain ⟨g, hg⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
        (A := Pbar) (G := c.Lbar) Pbar.subtype ⟨p, hp⟩
    exact ⟨g, hg.symm⟩
  have hker : (MulAut.conj : c.Lbar →* MulAut c.Lbar).ker =
      Subgroup.center c.Lbar := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h1 : g * y * g⁻¹ = y := by
        have := congrArg (fun f : MulAut c.Lbar => f y) h
        simpa [MulAut.conj_apply] using this
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    · intro h
      ext y
      rw [MulAut.conj_apply]
      rw [← h y]
      simpa
  let innEquiv : (c.Lbar ⧸ Subgroup.center c.Lbar) ≃* c.lbarInn :=
    ((QuotientGroup.quotientMulEquivOfEq hker).symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : c.Lbar →* MulAut c.Lbar))
  obtain ⟨eX⟩ := hON.2.2
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  have hXsimple : IsSimpleGroup (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    MulEquiv.isSimpleGroup eX
  have hInnSimple : IsSimpleGroup c.lbarInn := by
    haveI : IsSimpleGroup (c.Lbar ⧸ Subgroup.center c.Lbar) := hXsimple
    exact MulEquiv.isSimpleGroup innEquiv.symm
  haveI : IsSimpleGroup c.lbarInn := hInnSimple
  have hXperfect : Group.IsPerfect (c.Lbar ⧸ Subgroup.center c.Lbar) := by
    haveI : IsSimpleGroup (c.Lbar ⧸ Subgroup.center c.Lbar) := hXsimple
    refine
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.isPerfect_of_simple_not_prime_card _ ?_
    rw [Nat.card_congr eX.toEquiv]
    change ¬ Nat.Prime (Nat.card CFSG.Blueprint.NativeSporadic.ON)
    rw [CFSG.Sporadic.ON.card_ON_eq]
    intro hp
    have h2 : 2 ∣ 460815505920 := by norm_num
    rcases hp.eq_two_or_odd with h2eq | hodd
    · norm_num at h2eq
    · norm_num at hodd
  haveI : Group.IsPerfect (c.Lbar ⧸ Subgroup.center c.Lbar) := hXperfect
  have hInnPerfect : Group.IsPerfect c.lbarInn :=
    Group.IsPerfect.ofSurjective (f := innEquiv.toMonoidHom) innEquiv.surjective
  haveI : Group.IsPerfect c.lbarInn := hInnPerfect
  have hLzmem : Lz c x ∈ thetaComponentsAt 3 x :=
    Lz_mem_thetaComponentsAt c hON hP hA hZA hx hx1 hC
  have hLzW : Lz c x ≤ W := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hLzmem |>.1
  have hLzL : Lz c x ≤ c.L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hLzInn : ((Lz c x).subgroupOf W).map φ = c.lbarInn := by
    ext τ
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlG : (l : G) ∈ Lz c x := Subgroup.mem_subgroupOf.mp hl
      have hlC : (l : G) ∈ c.L := hLzL hlG
      rw [show φ l = CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
          ⟨(l : G), hC l.2⟩ from rfl,
        CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
          (hC l.2) hlC]
      exact ⟨_, rfl⟩
    · rintro ⟨q, rfl⟩
      have hq : q ∈ ((Lz c x).subgroupOf c.L).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) := by
        rw [Lz_image_eq_top c hON hP hA hZA hx hx1 hC]
        exact Subgroup.mem_top q
      obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp hq
      have hlG : (l : G) ∈ Lz c x := Subgroup.mem_subgroupOf.mp hl
      have hlW : (l : G) ∈ W := hLzW hlG
      refine ⟨⟨(l : G), hlW⟩, Subgroup.mem_subgroupOf.mpr hlG, ?_⟩
      rw [show φ ⟨(l : G), hlW⟩ =
          CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L ⟨(l : G), hC hlW⟩ from rfl,
        CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
          (hC hlW) l.2]
      change MulAut.conj (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) l) = MulAut.conj q
      rw [hlq]
  have hInn_le_range : c.lbarInn ≤ φ.range := by
    rw [← hLzInn]
    exact Subgroup.map_le_range _ _
  let Inn' : Subgroup φ.range := c.lbarInn.subgroupOf φ.range
  let P' : Subgroup φ.range := (J.subgroupOf W).map φ.rangeRestrict
  have hP'sn : P'.IsSubnormal :=
    Subgroup.IsSubnormal.map φ.rangeRestrict_surjective hJsn
  have hP'_map : P'.map φ.range.subtype = Pbar := by
    dsimp only [P', Pbar]
    rw [Subgroup.map_map]
    rfl
  have hP'_le : P' ≤ Inn' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hPInn (by rw [← hP'_map]; exact Subgroup.mem_map_of_mem φ.range.subtype hx)
  have hInn'Simple : IsSimpleGroup Inn' := by
    haveI : IsSimpleGroup c.lbarInn := hInnSimple
    exact MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hInn_le_range)
  have hcase := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hInn'Simple
    (Subgroup.IsSubnormal.subgroupOf hP'sn)
  rcases hcase with hbot | htop
  · have hP'bot : P' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxInn : x ∈ Inn' := hP'_le hx
      have hmem : (⟨x, hxInn⟩ : Inn') ∈ P'.subgroupOf Inn' := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      rw [hbot] at hmem
      simpa using Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
    have hPbar_bot : Pbar = ⊥ := by
      rw [← hP'_map, hP'bot, Subgroup.map_bot]
    intro j hj
    have hjW : j ∈ W := hJW hj
    have hmemP : φ ⟨j, hjW⟩ ∈ Pbar :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hj)
    rw [hPbar_bot] at hmemP
    have hφj : φ ⟨j, hjW⟩ = 1 := Subgroup.mem_bot.mp hmemP
    have hmemker : ⟨j, hC hjW⟩ ∈
        (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker := by
      rw [MonoidHom.mem_ker]
      change (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L) ⟨j, hC hjW⟩ = 1 at hφj ⊢
      exact hφj
    have hmemmap : j ∈
        (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map D.M.subtype :=
      Subgroup.mem_map.mpr ⟨⟨j, hC hjW⟩, hmemker, rfl⟩
    simpa [Cbar] using hmemmap
  · have hInn_le_Pbar : c.lbarInn ≤ Pbar := by
      intro τ hτ
      have hτrange : τ ∈ φ.range := hInn_le_range hτ
      let τ' : φ.range := ⟨τ, hτrange⟩
      have hτ'Inn : τ' ∈ Inn' := by
        rw [Subgroup.mem_subgroupOf]; exact hτ
      have hτ'P : τ' ∈ P' := by
        have hmem : (⟨τ', hτ'Inn⟩ : Inn') ∈ P'.subgroupOf Inn' := by
          rw [htop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hmem
      have hmem : φ.range.subtype τ' ∈ P'.map φ.range.subtype :=
        Subgroup.mem_map_of_mem φ.range.subtype hτ'P
      rwa [hP'_map] at hmem
    have hPbar_eq : Pbar = c.lbarInn := le_antisymm hPInn hInn_le_Pbar
    have hLzCommut : ⁅J, Lz c x⁆ ≤ inSubgroup (aschbacherSolvableCore 3) W := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact CFSG.RankThree.PartTwo.Sec10.commutator_mem_theta_of_ne hJ hLzmem hJne ha hb
    have hCommutImage : ⁅Pbar, c.lbarInn⁆ ≤ (aschbacherSolvableCore 3 W).map φ := by
      rw [Subgroup.commutator_le]
      intro p hp q hq
      obtain ⟨jw, hjw, rfl⟩ := Subgroup.mem_map.mp hp
      rw [← hLzInn] at hq
      obtain ⟨lw, hlw, rfl⟩ := Subgroup.mem_map.mp hq
      have hmemG := (Subgroup.commutator_le.mp hLzCommut)
        (jw : G) (Subgroup.mem_subgroupOf.mp hjw) (lw : G) (Subgroup.mem_subgroupOf.mp hlw)
      have hmemCore : ⁅jw, lw⁆ ∈ aschbacherSolvableCore 3 W := by
        have hmem' : W.subtype ⁅jw, lw⁆ ∈ inSubgroup (aschbacherSolvableCore 3) W := by
          simpa [map_commutatorElement] using hmemG
        exact (Subgroup.mem_map_iff_mem W.subtype_injective).mp hmem'
      rw [← map_commutatorElement]
      exact Subgroup.mem_map_of_mem φ hmemCore
    have hSolvCore : Group.IsSolvable (aschbacherSolvableCore 3 W) :=
      (solvable_prime_complement_core_characterization (H := W) Nat.prime_three).1
    have hSolvImage : Group.IsSolvable ((aschbacherSolvableCore 3 W).map φ) := by
      haveI : Group.IsSolvable (aschbacherSolvableCore 3 W) := hSolvCore
      have hrange : Group.IsSolvable (φ.comp (aschbacherSolvableCore 3 W).subtype).range :=
        Group.isSolvable_of_surjective
          (φ.comp (aschbacherSolvableCore 3 W).subtype).rangeRestrict_surjective
      have hmap : (φ.comp (aschbacherSolvableCore 3 W).subtype).range =
          (aschbacherSolvableCore 3 W).map φ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hmap]
      exact hrange
    have hcomm_eq : ⁅Pbar, c.lbarInn⁆ = c.lbarInn := by
      rw [hPbar_eq]
      exact Subgroup.commutator_eq_self
    have hInn_le_image : c.lbarInn ≤ (aschbacherSolvableCore 3 W).map φ := by
      rw [← hcomm_eq]
      exact hCommutImage
    have hSolvInn : Group.IsSolvable c.lbarInn := by
      haveI : Group.IsSolvable ((aschbacherSolvableCore 3 W).map φ) := hSolvImage
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hInn_le_image) (Subgroup.inclusion_injective _)
    exact False.elim ((Group.IsPerfect.not_isSolvable (G := c.lbarInn)) hSolvInn)

theorem normalizes_of_le_C'''
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 x) (hJC : J ≤ Cbar c) :
    A ≤ Subgroup.normalizer (J : Set G) := by
  classical
  have hAL : A ≤ c.L := hAPL.trans inf_le_right
  have hAW : A ≤ Subgroup.centralizer ({x} : Set G) := le_centralizer_of_le_inf c hAPL hx
  have hJW : J ≤ Subgroup.centralizer ({x} : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hJM : J ≤ D.M := hJC.trans (Subgroup.map_subtype_le _)
  have hcommL : ⁅c.L, J⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L D.M J c.le_normalizer_L
      hJM).mp hJC
  have hJA : ⁅J, A⁆ ≤ CFSG.Open.pCoreOf 2 c.L := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hAL le_rfl).trans hcommL
  have hJAW : ⁅J, A⁆ ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.commutator_le_of_le hJW hAW
  refine le_normalizer_of_commutator_le_theta hJ hAW (le_trans (le_inf hJA hJAW) ?_)
  exact pCoreOf_inf_centralizer_le_solvableCore c
    (pCoreInfCentralizer_normal' c hON hx (hA.2 x (hZA hx)) hx1 hC)

theorem thetaComponentsAt_center_normalized'''
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    ∀ L ∈ thetaComponentsAt 3 x, A ≤ Subgroup.normalizer (L : Set G) := by
  intro L hL
  by_cases hLz : L = Lz c x
  · subst hLz
    have hAL : A ≤ c.L := hAPL.trans inf_le_right
    have hAW : A ≤ Subgroup.centralizer ({x} : Set G) :=
      le_centralizer_of_le_inf c hAPL hx
    intro a ha
    exact CFSG.RankThree.PartTwo.Sec8.Item812Res2.mem_normalizer_inSubgroup_perfectResidual
      (Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨hAL ha, hAW ha⟩))
  · exact normalizes_of_le_C''' c hON hP hA hZA hAPL hx hx1 hC hL
      (thetaComponent_le_C_of_ne_Lz_core' c hON hP hA hZA hx hx1 hC hL hLz)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
