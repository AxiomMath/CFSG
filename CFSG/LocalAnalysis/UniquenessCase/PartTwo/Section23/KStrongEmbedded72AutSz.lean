module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Setup
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Socle
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoSz32
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Fischer

theorem kf7_autSz_case
    {p : ℕ} (hp : p.Prime) (hp5 : p = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : F07.IsAutSz ↥L 5)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hSgrp, hSz, ⟨eL⟩⟩ := hshape
  letI : Group S := hSgrp
  have hSM : CFSG.Blueprint.SuzukiModel S 2 5 :=
    (CFSG.Blueprint.LieModel.suzukiModel (G := S) hSz).2
  haveI : Finite S := CFSG.LieType.Simplicity.fam_suzuki_finiteness S 2 5 hSM
  obtain ⟨-, a, ha, F, hFfield, hFfin, hf, hFcard, ⟨eS⟩⟩ := hSM
  have ha2 : a = 2 := by omega
  subst ha2
  letI : Field F := hFfield
  letI : Finite F := hFfin
  have hFcard' : Nat.card F = 2 ^ (2 * 2 + 1) := by
    rw [show 2 * 2 + 1 = 5 by norm_num]
    exact hFcard
  obtain ⟨-, hFsimple, hFnab⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab
      (b := 2) (by norm_num) hFcard'
  haveI : IsSimpleGroup (CFSG.Blueprint.suzukiGroup 2 F) := hFsimple
  haveI : IsSimpleGroup S := eS.isSimpleGroup
  have hSnab : ∃ x y : S, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hFnab
    refine ⟨eS.symm x, eS.symm y, fun h => hxy ?_⟩
    simpa using congrArg eS h
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, -, -⟩ := kf7_setup hp (by norm_num) hO hLN hKL hN
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  let K' : Subgroup (MulAut S) := (K.subgroupOf L).map eL.toMonoidHom
  have hK'normal : K'.Normal :=
    (hKn.subgroupOf L).map eL.toMonoidHom eL.surjective
  have hK'simple : IsSimpleGroup ↥K' := by
    haveI : IsSimpleGroup ↥(K.subgroupOf L) :=
      (Subgroup.subgroupOfEquivOfLe hKL).isSimpleGroup
    exact (eL.subgroupMap (K.subgroupOf L)).symm.isSimpleGroup
  have hK'eq : K' = innerAut S := by
    change K' = (MulAut.conj : S →* MulAut S).range
    exact eq_inner_of_normal_simple_subgroup_mulAut hSnab hK'normal hK'simple
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hSnab
      have hx : x ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  have eKS : ↥K ≃* S :=
    ((Subgroup.subgroupOfEquivOfLe hKL).symm.trans (eL.subgroupMap (K.subgroupOf L))).trans
      ((MulEquiv.subgroupCongr hK'eq).trans (innerAutEquiv hZ).symm)
  let hv : (TauCeti.LieTypeIndex.suzuki 2).Valid :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzuki_valid (by norm_num)
  let d : TauCeti.ValidLieTypeIndex := ⟨.suzuki 2, hv⟩
  have hd : d.1 = .suzuki 2 := rfl
  obtain ⟨eCat⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_suzukiGroup_equiv_cat
      (b := 2) (by norm_num) hFcard'
  have eKCat : ↥K ≃* CFSG.AGLEmbedding.CatGroup d := eKS.trans (eS.trans eCat)
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  have e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d :=
    (MulEquiv.subgroupCongr hKeq).symm.trans eKCat
  exact (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.isSolvable_and_pRank_three_le_one_of_sz32
    (d := d) hd hO hN e).1

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
