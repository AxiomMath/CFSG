module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Gen
public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.Open

private abbrev Om12Mat : Subgroup (GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :=
  StatedOmega (StatedQuadPlus 6 (ZMod 2))

private abbrev Om12Proj : Type :=
  StatedProj Om12Mat

private theorem largeEvenMarking_of_mulEquiv_om12 {G : Type} [Group G] {X : Subgroup G}
    (e : ↥X ≃* ↥D6M.Om12) :
    CFSG.StandardType.LargeEvenMarking ↥X
      (fun lab _ _ _ _ _ => lab.n = 1 ∧ lab.tag = .D ∧ lab.rank = 6) ∧
      Subgroup.center ↥X = ⊥ ∧ IsSimpleGroup ↥X := by
  classical
  have hcoe : ⇑(CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2)) =
      StatedQuadPlus 6 (ZMod 2) :=
    CFSG.LieType.Universal.Spin.coe_quadPlus 6 (ZMod 2)
  let eOrth : ↥Om12Mat ≃* ↥D6M.Om12 :=
    CFSG.RankThree.PartOne.statedOmegaOrthEquiv
      (Q := CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))
      (Q₀ := StatedQuadPlus 6 (ZMod 2)) hcoe
  have hQ : CFSG.LieType.ChevTwo.GoodQ (StatedQuadPlus 6 (ZMod 2)) :=
    CFSG.LieType.ChevTwo.goodQ_plus (n := 5) (by norm_num)
  haveI hDsimple : IsSimpleGroup ↥Om12Mat := hQ.simple
  have hOmsimple : IsSimpleGroup ↥D6M.Om12 := eOrth.symm.isSimpleGroup
  have hXsimple : IsSimpleGroup ↥X := by
    haveI := hOmsimple
    exact e.isSimpleGroup
  have hbot : (StatedScalars (Fin 6 ⊕ Fin 6) (ZMod 2)).subgroupOf
      (StatedOmega (StatedQuadPlus 6 (ZMod 2))) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := ZMod 2) (n := 6) (by norm_num)
  have hZD : Subgroup.center ↥Om12Mat = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (K := ZMod 2) (n := 6)
      (by norm_num), hbot]
  have hZO : Subgroup.center ↥D6M.Om12 = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_mulEquiv_of_center_eq_bot eOrth hZD
  have hZX : Subgroup.center ↥X = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_mulEquiv_of_center_eq_bot e.symm hZO
  have hDperf : Group.IsPerfect ↥Om12Mat :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := ZMod 2) (n := 6)
      (by norm_num)
  have hOperf : Group.IsPerfect ↥D6M.Om12 :=
    Group.IsPerfect.ofSurjective (f := eOrth.toMonoidHom) eOrth.surjective
  have hXperf : Group.IsPerfect ↥X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have isoR : Om12Proj ≃* ↥Om12Mat :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot Om12Mat hbot).symm
  have hRsimple : IsSimpleGroup Om12Proj :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
      (K := ZMod 2) (n := 6) (by norm_num)
  have hZR : Subgroup.center Om12Proj = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_mulEquiv_of_center_eq_bot
      (S := ↥Om12Mat) (T := Om12Proj) isoR.symm hZD
  have hRnab : ∃ a b : Om12Proj, a * b ≠ b * a := by
    by_contra h
    have hcomm : ∀ a b : Om12Proj, a * b = b * a := by
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    have htop : Subgroup.center Om12Proj = ⊤ :=
      Subgroup.center_eq_top_iff.mpr (isMulCommutative_iff.mpr hcomm)
    exact (bot_ne_top : (⊥ : Subgroup Om12Proj) ≠ ⊤) (by rw [← hZR, htop])
  have θ : ↥X ⧸ Subgroup.center ↥X ≃* Om12Proj :=
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans
      (e.trans (eOrth.symm.trans isoR.symm))
  refine ⟨?_, hZX, hXsimple⟩
  refine ⟨hXperf.commutator_eq_top, ⟨.D, 6, 1⟩, ?_, ?_⟩
  · simp [CFSG.Assembly.LargeEvenInLambda2]
  · dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact ⟨hRsimple, hRnab, θ, rfl, rfl, rfl⟩

theorem isRow_D6_of_mulEquiv_om12 {G : Type} [Group G] {X : Subgroup G}
    (e : ↥X ≃* ↥D6M.Om12) :
    IsRow Row.D6 X ∧ CFSG.StandardType.LargeEvenMarking ↥X (fun lab _ _ _ _ _ => FSLab lab) ∧
      Subgroup.center ↥X = ⊥ ∧ IsSimpleGroup ↥X := by
  obtain ⟨hmark, hZ, hS⟩ := largeEvenMarking_of_mulEquiv_om12 e
  refine ⟨?_, ?_, hZ, hS⟩
  · unfold IsRow
    exact CFSG.StandardType.largeEvenMarking_mono
      (fun lab R _ I F θ h => ⟨h.1, Or.inl ⟨rfl, h.2.1, h.2.2⟩⟩) hmark
  · exact CFSG.StandardType.largeEvenMarking_mono
      (fun lab R _ I F θ h => ⟨h.1, Or.inl ⟨h.2.1, h.2.2⟩⟩) hmark

end CFSG.StandardType.FrameRoute.FS81
