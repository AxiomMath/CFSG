module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair

public section

namespace CFSG.Quasithin.H13.C1294

noncomputable abbrev sl4D : CFSG.LieType.Universal.UniversalRootDatum (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :=
  CFSG.LieType.Universal.SpecialLinear.rootDatum 3 (ZMod 2)

noncomputable abbrev sl4H : Fin sl4D.rank → Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :=
  CFSG.LieType.Universal.SpecialLinear.torus 3 (ZMod 2)

noncomputable abbrev sl4n : Fin sl4D.rank → Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) :=
  CFSG.LieType.Universal.SpecialLinear.weylRep 3 (ZMod 2)

noncomputable abbrev sl4B : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :=
  CFSG.LieType.Steinberg.borel sl4D sl4H

noncomputable abbrev sl4N : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :=
  CFSG.LieType.Steinberg.weylN sl4n sl4H

noncomputable abbrev sl4S : Set (CFSG.GH74.BNPair.WeylGroup sl4B sl4N) :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.simpleRefl sl4D sl4n sl4H

noncomputable instance sl4_cartan_normal : (CFSG.GH74.BNPair.cartan sl4B sl4N).Normal :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.cartan_borel_weylN_normal
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum 3 (ZMod 2))
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras 3 (ZMod 2))

theorem sl4_isBNPair : CFSG.GroupTheory.TitsSystem.IsBNPair sl4B sl4N sl4S :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.isBNPair_borel_weylN
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum 3 (ZMod 2))
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras 3 (ZMod 2))

theorem sl4_overgroup_parabolic :
    ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)), sl4B ≤ P →
      ∃! J : Set (CFSG.GH74.BNPair.WeylGroup sl4B sl4N),
        J ⊆ sl4S ∧ P = CFSG.GH74.BNPair.parabolic sl4B sl4N J :=
  (CFSG.GroupTheory.TitsSystem.bourbaki_tits_standard_parabolics sl4_isBNPair).2.2.1

end CFSG.Quasithin.H13.C1294
