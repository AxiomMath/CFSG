module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOne3
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneKD5b
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneKD5c3
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneSU6

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ltrcba_narrowOriginalAt_iff_shapeAt (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) :
    S2MathAs3_1615.KD2NarrowOriginalAt lab R I ↔ GGRankOneShapeAt 3 lab R I := by
  constructor
  · intro h L' _ _ ψ hψ hker hperf e J a hset
    obtain ⟨⟨m, hm1, h3m, hshape⟩, hnon⟩ := h L' ψ hψ hker hperf e J a hset
    exact ⟨m, hm1, h3m, hshape, hnon⟩
  · intro h L' _ _ ψ hψ hker hperf e J a hset
    obtain ⟨m, hm1, h3m, hshape, hnon⟩ := h L' ψ hψ hker hperf e J a hset
    exact ⟨⟨m, hm1, h3m, hshape⟩, hnon⟩

theorem ggTBJNoRankOne3_of_strong (h : S2MathAs3_1615.StrongKD2) : GGTBJNoRankOne3 := by
  have hKD2' : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (fun R _ I _ => GGRankOneShapeAt 3 lab R I) := by
    intro lab hlab
    exact LargeEvenLabelAll.mono
      (fun R _ I _ hraw => (ltrcba_narrowOriginalAt_iff_shapeAt lab R I).mp hraw)
      (S2MathAs3_1615.KD2Narrow_iff_originalSlice.mp
        (S2MathAs3_1615.KD2Narrow_of_strong h) lab hlab)
  have hKD5c' : ∀ f : ℕ, 3 ∣ 2 ^ f + 1 →
      LargeEvenLabelAll (⟨.twA, 5, f⟩ : LargeEvenLabel)
        fun R _ I _ => GGSU6NoParabolicAtN 3 I :=
    ggSU6NoParabolicKnown3_of_strong h
  intro G _ _ B Bs x L D J hcfg hJ
  exact ggRankOne_su6_at (n := 3) (by norm_num) hKD2' ggSU6DiagInvertedKnown_holds hKD5c' hcfg hJ

theorem ggFieldTwoCornerNoSL28_of_strong (h : S2MathAs3_1615.StrongKD2) :
    GGFieldTwoCornerNoSL28 :=
  ggFieldTwoCornerNoSL28_of_noRankOne3 (ggTBJNoRankOne3_of_strong h)

end CFSG.StandardType

end
