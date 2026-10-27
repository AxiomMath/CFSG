module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwo
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

theorem false_of_fixedDatum_glTwo {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq3 : 3 < p ^ f) {F : Type} [Group F]
    (e : F ≃* glPi π 2 (p ^ f) K) (h : FixedDatum F) : False := by
  obtain ⟨R, P, hPR, -, hPnc, hRs, hRn⟩ := h
  have hN : (R.map e.toMonoidHom).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨e.symm g * r * (e.symm g)⁻¹, hRn _ r hr, ?_⟩
    simp
  let eR : R ≃* R.map e.toMonoidHom := Subgroup.equivMapOfInjective R e.toMonoidHom e.injective
  haveI : Group.IsSolvable (R.map e.toMonoidHom) := Group.isSolvable_of_surjective (f := eR.toMonoidHom) eR.surjective
  have hNc : IsCyclic (R.map e.toMonoidHom) :=
    glPi_two_solvable_normal_cyclic hK hq3 (R.map e.toMonoidHom) inferInstance
  haveI : IsCyclic R := eR.isCyclic.mpr hNc
  have : IsCyclic (P.subgroupOf R) := inferInstance
  exact hPnc ((Subgroup.subgroupOfEquivOfLe hPR).isCyclic.mp this)

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
