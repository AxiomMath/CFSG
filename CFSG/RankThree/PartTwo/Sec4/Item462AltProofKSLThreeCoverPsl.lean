module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCover
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeLiftPslLinear
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeLiftPslUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ker_projOf_eq_center {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) :
    (projOf (slPi π 3 (p ^ f) K)).ker = Subgroup.center (slPi π 3 (p ^ f) K) := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  ext s
  rw [mem_ker_projOf, Subgroup.mem_center_iff]
  constructor
  · intro hs g
    exact Subtype.ext (commute_of_mem_statedScalars hs (g : GL (Fin 3) K))
  · intro h
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    exact (congrArg Subtype.val (h ⟨x, hx⟩)).symm

theorem coverLift_of_mulEquiv_psl {X : Type} [Group X] (hX : Group.IsPerfect X) {π : Bool}
    {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (e : X ≃* projImage (slPi π 3 (p ^ f) K)) : CoverLift X π p f K := by
  have hperfP : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcP : Subgroup.center (projImage (slPi π 3 (p ^ f) K)) = ⊥ :=
    center_projImage_eq_bot hK hq
  have hcX : Subgroup.center X = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, hcP, Subgroup.map_bot]
  refine ⟨e.symm.toMonoidHom.comp (projOf (slPi π 3 (p ^ f) K)), ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp (projOf_surjective _)
  · rw [hcX, MonoidHom.comap_bot, ← ker_projOf_eq_center hK hq]
    exact MonoidHom.ker_comp_of_injective (projOf (slPi π 3 (p ^ f) K)) e.symm.toMonoidHom
      e.symm.injective
  · intro β hβ
    have hζ : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    cases π
    · obtain ⟨ζ', h3, hl⟩ := exists_lift_aut_psl_unitary hK hq2 _ hζ
      refine ⟨ζ', h3, fun s => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hl s, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    · obtain ⟨ζ', h3, hl⟩ := exists_lift_aut_psl_linear hK _ hζ
      refine ⟨ζ', h3, fun s => ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hl s, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
