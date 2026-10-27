module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Bridge
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem exists_conj_of_pow_three_cover {Kb : Type} [Group Kb] [Finite Kb]
    (hperf : Group.IsPerfect Kb)
    (hJ : Nonempty (Kb ⧸ Subgroup.center Kb ≃* Blueprint.NativeSporadic.J3))
    (α : MulAut Kb) (hα : α ^ 3 = 1) : ∃ g : Kb, MulAut.conj g = α := by
  obtain ⟨e⟩ := hJ
  let r : MulAut Kb →* MulAut (Kb ⧸ Subgroup.center Kb) :=
    { toFun := fun σ => QuotientGroup.congr (Subgroup.center Kb) (Subgroup.center Kb) σ
        (Subgroup.map_center_eq σ)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x => rfl
      map_mul' := fun σ τ => by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x => rfl }
  have hr : ∀ (σ : MulAut Kb) (y : Kb),
      r σ (QuotientGroup.mk y) = (QuotientGroup.mk (σ y) : Kb ⧸ Subgroup.center Kb) :=
    fun σ y => rfl
  have h3 : (r α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨gb, hgb⟩ := exists_conj_of_pow_three_J3 e (r α) h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  refine ⟨g, ?_⟩
  symm
  refine Sec4.Item426.mulAut_eq_of_forall_inv_mul_mem_center hperf (fun y => ?_)
  have h1 := congrArg (fun γ : MulAut (Kb ⧸ Subgroup.center Kb) => γ (QuotientGroup.mk y)) hgb
  simp only [MulAut.conj_apply, hr] at h1
  rw [← QuotientGroup.eq_one_iff]
  simp only [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [← h1]
  group

end CFSG.RankThree.PartTwo.Sec8.Hering611
