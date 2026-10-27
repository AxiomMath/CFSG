module

public import CFSG.Quasithin.EmptyFaithful.SBd14Ctx
public import CFSG.Quasithin.EmptyFaithful.T1531Geom

public section

namespace CFSG.Quasithin.SBd14

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.V_classes (r : RestHyp T Mc M V₁ V₂ Yp I L t) :
    ∃ z : G, z ∈ VZ T M ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ g ∈ T, g * z = z * g) ∧
      ∀ y ∈ VZ T M, y ≠ 1 →
        (∃ m ∈ M, m * y * m⁻¹ = z) ∨ ∃ v ∈ V₁, v ≠ 1 ∧ ∃ m ∈ M, m * y * m⁻¹ = v := by
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D := r.ctx.hyp.decomp
  obtain ⟨z, hzV, hz1, hz₁, hz₂, hzT⟩ := exists_fixed_singular hyp D
  refine ⟨z, hzV, hz1, r.V_sq z hzV, fun g hg => mul_inv_eq_iff_eq_mul.mp (hzT g hg), ?_⟩
  intro y hyV hy1
  by_cases hys : y ∈ V₁ ∨ y ∈ V₂
  · right
    rcases hys with h | h
    · exact ⟨y, h, hy1, 1, M.one_mem, by simp⟩
    · refine ⟨t * y * t⁻¹, D.swap₂ y h, fun e => hy1 ?_, t, D.t_mem, rfl⟩
      simpa [mul_assoc] using congrArg (fun w => t⁻¹ * w * t) e
  · left
    push Not at hys
    exact exists_conj_singular hyp D ⟨hyV, hys.1, hys.2⟩ ⟨hzV, hz₁, hz₂⟩

end CFSG.Quasithin.SBd14
