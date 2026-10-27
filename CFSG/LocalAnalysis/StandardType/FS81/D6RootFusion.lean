module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.D6RootWords

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {X : Type} [Group X]

theorem Basis3.acts_of_forall_vec {k : ℕ} (B : Basis3 X k) {g : X}
    {M : Matrix (Fin k) (Fin k) (ZMod 3)} (h : ∀ v, g * B.vec v * g⁻¹ = B.vec (M *ᵥ v)) :
    B.Acts g M := by
  intro j
  rw [← B.vec_single j, h]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_mem_acts_list_prod {B : Basis3 X 7} {Y K : Subgroup X} {g : X}
    (hK : evenFix0 6 ⊆ B.realized K) (hKY : K ≤ Y)
    (hgY : K.map (MulAut.conj g).toMonoidHom ≤ Y)
    (hg : ∀ v, g * B.vec v * g⁻¹ = B.vec (wbar1 *ᵥ v))
    (l : List (Matrix (Fin 7) (Fin 7) (ZMod 3)))
    (hl : ∀ A ∈ l, A ∈ evenFix0 6 ∨ ∃ s ∈ evenFix0 6, A = wbar1 * s * wbar1) :
    ∃ y ∈ Y, B.Acts y l.prod := by
  have hgA : B.Acts g wbar1 := B.acts_of_forall_vec hg
  have hgA' : B.Acts g⁻¹ wbar1 := by
    refine B.acts_of_forall_vec fun v => ?_
    have h := hg (wbar1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, wbar1_mul_self, Matrix.one_mulVec] at h
    calc g⁻¹ * B.vec v * g⁻¹⁻¹ = g⁻¹ * (g * B.vec (wbar1 *ᵥ v) * g⁻¹) * g := by
          rw [h, inv_inv]
      _ = B.vec (wbar1 *ᵥ v) := by group
  induction l with
  | nil => exact ⟨1, Y.one_mem, by simpa using B.acts_one⟩
  | cons A l ih =>
    obtain ⟨y, hyY, hy⟩ := ih fun A' hA' => hl A' (List.mem_cons_of_mem _ hA')
    have hA : ∃ z ∈ Y, B.Acts z A := by
      rcases hl A List.mem_cons_self with hA | ⟨s, hs, rfl⟩
      · obtain ⟨z, hzK, hz⟩ := hK hA
        exact ⟨z, hKY hzK, hz⟩
      · obtain ⟨z, hzK, hz⟩ := hK hs
        refine ⟨g * z * g⁻¹, hgY ⟨z, hzK, rfl⟩, ?_⟩
        exact B.acts_mul (B.acts_mul hgA hz) hgA'
    obtain ⟨z, hzY, hz⟩ := hA
    exact ⟨z * y, Y.mul_mem hzY hyY, by simpa using B.acts_mul hz hy⟩

theorem exists_mem_conj_b_zero_eq_vec_of_isD6Root [Finite X] {B : Basis3 X 7}
    {Y K : Subgroup X} {g : X} (hK : evenFix0 6 ⊆ B.realized K) (hKY : K ≤ Y)
    (hgY : K.map (MulAut.conj g).toMonoidHom ≤ Y)
    (hg : ∀ v, g * B.vec v * g⁻¹ = B.vec (wbar1 *ᵥ v)) {e : Coords 7} (he : IsD6Root e) :
    ∃ y ∈ Y, y ∈ Subgroup.normalizer (B.span : Set X) ∧ y * B.b 0 * y⁻¹ = B.vec e := by
  obtain ⟨l, hl, hle⟩ := exists_list_prod_mulVec_of_isD6Root he
  obtain ⟨y, hyY, hy⟩ := exists_mem_acts_list_prod hK hKY hgY hg l hl
  refine ⟨y, hyY, B.mem_normalizer_of_acts hy, ?_⟩
  rw [← B.vec_single 0, B.acts_vec hy, hle]

end CFSG.StandardType.FrameRoute.FS81
