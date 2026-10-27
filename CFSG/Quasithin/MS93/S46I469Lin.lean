module

public import CFSG.Quasithin.MS93.S46I466bLin

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Quasithin.MS93.S46.I466b
open scoped Matrix

variable {F : Type} [Field F]

theorem exists_pair_conj {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {u v : Fin 3 → F} (hu : u ∈ P) (hv : v ∈ P) (hu0 : u ≠ 0) (huv : v ∉ F ∙ u) :
    ∃ y : SL3 F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = u ∧
      (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = v ∧
      (∀ x : Fin 3 → F, x 1 = 0 → (y : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ P) ∧
      ∀ p ∈ P, (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p) 1 = 0 := by
  obtain ⟨w, hw⟩ := exists_not_mem_of_finrank_eq_two hP
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![u, w, v] j i with hMdef
  have hMv : ∀ x : Fin 3 → F, M *ᵥ x = x 0 • u + x 1 • w + x 2 • v := by
    intro x
    funext i
    simp [hMdef, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hMinj : Function.Injective M.mulVec := by
    intro x x' hxx
    have h0 : M *ᵥ (x - x') = 0 := by rw [Matrix.mulVec_sub, hxx, sub_self]
    rw [hMv] at h0
    set z := x - x' with hz
    have hz1 : z 1 = 0 := by
      by_contra hne
      apply hw
      have e : z 1 • w = -(z 0 • u + z 2 • v) := by
        rw [eq_neg_iff_add_eq_zero, ← h0]; abel
      have : w = (z 1)⁻¹ • (-(z 0 • u + z 2 • v)) := by
        rw [← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact P.smul_mem _ (P.neg_mem (P.add_mem (P.smul_mem _ hu) (P.smul_mem _ hv)))
    have hz2 : z 2 = 0 := by
      by_contra hne
      apply huv
      have e : z 2 • v = -(z 0 • u) := by
        rw [eq_neg_iff_add_eq_zero, ← h0, hz1, zero_smul, add_zero]; abel
      have : v = (z 2)⁻¹ • (-(z 0 • u)) := by
        rw [← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
    have hz0 : z 0 = 0 := by
      rw [hz1, hz2, zero_smul, add_zero, zero_smul, add_zero] at h0
      exact (smul_eq_zero.mp h0).resolve_right hu0
    have : z = 0 := by
      funext i
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
    exact sub_eq_zero.mp this
  have hdet : M.det ≠ 0 := by
    have := Matrix.mulVec_injective_iff_isUnit.mp hMinj
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact this.ne_zero
  set d := M.det with hd
  set M' : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![u, d⁻¹ • w, v] j i with hM'def
  have hM'det : M'.det = 1 := by
    have e : M'.det = d⁻¹ * M.det := by
      rw [Matrix.det_fin_three, Matrix.det_fin_three]
      simp [hM'def, hMdef]
      ring
    rw [e, ← hd, inv_mul_cancel₀ hdet]
  have hM'v : ∀ x : Fin 3 → F, M' *ᵥ x = x 0 • u + x 1 • (d⁻¹ • w) + x 2 • v := by
    intro x
    funext i
    simp [hM'def, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  set m : SL3 F := ⟨M', hM'det⟩ with hmdef
  have hm : ∀ x : Fin 3 → F, (m : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      x 0 • u + x 1 • (d⁻¹ • w) + x 2 • v := hM'v
  refine ⟨m, by rw [hm]; simp, by rw [hm]; simp, fun x hx => ?_, fun p hp => ?_⟩
  · rw [hm, hx, zero_smul, add_zero]
    exact P.add_mem (P.smul_mem _ hu) (P.smul_mem _ hv)
  · obtain ⟨a, c, rfl⟩ := mem_plane_iff hP hu hv hu0 huv hp
    have e : a • u + c • v = (m : Matrix (Fin 3) (Fin 3) F) *ᵥ ![a, 0, c] := by
      rw [hm]; simp
    rw [e, inv_mulVec_mulVec_SL3]
    rfl

theorem exists_rot_pair [CharP F 2] {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {u v : Fin 3 → F} (hu : u ∈ P) (hv : v ∈ P) (hu0 : u ≠ 0) (huv : v ∉ F ∙ u) :
    ∃ B : SL3 F, B ^ 3 = 1 ∧ (∀ x, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ P) ∧
      (B : Matrix (Fin 3) (Fin 3) F) *ᵥ u = v := by
  obtain ⟨y, hy0, hy2, hyP, -⟩ := exists_pair_conj hP hu hv hu0 huv
  refine ⟨y * rot02 * y⁻¹, ?_, fun x => ?_, ?_⟩
  · rw [conj_pow, rot02_pow_three]
    group
  · have e : ((y * rot02 * y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x =
        (y : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((rot02 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) -
            ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
      rw [Matrix.mulVec_sub, mulVec_inv_mulVec_SL3, coe_mul_SL3, coe_mul_SL3,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [e]
    refine hyP _ ?_
    rw [rot02_mulVec]
    simp
  · have e0 : ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = ![1, 0, 0] := by
      rw [← hy0, inv_mulVec_mulVec_SL3]
    rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e0,
      rot02_mulVec, ← hy2]
    congr 1
    funext i
    fin_cases i <;> simp

theorem eq_one_of_mem_axisGroup {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {A : SL3 F} (hA : A ∈ axisGroup P) {x : Fin 3 → F} (hx : x ∉ P)
    (hAx : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : A = 1 := by
  have htop := sup_span_eq_top hP hx
  have hfix : ∀ y : Fin 3 → F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
    intro y
    have hy : y ∈ P ⊔ F ∙ x := by rw [htop]; exact Submodule.mem_top
    obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hA.1 p hp, hAx]
  apply Subtype.ext
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [hfix, coe_one_SL3, Matrix.one_mulVec]

end CFSG.Quasithin.MS93.S46
