module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGroup
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.L32A.C.SL3N

open Matrix CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem transvection_mulVec {i j : Fin 3} (hij : i ≠ j) (c : F) (v : Fin 3 → F) :
    ((SpecialLinearGroup.transvection hij c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      v + Pi.single i (c * v j) := by
  rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec]
  congr 1
  funext k
  simp only [mulVec, dotProduct, single_apply, Pi.single_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · have hik : i ≠ k := fun h => hk h.symm
    simp [hk, hik]

theorem upMat_mulVec (x y z : F) (v : Fin 3 → F) :
    upMat x y z *ᵥ v = ![v 0 + z * v 1 + y * v 2, v 1 + x * v 2, v 2] := by
  funext k
  fin_cases k <;> simp [upMat, mulVec, dotProduct, Fin.sum_univ_three]

theorem u3Mat_mulVec (x y z : F) (v : Fin 3 → F) :
    u3Mat x y z *ᵥ v = ![v 0, x * v 0 + v 1, y * v 0 + z * v 1 + v 2] := by
  funext k
  fin_cases k <;> simp [u3Mat, mulVec, dotProduct, Fin.sum_univ_three]

variable [CharP F 2]

theorem fix_upperUni {v : Fin 3 → F}
    (hv : ∀ u ∈ upperUni F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : v 1 = 0 ∧ v 2 = 0 := by
  have h1 := congrFun (hv (up3 1 0 0) (mem_upperUni.mpr ⟨1, 0, 0, rfl⟩)) 1
  have h2 := congrFun (hv (up3 0 0 1) (mem_upperUni.mpr ⟨0, 0, 1, rfl⟩)) 0
  rw [up3_coe, upMat_mulVec] at h1 h2
  simp at h1 h2
  exact ⟨by simpa [h1] using h2, h1⟩

theorem upperUni_mulVec_e0 {u : SL(3, F)} (hu : u ∈ upperUni F) :
    (u : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  rw [up3_coe, upMat_mulVec]
  funext k
  fin_cases k <;> simp

theorem upperUni_mulVec_two {u : SL(3, F)} (hu : u ∈ upperUni F) (w : Fin 3 → F) :
    ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 2 = w 2 := by
  obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hu
  rw [up3_coe, upMat_mulVec]
  simp

theorem entries_of_mem_normalizer {g : SL(3, F)}
    (hg : g ∈ Subgroup.normalizer (upperUni F : Set SL(3, F))) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hconj : ∀ u ∈ upperUni F, g⁻¹ * u * g ∈ upperUni F := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
    simpa using this
  have hfix : ∀ u ∈ upperUni F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 := by
    intro u hu
    have h1 := upperUni_mulVec_e0 (hconj u hu)
    have e : (u : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ * u * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      have h : u * g = g * (g⁻¹ * u * g) := by group
      exact congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
    rw [mulVec_mulVec, e, ← mulVec_mulVec, h1]
  obtain ⟨h10, h20⟩ := fix_upperUni hfix
  simp only [mulVec_single_one, Matrix.col_apply] at h10 h20
  refine ⟨h10, h20, ?_⟩
  have hu1 : up3 (1 : F) 0 0 ∈ upperUni F := mem_upperUni.mpr ⟨1, 0, 0, rfl⟩
  have hgu : g * up3 1 0 0 * g⁻¹ ∈ upperUni F := (Subgroup.mem_normalizer_iff.mp hg _).mp hu1
  have he1 : (Pi.single 1 1 : Fin 3 → F) = (up3 (1 : F) 0 0 : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single 2 1 - Pi.single 2 1 := by
    rw [up3_coe, upMat_mulVec]
    funext k
    fin_cases k <;> simp
  have h2 := upperUni_mulVec_two hgu ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1)
  have e : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 =
      ((g * up3 1 0 0 * g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1) -
          (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 := by
    have e2 : (g : Matrix (Fin 3) (Fin 3) F) * (up3 (1 : F) 0 0 : Matrix (Fin 3) (Fin 3) F) =
        ((g * up3 1 0 0 * g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
          (g : Matrix (Fin 3) (Fin 3) F) := by
      have h : g * up3 1 0 0 = g * up3 1 0 0 * g⁻¹ * g := by group
      exact congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
    rw [he1, mulVec_sub, mulVec_mulVec, mulVec_mulVec, e2]
  have h3 := congrFun e 2
  rw [Pi.sub_apply, h2, sub_self] at h3
  simpa [mulVec_single_one, Matrix.col_apply] using h3

omit [CharP F 2] in
theorem diag_mul_eq_one {g : SL(3, F)} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  have h := g.2
  rw [det_fin_three, h10, h20, h21] at h
  simpa using h

omit [CharP F 2] in
theorem eq_smul_of_comm (φ : (Fin 3 → F) →+ (Fin 3 → F))
    (hφ : ∀ (g : SL(3, F)) (v : Fin 3 → F),
      φ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v) :
    ∃ c : F, ∀ v, φ v = c • v := by
  classical
  have key : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      φ (Pi.single i c) = Pi.single i (c * φ (Pi.single j 1) j) := by
    intro i j hij c
    have h := hφ (SpecialLinearGroup.transvection hij c) (Pi.single j 1)
    rw [transvection_mulVec, transvection_mulVec, map_add] at h
    have e : Pi.single i (c * (Pi.single j (1 : F) : Fin 3 → F) j) =
        (Pi.single i c : Fin 3 → F) := by simp
    rw [e] at h
    exact add_left_cancel h
  set c₀ := φ (Pi.single 0 1) 0 with hc₀
  have h1 : φ (Pi.single 1 1) 1 = c₀ := by
    rw [key 1 0 (by decide) 1]
    simp [hc₀]
  have h0 : ∀ c : F, φ (Pi.single 0 c) = Pi.single 0 (c * c₀) := by
    intro c
    rw [key 0 1 (by decide) c, h1]
  have hall : ∀ (i : Fin 3) (c : F), φ (Pi.single i c) = Pi.single i (c * c₀) := by
    intro i c
    fin_cases i
    · exact h0 c
    · exact key 1 0 (by decide) c
    · exact key 2 0 (by decide) c
  refine ⟨c₀, fun v => ?_⟩
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum]
  simp only [hall, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext k
  simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · subst hk
    simp [mul_comm]
  · simp

omit [CharP F 2] in
theorem eq_bot_or_eq_top (M : AddSubgroup (Fin 3 → F))
    (hM : ∀ (g : SL(3, F)), ∀ v ∈ M, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  classical
  by_cases hb : M = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨v, hvM⟩, hv0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hb
  have hv0 : v ≠ 0 := fun h => hv0' (Subtype.ext h)
  have hmove : ∀ w ∈ M, ∀ (i j : Fin 3) (hij : i ≠ j) (c : F), Pi.single i (c * w j) ∈ M := by
    intro w hw i j hij c
    have h := M.sub_mem (hM (SpecialLinearGroup.transvection hij c) w hw) hw
    rwa [transvection_mulVec, add_sub_cancel_left] at h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hline : ∀ i, i ≠ j → ∀ c : F, (Pi.single i c : Fin 3 → F) ∈ M := by
    intro i hij c
    have := hmove v hvM i j hij (c / v j)
    rwa [div_mul_cancel₀ c hj] at this
  have hall : ∀ (k : Fin 3) (c : F), (Pi.single k c : Fin 3 → F) ∈ M := by
    intro k c
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨i, hik⟩ : ∃ i : Fin 3, i ≠ k := by
        fin_cases k
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have h1 := hmove (Pi.single i 1) (hline i hik 1) k i (Ne.symm hik) c
      simpa using h1
    · exact hline k hkj c
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact AddSubgroup.sum_mem _ fun k _ => hall k (w k)

end CFSG.Quasithin.H13.L32A.C.SL3N
