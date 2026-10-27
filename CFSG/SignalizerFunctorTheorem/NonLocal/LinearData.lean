module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SignalizerFunctorTheorem.NonLocal

local notation "SL" => Matrix.SpecialLinearGroup

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable (n : ℕ) (K : Type*) [Field K]

@[expose] noncomputable def linearProjData : ProjData K (Fin n) (SL (Fin n) K)
    (projectiveSL n K) where
  ρ := Matrix.SpecialLinearGroup.toGL
  hρ := Matrix.SpecialLinearGroup.toGL_injective
  π := proj n K
  hπ := proj_surjective n K
  hker := by
    intro h
    rw [proj_eq_one_iff, mem_scalars]
    constructor
    · rintro ⟨c, -, hc⟩
      exact ⟨c, by simpa using hc⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_, by simpa using hc⟩
      have h1 : (h : Matrix (Fin n) (Fin n) K).det = 1 := h.2
      rw [show (h : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K) by simpa using hc,
        scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
      exact Units.ext (by simpa using h1)



variable {n : ℕ} {K : Type*} [Field K] (k : Subfield K)

@[expose] def tvElt (i j : Fin n) (hij : i ≠ j) (c : k) : SL (Fin n) k :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem coe_map_tvElt (i j : Fin n) (hij : i ≠ j) (c : k) :
    ((Matrix.SpecialLinearGroup.map k.subtype (tvElt k i j hij c) : SL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = transvection i j (c : K) := by
  ext a b
  rw [SpecialLinearGroup.map_apply_coe]
  simp only [tvElt, transvection, RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.map_apply]
  rw [map_add]
  congr 1
  · by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]



variable {n : ℕ} {K : Type*} [Field K] (k : Subfield K)

theorem transvection_mulVec_one (i j : Fin n) (v : Fin n → K) :
    (transvection i j (1 : K)) *ᵥ v = v + Pi.single i (v j) := by
  simp [transvection, add_mulVec, Matrix.single_mulVec]
  rfl

theorem linear_irreducible (hn : 2 ≤ n) (W : Submodule K (Fin n → K))
    (hW : ∀ g : SL (Fin n) k, ∀ v ∈ W,
      (((linearProjData n K).ρ (Matrix.SpecialLinearGroup.map k.subtype g) :
        (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  have hT : ∀ (i i' : Fin n) (hii' : i ≠ i') (v : Fin n → K), v ∈ W →
      Pi.single i (v i') ∈ W := by
    intro i i' hii' v hv
    have h1 := hW (tvElt k i i' hii' 1) v hv
    set g : SL (Fin n) K := Matrix.SpecialLinearGroup.map k.subtype (tvElt k i i' hii' 1) with hg
    have h2 : (((linearProjData n K).ρ g : (Matrix (Fin n) (Fin n) K)ˣ) :
        Matrix (Fin n) (Fin n) K) *ᵥ v = v + Pi.single i (v i') := by
      have : (((linearProjData n K).ρ g : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) = transvection i i' (1 : K) :=
        coe_map_tvElt k i i' hii' 1
      rw [this, transvection_mulVec_one]
    rw [h2] at h1
    simpa using W.sub_mem h1 hv
  have hne : ∀ i, i ≠ j → Pi.single i (1 : K) ∈ W := by
    intro i hij
    have h1 := hT i j hij w hwW
    have h2 := W.smul_mem (w j)⁻¹ h1
    rw [← Pi.single_smul] at h2
    simpa [inv_mul_cancel₀ hj] using h2
  have hbasis : ∀ i, Pi.single i (1 : K) ∈ W := by
    intro i
    by_cases hij : i = j
    · subst hij
      obtain ⟨i', hi'⟩ : ∃ i' : Fin n, i' ≠ i := by
        by_contra h
        push Not at h
        have : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := (h _).trans (h _).symm
        simp [Fin.ext_iff] at this
      have h1 := hT i i' hi'.symm (Pi.single i' 1) (hne i' hi')
      simpa using h1
    · exact hne i hij
  rw [eq_top_iff]
  intro v _
  have : v = ∑ i, v i • (Pi.single i (1 : K) : Fin n → K) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact W.sum_mem (fun i _ => W.smul_mem _ (hbasis i))

theorem single_mul_single_self {i j : Fin n} (hij : i ≠ j) :
    (Matrix.single i j (1 : K)) * Matrix.single i j (1 : K) = 0 :=
  Matrix.single_mul_single_of_ne (h := Ne.symm hij) ..

theorem linear_centralizer_eq_one (hn : 2 ≤ n) (x : projectiveSL n K)
    (hx : ∀ g : SL (Fin n) k,
      x * proj n K (Matrix.SpecialLinearGroup.map k.subtype g) =
        proj n K (Matrix.SpecialLinearGroup.map k.subtype g) * x) : x = 1 := by
  obtain ⟨x', rfl⟩ := proj_surjective n K x
  have hcomm : ∀ i j : Fin n, i ≠ j → Commute (Matrix.single i j (1 : K))
      (x' : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    have h1 := hx (tvElt k i j hij 1)
    rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h1
    set T' := Matrix.SpecialLinearGroup.map k.subtype (tvElt k i j hij 1) with hT'
    obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
    set s : SL (Fin n) K := (x' * T')⁻¹ * (T' * x') with hs
    have h2 : T' * x' = (x' * T') * s := (mul_inv_cancel_left _ _).symm
    have h3 : (T' : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j 1 := by
      have := coe_map_tvElt k i j hij 1
      rw [hT']
      simpa [transvection] using this
    have h4 : (T' : Matrix (Fin n) (Fin n) K) * x' =
        ((x' : Matrix (Fin n) (Fin n) K) * T') * scalar (Fin n) (c : K) := by
      calc (T' : Matrix (Fin n) (Fin n) K) * x' = ((T' * x' : SL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := (Matrix.SpecialLinearGroup.coe_mul _ _).symm
        _ = (((x' * T') * s : SL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
            congrArg _ h2
        _ = ((x' * T' : SL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (s : Matrix _ _ _) :=
            Matrix.SpecialLinearGroup.coe_mul _ _
        _ = _ := by rw [hc, Matrix.SpecialLinearGroup.coe_mul x' T']
    set E : Matrix (Fin n) (Fin n) K := Matrix.single i j 1 with hE
    set X : Matrix (Fin n) (Fin n) K := (x' : Matrix (Fin n) (Fin n) K) with hX
    have hE2 : E * E = 0 := single_mul_single_self hij
    by_cases hc1 : (c : K) = 1
    · rw [h3, hc1, map_one, mul_one] at h4
      have : E * X = X * E := by
        have h5 := h4
        simp only [add_mul, mul_add, one_mul, mul_one] at h5
        exact add_left_cancel (a := X) (by simpa [add_comm, add_assoc] using h5)
      exact this
    · exfalso
      have h5 : E * X = X * (((c : K) - 1) • (1 : Matrix (Fin n) (Fin n) K) + (c : K) • E) := by
        rw [h3] at h4
        have h6 : (1 + E) * X = (X * (1 + E)) * scalar (Fin n) (c : K) := h4
        have h7 : scalar (Fin n) (c : K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.smul_one_eq_diagonal]; rfl
        rw [h7] at h6
        simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_add, sub_smul] at h6 ⊢
        rw [mul_sub, mul_smul_comm, mul_one, one_smul, mul_one]
        rw [eq_sub_of_add_eq' h6]
        abel
      set M : Matrix (Fin n) (Fin n) K :=
        ((c : K) - 1) • (1 : Matrix (Fin n) (Fin n) K) + (c : K) • E with hM
      have hcne : (c : K) - 1 ≠ 0 := sub_ne_zero.mpr hc1
      have hMunit : IsUnit M := by
        have hu : IsUnit (((c : K) - 1) • (1 : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, det_one]
          simp [hcne]
        have hr : IsNilpotent ((c : K) • E) := ⟨2, by
          rw [pow_two, smul_mul_smul_comm, hE2]; simp⟩
        have hcm : Commute ((c : K) • E) (((c : K) - 1) • (1 : Matrix (Fin n) (Fin n) K)) :=
          ((Commute.one_right E).smul_left (c : K)).smul_right ((c : K) - 1)
        exact hr.isUnit_add_left_of_commute hu hcm
      have hdetM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMunit
      have hdetE : E.det = 0 := by
        refine Matrix.det_eq_zero_of_row_eq_zero j (fun l => ?_)
        simp only [hE, Matrix.single_apply, ite_eq_right_iff]
        intro h
        exact absurd h.1 hij
      have hdetX : X.det = 1 := x'.2
      have h8 := congrArg Matrix.det h5
      rw [Matrix.det_mul, Matrix.det_mul, hdetE, hdetX] at h8
      have h9 : M.det = 0 := by simpa using h8.symm
      exact hdetM.ne_zero h9
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j hij => hcomm i j hij)
  have hdet : a ^ n = 1 := by
    have h1 : (x' : Matrix (Fin n) (Fin n) K).det = 1 := x'.2
    rw [← ha, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    exact h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hdet
    exact zero_ne_one hdet
  rw [proj_eq_one_iff]
  exact mem_scalars.mpr ⟨Units.mk0 a ha0, Units.ext (by simpa using hdet), by simpa using ha.symm⟩

end CFSG.SignalizerFunctorTheorem.NonLocal
