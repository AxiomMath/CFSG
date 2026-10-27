module

public import CFSG.RankThree.PartOne.KF4.B2Families

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

section Orbit

variable
  {K : Type} [Field K]

variable (K) in
@[expose] def f4B2Range : Subgroup (GL (Fin 4) K) := (f4B2RepGL K).range

@[expose] def MemR (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ h ∈ f4B2Range K, (h : Matrix (Fin 4) (Fin 4) K) = M

theorem MemR.mul {M N : Matrix (Fin 4) (Fin 4) K} (hM : MemR M) (hN : MemR N) :
    MemR (M * N) := by
  obtain ⟨g, hg, rfl⟩ := hM
  obtain ⟨h, hh, rfl⟩ := hN
  exact ⟨g * h, mul_mem hg hh, by simp⟩

theorem memR_of_mem {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K f4B2Support) :
    MemR (f4B2_data.Mat g) :=
  ⟨f4B2RepGL K ⟨g, hg⟩, ⟨_, rfl⟩, rfl⟩

theorem memR_x2 (c : K) : MemR (1 + single 1 2 c) := by
  have := memR_of_mem (xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inl rfl)) c)
  rwa [f4B2_Mat_x2] at this

theorem memR_y2 (c : K) : MemR (1 + single 2 1 c) := by
  have := memR_of_mem (yUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inl rfl)) c)
  rwa [f4B2_Mat_y2] at this

theorem memR_x3 (c : K) : MemR (1 + (single 0 1 c + single 2 3 c)) := by
  have := memR_of_mem (xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inr rfl)) c)
  rwa [f4B2_Mat_x3] at this

theorem memR_na : MemR (f4B2Na : Matrix (Fin 4) (Fin 4) K) := by
  have := memR_of_mem (weylElt_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inl rfl)) 1)
  rwa [f4B2_Mat_na] at this

theorem memR_nb : MemR (f4B2Nb : Matrix (Fin 4) (Fin 4) K) := by
  have := memR_of_mem (weylElt_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inr rfl)) 1)
  rwa [f4B2_Mat_nb] at this

theorem memR_diag_a (a : Kˣ) : MemR (Matrix.diagonal ![1, (a : K), ((a⁻¹ : Kˣ) : K), 1]) := by
  have := memR_of_mem (torus2Elt_mem_f4B2 (K := K) a 1)
  rw [f4B2_Mat_torus] at this
  simpa using this

theorem memR_diag_b (b : Kˣ) : MemR (Matrix.diagonal ![(b : K), 1, 1, ((b⁻¹ : Kˣ) : K)]) := by
  have := memR_of_mem (torus2Elt_mem_f4B2 (K := K) b b)
  rw [f4B2_Mat_torus] at this
  simpa using this

theorem memR_pos3 (s : K) : MemR (1 + s • (-single 0 3 1) : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨ε, h⟩ := f4B2Family_3 (K := K)
  have := memR_of_mem (pinnedX_mem_f4B2 (f4B2PosRoot_mem_parabolicRoots 3) ((ε⁻¹ : Kˣ) * s))
  rw [h] at this
  rwa [← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero ε), one_mul] at this

theorem memR_neg3 (s : K) : MemR (1 + s • (-single 3 0 1) : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨ε, h⟩ := f4B2Family_neg_3 (K := K)
  have := memR_of_mem (pinnedX_mem_f4B2 (neg_f4B2PosRoot_mem_parabolicRoots 3) ((ε⁻¹ : Kˣ) * s))
  rw [h] at this
  rwa [← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero ε), one_mul] at this

theorem orbit_12 {u1 u2 : K} (h : u1 ≠ 0 ∨ u2 ≠ 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, MemR M ∧ M *ᵥ (Pi.single 1 1 : Fin 4 → K) = ![0, u1, u2, 0] ∧
      M *ᵥ ![1, 1, 0, 0] = ![1, u1, u2, 0] := by
  by_cases h1 : u1 = 0
  · have h2 : u2 ≠ 0 := h.resolve_left (not_not.2 h1)
    obtain ⟨a, ha⟩ : ∃ a : Kˣ, (a : K) = -u2⁻¹ := ⟨Units.mk0 (-u2⁻¹) (by simp [h2]), rfl⟩
    have ha' : ((a⁻¹ : Kˣ) : K) = -u2 := by
      rw [Units.val_inv_eq_inv_val, ha, inv_neg, inv_inv]
    refine ⟨Matrix.diagonal ![1, (a : K), ((a⁻¹ : Kˣ) : K), 1] * f4B2Na,
      (memR_diag_a a).mul memR_na, ?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply, f4B2Na,
          Pi.single_apply, ha', h1]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Matrix.diagonal_apply,
          f4B2Na, ha, ha', h1]
  · obtain ⟨a, ha⟩ : ∃ a : Kˣ, (a : K) = u1 := ⟨Units.mk0 u1 h1, rfl⟩
    have ha' : ((a⁻¹ : Kˣ) : K) = u1⁻¹ := by rw [Units.val_inv_eq_inv_val, ha]
    refine ⟨Matrix.diagonal ![1, (a : K), ((a⁻¹ : Kˣ) : K), 1] * (1 + single 2 1 (u1 * u2)),
      (memR_diag_a a).mul (memR_y2 _), ?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply, ha, ha', h1]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, ha, ha', h1]

theorem orbit_03 {v0 v3 : K} (h : v0 ≠ 0 ∨ v3 ≠ 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, MemR M ∧ M *ᵥ (Pi.single 1 1 : Fin 4 → K) = Pi.single 1 1 ∧
      M *ᵥ (Pi.single 2 1 : Fin 4 → K) = Pi.single 2 1 ∧
      M *ᵥ (Pi.single 0 1 : Fin 4 → K) = ![v0, 0, 0, v3] := by
  by_cases h0 : v0 = 0
  · have h3 : v3 ≠ 0 := h.resolve_left (not_not.2 h0)
    obtain ⟨b, hb⟩ : ∃ b : Kˣ, (b : K) = -v3⁻¹ := ⟨Units.mk0 (-v3⁻¹) (by simp [h3]), rfl⟩
    have hb' : ((b⁻¹ : Kˣ) : K) = -v3 := by
      rw [Units.val_inv_eq_inv_val, hb, inv_neg, inv_inv]
    refine ⟨Matrix.diagonal ![(b : K), 1, 1, ((b⁻¹ : Kˣ) : K)] *
      ((1 + (-1 : K) • (-single 0 3 1)) * (1 + (1 : K) • (-single 3 0 1))),
      (memR_diag_b b).mul ((memR_pos3 _).mul (memR_neg3 _)), ?_, ?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply, hb, hb', h0]
  · obtain ⟨b, hb⟩ : ∃ b : Kˣ, (b : K) = v0 := ⟨Units.mk0 v0 h0, rfl⟩
    have hb' : ((b⁻¹ : Kˣ) : K) = v0⁻¹ := by rw [Units.val_inv_eq_inv_val, hb]
    refine ⟨Matrix.diagonal ![(b : K), 1, 1, ((b⁻¹ : Kˣ) : K)] *
      (1 + (-(v0 * v3)) • (-single 3 0 1)), (memR_diag_b b).mul (memR_neg3 _), ?_, ?_, ?_⟩
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply]
    · ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.single_apply, Matrix.add_apply, Matrix.one_apply, Pi.single_apply, hb, hb', h0]

theorem exists_mem_range_mulVec {a : Fin 4 → K} (ha : a ≠ 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, MemR M ∧ M *ᵥ (Pi.single 1 1 : Fin 4 → K) = a := by
  by_cases h12 : a 1 ≠ 0 ∨ a 2 ≠ 0
  · obtain ⟨M, hM, hM1, hM2⟩ := orbit_12 h12
    by_cases h03 : a 0 ≠ 0 ∨ a 3 ≠ 0
    · obtain ⟨H, hH, hH1, hH2, hH0⟩ := orbit_03 h03
      refine ⟨H * (M * (1 + (single 0 1 1 + single 2 3 1))), hH.mul (hM.mul (memR_x3 1)), ?_⟩
      have e1 : (1 + (single 0 1 1 + single 2 3 1) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          (Pi.single 1 1 : Fin 4 → K) = ![1, 1, 0, 0] := by
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Matrix.add_apply, Matrix.one_apply,
            Pi.single_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, hM2]
      have e2 : (![1, a 1, a 2, 0] : Fin 4 → K) = (Pi.single 0 1 : Fin 4 → K) +
          (a 1 • (Pi.single 1 1 : Fin 4 → K) + a 2 • (Pi.single 2 1 : Fin 4 → K)) := by
        ext i
        fin_cases i <;> simp []
      rw [e2, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hH1,
        hH2, hH0]
      ext i
      fin_cases i <;> simp []
    · have h0 : a 0 = 0 := by
        by_contra h; exact h03 (Or.inl h)
      have h3 : a 3 = 0 := by
        by_contra h; exact h03 (Or.inr h)
      refine ⟨M, hM, ?_⟩
      rw [hM1]
      ext i
      fin_cases i <;> simp [h0, h3]
  · have h1 : a 1 = 0 := by
      by_contra h; exact h12 (Or.inl h)
    have h2 : a 2 = 0 := by
      by_contra h; exact h12 (Or.inr h)
    have h03 : a 0 ≠ 0 ∨ a 3 ≠ 0 := by
      by_contra h
      push Not at h
      refine ha ?_
      ext i
      fin_cases i <;> simp [h.1, h.2, h1, h2]
    obtain ⟨H, hH, hH1, hH2, hH0⟩ := orbit_03 h03
    refine ⟨H * f4B2Nb, hH.mul memR_nb, ?_⟩
    have e1 : (f4B2Nb : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single 1 1 : Fin 4 → K) =
        Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, f4B2Nb, Pi.single_apply]
    rw [← Matrix.mulVec_mulVec, e1, hH0]
    ext i
    fin_cases i <;> simp [h1, h2]

end Orbit

end CFSG.RankThree.PartOne.KF4
