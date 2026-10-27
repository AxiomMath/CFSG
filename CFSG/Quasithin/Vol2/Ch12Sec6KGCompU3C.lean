module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3B
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary
import CFSG.LieType.SeitzGeneration.SpFourMix

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

theorem hypForm_eq_hypHf (x y : HypIndex 1 1 → K) : hypForm h 1 1 x y = hypHf h x y := by
  rw [gramForm_apply, hypHf, hrow, ← dotProduct_mulVec]

theorem map_map_bar (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    (A.map h.bar).map h.bar = A := by
  ext i j
  simp [h.bar_bar]

theorem eq_one_of_mul_map_bar {A A' : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hA : (A.map h.bar)ᵀ * hypGram 1 1 K * A = hypGram 1 1 K) (hAA : A * A' = 1) {c : K}
    (hAc : A * A.map h.bar = c • 1) : c = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hA'A : A' * A = 1 := mul_eq_one_comm.mp hAA
  have hAb : A.map h.bar = c • A' := by
    calc A.map h.bar = A' * (A * A.map h.bar) := by rw [← mul_assoc, hA'A, one_mul]
      _ = c • A' := by rw [hAc, mul_smul_comm, mul_one]
  have hbA : A.map h.bar * A = c • 1 := by rw [hAb, smul_mul_assoc, hA'A]
  have hcb : h.bar c = c := by
    have h1 := congrArg (Matrix.map · h.bar) hAc
    rw [Matrix.map_mul, map_map_bar, map_smul_bar, Matrix.map_one _ (map_zero h.bar)
      (map_one h.bar), hbA] at h1
    have := congrFun (congrFun h1 (.inl 0)) (.inl 0)
    simpa using this.symm
  have hJb : (hypGram 1 1 K).map h.bar = hypGram 1 1 K := hypGram_map _
  have hAbar : Aᵀ * hypGram 1 1 K * A.map h.bar = hypGram 1 1 K := by
    have h1 := congrArg (Matrix.map · h.bar) hA
    rwa [Matrix.map_mul, Matrix.map_mul, transpose_map, map_map_bar, hJb] at h1
  have hc2 : c * c = 1 := by
    have h1 : ((A * A.map h.bar).map h.bar)ᵀ * hypGram 1 1 K * (A * A.map h.bar) =
        hypGram 1 1 K := by
      rw [Matrix.map_mul, map_map_bar, transpose_mul]
      have : Aᵀ * (A.map h.bar)ᵀ * hypGram 1 1 K * (A * A.map h.bar) =
          Aᵀ * ((A.map h.bar)ᵀ * hypGram 1 1 K * A) * A.map h.bar := by
        simp only [Matrix.mul_assoc]
      rw [this, hA, hAbar]
    rw [hAc, map_smul_bar, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), hcb, transpose_smul,
      transpose_one, smul_mul_assoc, one_mul, smul_mul_assoc, mul_smul_comm, mul_one,
      smul_smul] at h1
    have := congrFun (congrFun h1 (.inl 0)) (.inr (.inr 0))
    simpa [hypGram_apply] using this
  have hdb : (A.map h.bar).det = h.bar A.det := by rw [RingHom.map_det]; rfl
  have hN : A.det * h.bar A.det = 1 := by
    have h1 := congrArg Matrix.det hA
    rw [det_mul, det_mul, det_transpose, hdb] at h1
    have hJ : (hypGram 1 1 K).det ≠ 0 := det_hypGram_ne_zero
    have : (h.bar A.det * A.det - 1) * (hypGram 1 1 K).det = 0 := by linear_combination h1
    rw [mul_comm]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hJ)
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg Matrix.det hAc
    rw [det_mul, hdb, det_smul, det_one, mul_one, card_hypIndex, hN] at h1
    exact h1.symm
  calc c = c ^ 3 * (c * c)⁻¹ * c ^ 0 := by
        rw [pow_zero, mul_one, pow_succ, pow_two]
        have hc0 : c ≠ 0 := fun h0 => by rw [h0, zero_mul] at hc2; exact zero_ne_one hc2
        field_simp
    _ = 1 := by rw [hc3, hc2, inv_one, mul_one, pow_zero, mul_one]

theorem exists_transv (hp2 : p ≠ 2) {A A' : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hA : (A.map h.bar)ᵀ * hypGram 1 1 K * A = hypGram 1 1 K) (hAA : A * A' = 1) {c : K}
    (hAc : A * A.map h.bar = c • 1) :
    ∃ u u' : Matrix (HypIndex 1 1) (HypIndex 1 1) K, u * u' = 1 ∧ u' * u = 1 ∧
      (u.map h.bar)ᵀ * hypGram 1 1 K * u = hypGram 1 1 K ∧ u ^ p = 1 ∧
      (∀ c : K, u ≠ c • 1) ∧ A * u.map h.bar * A' = u' := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  have hc1 := eq_one_of_mul_map_bar h hA hAA hAc
  rw [hc1, one_smul] at hAc
  have hA'A : A' * A = 1 := mul_eq_one_comm.mp hAA
  let Ag : GL (HypIndex 1 1) K := ⟨A, A', hAA, hA'A⟩
  have hAg : Ag ∈ hypUnitary h 1 1 := hA
  obtain ⟨b, t, s, ht, hs, hττ, hfin, Bf, hBs, -, hBsym⟩ :=
    exists_descended_form h hp2 (r := 1) (ε := 1) (by norm_num) hAg one_ne_zero
      (by rw [one_smul]; exact hAc)
  have hτv : ∀ v, ((b : K) • semilinearMatrixMap h (Ag : Matrix (HypIndex 1 1) (HypIndex 1 1) K))
      v = ((b : K) • A) *ᵥ fun i => h.bar (v i) := fun v => by
    rw [LinearMap.smul_apply, semilinearMatrixMap_apply, smul_mulVec]
  have : FiniteDimensional h.fixedField
      (conjFixed h ((b : K) • semilinearMatrixMap h
        (Ag : Matrix (HypIndex 1 1) (HypIndex 1 1) K))) :=
    Module.finite_of_finrank_eq_succ hfin
  let bW := Module.finBasisOfFinrankEq h.fixedField _ hfin
  obtain ⟨v, hv0, hvv⟩ : ∃ v, v ≠ 0 ∧ Bf v v = 0 := by
    rcases hBsym with hsym | halt
    · obtain ⟨x, hx0, hx⟩ := CFSG.LieType.SeitzGeneration.exists_nonzero_zero_quadratic
        (K := h.fixedField) (σ := Fin (2 * 1 + 1)) (by simp)
        (LinearMap.BilinForm.toMatrix bW Bf)
      refine ⟨bW.equivFun.symm x, fun h0 => hx0 ((LinearEquiv.map_eq_zero_iff _).mp h0), ?_⟩
      rw [← LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
      exact hx
    · exact ⟨bW 0, bW.ne_zero 0, halt (bW 0)⟩
  set e : HypIndex 1 1 → K := v.1 with he
  have he0 : e ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hee : hypHf h e e = 0 := by
    have h1 := hBs v v
    rw [hvv, hypForm_eq_hypHf] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hs
  have hτe : ((b : K) • A) *ᵥ (fun i => h.bar (e i)) = e := by
    rw [← hτv]
    exact (mem_conjFixed (h := h)).mp v.2
  have hNb : (b : K) * h.bar (b : K) = 1 := by
    obtain ⟨i⟩ : Nonempty (HypIndex 1 1) := ⟨.inl 0⟩
    have h1 := hττ (Pi.single i 1)
    rw [hτv, hτv] at h1
    have h2 : ((b : K) • A) *ᵥ (fun j => h.bar ((((b : K) • A) *ᵥ fun k =>
        h.bar ((Pi.single i 1 : HypIndex 1 1 → K) k)) j)) =
        ((b : K) * h.bar (b : K)) • Pi.single i 1 := by
      have h3 : (fun j => h.bar ((((b : K) • A) *ᵥ fun k =>
          h.bar ((Pi.single i 1 : HypIndex 1 1 → K) k)) j)) =
          (h.bar (b : K) • A.map h.bar) *ᵥ (Pi.single i 1 : HypIndex 1 1 → K) := by
        funext j
        rw [RingHom.map_mulVec]
        congr 1
        · ext k l
          simp
        · funext k
          simp [h.bar_bar]
      rw [h3, mulVec_mulVec, smul_mul_smul_comm, hAc, smul_mulVec, one_mulVec]
    rw [h2] at h1
    have := congrFun h1 i
    simpa using this
  set A₁ := (b : K) • A with hA₁
  set A₁' := (b : K)⁻¹ • A' with hA₁'
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have hA₁A₁' : A₁ * A₁' = 1 := by
    rw [hA₁, hA₁', smul_mul_smul_comm, hAA, mul_inv_cancel₀ hb0, one_smul]
  have hA₁u : (A₁.map h.bar)ᵀ * hypGram 1 1 K * A₁ = hypGram 1 1 K := by
    have h1 : (A₁.map h.bar)ᵀ * hypGram 1 1 K * A₁ =
        ((b : K) * h.bar (b : K)) • ((A.map h.bar)ᵀ * hypGram 1 1 K * A) := by
      rw [hA₁, map_smul_bar, transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        smul_smul, mul_comm (h.bar (b : K))]
    rw [h1, hNb, one_smul, hA]
  have hA₁bar : A₁ * A₁.map h.bar = 1 := by
    rw [hA₁, map_smul_bar, smul_mul_smul_comm, hAc, hNb, one_smul]
  have hconj : ∀ X : Matrix (HypIndex 1 1) (HypIndex 1 1) K, A * X * A' = A₁ * X * A₁' := by
    intro X
    simp only [hA₁, hA₁', smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hb0, one_smul]
  have hee' : hrow h.bar (hypGram 1 1 K) e ⬝ᵥ e = 0 := hee
  set u := unitTransv h.bar (hypGram 1 1 K) e (t : K) with hu
  set u' := unitTransv h.bar (hypGram 1 1 K) e (-(t : K)) with hu'
  have huu : u * u' = 1 := unitTransv_mul_neg hee' _
  have hu'u : u' * u = 1 := mul_eq_one_comm.mp huu
  have hN : vecMulVec e (hrow h.bar (hypGram 1 1 K) e) *
      vecMulVec e (hrow h.bar (hypGram 1 1 K) e) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hee', zero_smul, vecMulVec_zero]
  refine ⟨u, u', huu, hu'u, ?_, ?_, ?_, ?_⟩
  · rw [adjoint_unitTransv (bar := h.bar) h.bar_bar (hypGram_herm h), ht, mul_assoc, ← hu', hu'u,
      mul_one]
  · have h1 := pow_char_of_cube (K := K) (p := p) hp2
      (N := (t : K) • vecMulVec e (hrow h.bar (hypGram 1 1 K) e)) (by
        rw [smul_mul_smul_comm, hN, smul_zero, zero_mul])
    exact h1
  · intro c hc
    have h1 : (t : K) • vecMulVec e (hrow h.bar (hypGram 1 1 K) e) = (c - 1) • 1 := by
      rw [sub_smul, one_smul, ← hc, hu, unitTransv]
      abel
    have h2 := congrArg (fun M => M * M) h1
    simp only [smul_mul_smul_comm, hN, smul_zero, mul_one] at h2
    rcases smul_eq_zero.mp h2.symm with h0 | h0
    · have hc1' : c - 1 = 0 := mul_self_eq_zero.mp h0
      rw [hc1', zero_smul] at h1
      rcases smul_eq_zero.mp h1 with h0' | h0'
      · exact t.ne_zero h0'
      · rcases vecMulVec_eq_zero.mp h0' with h0'' | h0''
        · exact he0 h0''
        · exact he0 (eq_zero_of_hypHf_eq_zero h fun y => by
            rw [hypHf, h0'', zero_dotProduct])
    · exact one_ne_zero h0
  · rw [hconj, conj_map_unitTransv (bar := h.bar) h.bar_bar (hypGram_map _) hypGram_transpose hA₁u
      hA₁A₁' hA₁bar hτe, ht]

end CFSG.Quasithin.H13.S126C
