module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.SteinbergCBTwistedForm

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SteinbergCB Matrix

abbrev QIdx : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {F : Type} [Field F] {σ : F →+* F}

theorem statedQuadMinus_two {K : Type} [Field K] (b c : K) (v : QIdx → K) :
    StatedQuadMinus 2 K b c v = v (.inl 0) * v (.inr (.inl 0)) + v (.inr (.inr 0)) ^ 2 +
      b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 := by
  simp [StatedQuadMinus]

section Coord

variable (hinv : ∀ x, σ (σ x) = x) (ω : F)

@[expose] def coordB : frobFixed σ := ⟨ω + σ ω, mem_frobFixed.2 (frob_trace_mem hinv ω)⟩

@[expose] def coordC : frobFixed σ := ⟨ω * σ ω, mem_frobFixed.2 (frob_norm_mem hinv ω)⟩

@[expose] def coordInv : (QIdx → frobFixed σ) →ₗ[frobFixed σ] twistedForm σ where
  toFun v := twMk hinv (v (.inl 0)) ((v (.inr (.inr 0)) : F) + v (.inr (.inr 1)) * ω)
    (v (.inr (.inl 0)))
  map_add' v w := by
    apply Subtype.ext
    simp only [twMk_coe, Submodule.coe_add]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c v := by
    apply Subtype.ext
    simp only [twMk_coe, Submodule.coe_smul, RingHom.id_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Subfield.smul_def, frobFixed_apply] <;> ring

theorem coordInv_coe (v : QIdx → frobFixed σ) :
    ((coordInv hinv ω v : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) =
      !![(v (.inl 0) : F), (v (.inr (.inr 0)) : F) + v (.inr (.inr 1)) * ω;
        σ ((v (.inr (.inr 0)) : F) + v (.inr (.inr 1)) * ω), (v (.inr (.inl 0)) : F)] :=
  rfl

variable {hinv ω}

theorem coordInv_injective (hω : σ ω ≠ ω) : Function.Injective (coordInv hinv ω) := by
  intro v w h
  have h1 := congrArg (fun X : twistedForm σ => (X : Matrix (Fin 2) (Fin 2) F)) h
  simp only [coordInv_coe] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e01 := congrFun (congrFun h1 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e11 e01
  have hσ := congrArg σ e01
  simp only [map_add, map_mul, frobFixed_apply] at hσ
  have ht : ((v (.inr (.inr 1)) : F) - w (.inr (.inr 1))) * (ω - σ ω) = 0 := by
    linear_combination e01 - hσ
  have ht' : (v (.inr (.inr 1)) : F) = w (.inr (.inr 1)) := by
    have := (mul_eq_zero.1 ht).resolve_right (sub_ne_zero.2 (Ne.symm hω))
    exact sub_eq_zero.1 this
  have hu : (v (.inr (.inr 0)) : F) = w (.inr (.inr 0)) := by
    rw [ht'] at e01
    exact add_right_cancel e01
  funext i
  rcases i with i | i | i
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact Subtype.ext e00
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact Subtype.ext e11
  · fin_cases i
    · exact Subtype.ext hu
    · exact Subtype.ext ht'

theorem coordInv_surjective (hω : σ ω ≠ ω) : Function.Surjective (coordInv hinv ω) := by
  intro X
  obtain ⟨α, β, hα, hβ, hz⟩ := exists_frob_decomp hinv hω ((X : Matrix (Fin 2) (Fin 2) F) 0 1)
  have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = σ (α + β * ω) := by
    rw [← hz]
    exact (twistedForm_entry X.2 0 1).symm
  refine ⟨Sum.elim (fun _ => ⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩)
    (Sum.elim (fun _ => ⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem X.2 1⟩)
      ![⟨α, mem_frobFixed.2 hα⟩, ⟨β, mem_frobFixed.2 hβ⟩]), ?_⟩
  apply Subtype.ext
  rw [coordInv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hz, h10]

variable (hinv)

@[expose] noncomputable def twistCoords (hω : σ ω ≠ ω) :
    twistedForm σ ≃ₗ[frobFixed σ] (QIdx → frobFixed σ) :=
  (LinearEquiv.ofBijective (coordInv hinv ω) ⟨coordInv_injective (hinv := hinv) hω, coordInv_surjective (hinv := hinv) hω⟩).symm

theorem twistCoords_symm_apply (hω : σ ω ≠ ω) (v : QIdx → frobFixed σ) :
    (twistCoords hinv hω).symm v = coordInv hinv ω v := rfl

variable (ω)

theorem twistedDet_coordInv (h2 : (2 : F) = 0) (v : QIdx → frobFixed σ) :
    twistedDet σ (coordInv hinv ω v) =
      StatedQuadMinus 2 (frobFixed σ) (coordB hinv ω) (coordC hinv ω) v := by
  apply Subtype.ext
  rw [twistedDet_apply, coordInv_coe, statedQuadMinus_two, det_fin_two_of]
  simp only [map_add, map_mul, frobFixed_apply, coordB, coordC, Subfield.coe_add,
    Subfield.coe_mul, SubmonoidClass.coe_pow]
  linear_combination (-((v (.inr (.inr 0)) : F) ^ 2 + (ω + σ ω) * v (.inr (.inr 0)) *
    v (.inr (.inr 1)) + ω * σ ω * (v (.inr (.inr 1)) : F) ^ 2)) * h2

theorem coordB_nonsplit {ω : F} (h2 : (2 : F) = 0) (hω : σ ω ≠ ω) (s : frobFixed σ) :
    s ^ 2 + coordB hinv ω * s + coordC hinv ω ≠ 0 := by
  intro h
  have h' : ((s : F) + ω) * ((s : F) + σ ω) = 0 := by
    have := congrArg Subtype.val h
    simp only [Subfield.coe_add, Subfield.coe_mul, SubmonoidClass.coe_pow, coordB, coordC,
      ZeroMemClass.coe_zero] at this
    linear_combination this
  have hs : σ (s : F) = s := frobFixed_apply s
  rcases mul_eq_zero.1 h' with h1 | h1
  · apply hω
    have : ω = s := by linear_combination h1 - (s : F) * h2
    rw [this, hs]
  · apply hω
    have h3 : σ ω = s := by linear_combination h1 - (s : F) * h2
    have h4 : ω = s := by rw [← hinv ω, h3, hs]
    rw [h3, h4]

end Coord

end CFSG.Quasithin.G11.Harris.L2
