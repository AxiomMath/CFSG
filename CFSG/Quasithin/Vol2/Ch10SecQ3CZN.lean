module

public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.Vol2.Ch10SecALift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique SecA

section Matrix

variable {F : Type} [Field F]

theorem upper_of_conj_unip {δ : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : ∃ c : F, δ * unipSL 1 * δ⁻¹ = unipSL c) : (δ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨c, hc⟩ := hc
  have hc' : δ * unipSL 1 = unipSL c * δ := by
    rw [← hc]
    group
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [unipSL_zero, one_mul] at hc'
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) (mul_left_cancel (a := δ) (hc'.trans (mul_one _).symm))
    simp [coe_unipSL] at h1
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) hc'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_unipSL] at h00
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.empty_val'] at h00
  have : c * (δ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -h00
  exact (mul_eq_zero.mp this).resolve_left hc0

variable [Fintype F] {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
  {g : Matrix.SpecialLinearGroup (Fin 2) F}

theorem card_eq_of_conj_unip (hP1 : ∀ p ∈ P, ∃ b : F, g * p * g⁻¹ = unipSL b)
    (hP2 : ∀ b : F, g⁻¹ * unipSL b * g ∈ P) : Nat.card P = Fintype.card F := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective (fun b => ⟨g⁻¹ * unipSL b * g, hP2 b⟩) ⟨fun b b' h => ?_,
    fun p => ?_⟩
  · have h1 := congrArg (fun x : ↥P => (g * (x : Matrix.SpecialLinearGroup (Fin 2) F) * g⁻¹ :
      Matrix.SpecialLinearGroup (Fin 2) F)) h
    simp only [show ∀ z, g * (g⁻¹ * unipSL z * g) * g⁻¹ = unipSL z by intro z; group] at h1
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simpa [coe_unipSL] using h2
  · obtain ⟨b, hb⟩ := hP1 p p.2
    refine ⟨b, Subtype.ext ?_⟩
    simp only
    rw [← hb]
    group

theorem card_normalizer_le (hP1 : ∀ p ∈ P, ∃ b : F, g * p * g⁻¹ = unipSL b)
    (hP2 : ∀ b : F, g⁻¹ * unipSL b * g ∈ P) :
    Nat.card (Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) F))) ≤
      Fintype.card F * (Fintype.card F - 1) := by
  classical
  have hup : ∀ δ ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro δ hδ
    obtain ⟨c, hc⟩ := hP1 _ ((Subgroup.mem_normalizer_iff.mp hδ _).mp (hP2 1))
    exact upper_of_conj_unip ⟨c, by rw [← hc]; group⟩
  have hdet : ∀ δ ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 *
        ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
          1 := by
    intro δ hδ
    have h := (g * δ * g⁻¹).2
    rw [Matrix.det_fin_two, hup δ hδ, mul_zero, sub_zero] at h
    exact h
  set f : ↥(Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) F))) →
      {a : F // a ≠ 0} × F := fun δ =>
    (⟨((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0,
      left_ne_zero_of_mul_eq_one (hdet δ δ.2)⟩,
      ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1)
    with hf
  have hinj : Function.Injective f := by
    intro δ ε h
    simp only [hf, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 : ((g * δ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 1 = ((g * ε * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) 1 1 := by
      have e1 := hdet δ δ.2
      have e2 := hdet ε ε.2
      rw [h1] at e1
      exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e2) (e1.trans e2.symm)
    have h4 : g * (δ : Matrix.SpecialLinearGroup (Fin 2) F) * g⁻¹ = g * ε * g⁻¹ := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact h1
      · exact h2
      · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue]
        rw [hup δ δ.2, hup ε ε.2]
      · exact h3
    exact Subtype.ext (by simpa using h4)
  calc Nat.card _ ≤ Nat.card ({a : F // a ≠ 0} × F) := Nat.card_le_card_of_injective f hinj
    _ = Fintype.card F * (Fintype.card F - 1) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, mul_comm]

end Matrix

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
