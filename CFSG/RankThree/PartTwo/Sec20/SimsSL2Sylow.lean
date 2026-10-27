module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsSL2

open CFSG.SL2MinimalFaithful
open scoped MatrixGroups

section Core

variable {F : Type*} [Field F]

private def lower (y : F) : SL(2, F) := ⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two]⟩

private theorem coe_lower (y : F) :
    ((lower y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; y, 1] := rfl

private theorem matrix_conj_upper [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1)
    (s x : F) (hs : s * M 1 0 = M 0 0) :
    !![1, s; 0, 1] * (M * !![1, x; 0, 1] * M.adjugate) * !![1, s; 0, 1] =
      !![1, 0; M 1 0 ^ 2 * x, 1] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hs ⊢
  simp only [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hdet - (a * c * x) * h2 - (c * x) * hs
  · linear_combination s * h2 + (2 * s) * hdet - (s * c * x + a * x) * hs
  · linear_combination (-(c ^ 2 * x)) * h2
  · linear_combination hdet - (c * x) * hs

private theorem unipotent_mul_conj_mul_unipotent [CharP F 2] (r : SL(2, F)) (s x : F)
    (hs : s * r 1 0 = r 0 0) :
    unipotent s * (r * unipotent x * r⁻¹) * unipotent s = lower (r 1 0 ^ 2 * x) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_unipotent, coe_lower]
  exact matrix_conj_upper (r : Matrix (Fin 2) (Fin 2) F) r.det_coe s x hs

private theorem matrix_conj_upper_triangular (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1)
    (hc : M 1 0 = 0) (x : F) :
    M * !![1, x; 0, 1] * M.adjugate = !![1, M 0 0 ^ 2 * x; 0, 1] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hc ⊢
  subst hc
  simp only [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hdet
  · ring
  · linear_combination hdet

private theorem conj_unipotent_of_lower_left_eq_zero (r : SL(2, F)) (hc : r 1 0 = 0) (x : F) :
    r * unipotent x * r⁻¹ = unipotent (r 0 0 ^ 2 * x) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_unipotent]
  exact matrix_conj_upper_triangular (r : Matrix (Fin 2) (Fin 2) F) r.det_coe hc x

private theorem matrix_eq_upper_lower_upper (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1)
    (hc : M 1 0 ≠ 0) (s t : F) (hs : s * M 1 0 = M 0 0 - 1) (ht : t * M 1 0 = M 1 1 - 1) :
    !![1, s; 0, 1] * !![1, 0; M 1 0, 1] * !![1, t; 0, 1] = M := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hc hs ht ⊢
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination hs
  · apply mul_left_cancel₀ hc
    linear_combination hdet + a * ht + (c * t + 1) * hs
  · linear_combination ht

private theorem unipotent_mem_range (x : F) : unipotent x ∈ (unipotentHom (F := F)).range :=
  ⟨Multiplicative.ofAdd x, rfl⟩

private theorem mem_of_lower_left_ne_zero (R : Subgroup SL(2, F)) (hu : ∀ x, unipotent x ∈ R)
    (hl : ∀ y, lower y ∈ R) (M : SL(2, F)) (hc : M 1 0 ≠ 0) :
    M ∈ R := by
  have h := matrix_eq_upper_lower_upper (M : Matrix (Fin 2) (Fin 2) F) M.det_coe hc
    ((M 0 0 - 1) / M 1 0) ((M 1 1 - 1) / M 1 0) (div_mul_cancel₀ _ hc) (div_mul_cancel₀ _ hc)
  have hM : M = unipotent ((M 0 0 - 1) / M 1 0) * lower (M 1 0) *
      unipotent ((M 1 1 - 1) / M 1 0) := by
    refine Subtype.ext ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, coe_lower]
    exact h.symm
  rw [hM]
  exact R.mul_mem (R.mul_mem (hu _) (hl _)) (hu _)

private theorem le_normalizer_or_eq_top_of_unipotent_le [CharP F 2] [Finite F]
    (R : Subgroup SL(2, F)) (hR : (unipotentHom (F := F)).range ≤ R) :
    R ≤ Subgroup.normalizer (((unipotentHom (F := F)).range : Subgroup SL(2, F)) :
      Set SL(2, F)) ∨ R = ⊤ := by
  have hu : ∀ x : F, unipotent x ∈ R := fun x => hR (unipotent_mem_range x)
  by_cases h : ∀ r ∈ R, r 1 0 = 0
  · left
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    intro m hm
    obtain ⟨t, rfl⟩ := hm
    change r * unipotent (Multiplicative.toAdd t) * r⁻¹ ∈ (unipotentHom (F := F)).range
    rw [conj_unipotent_of_lower_left_eq_zero r (h r hr)]
    exact unipotent_mem_range _
  · right
    simp only [not_forall] at h
    obtain ⟨r, hr, hc⟩ := h
    have hl : ∀ y : F, lower y ∈ R := by
      intro y
      have hc2 : r 1 0 ^ 2 ≠ 0 := pow_ne_zero 2 hc
      have := unipotent_mul_conj_mul_unipotent r (r 0 0 / r 1 0) (y / r 1 0 ^ 2)
        (div_mul_cancel₀ _ hc)
      rw [mul_div_cancel₀ _ hc2] at this
      rw [← this]
      exact R.mul_mem (R.mul_mem (hu _) (R.mul_mem (R.mul_mem hr (hu _)) (R.inv_mem hr))) (hu _)
    refine eq_top_iff.2 fun M _ => ?_
    by_cases hM : M 1 0 = 0
    · have ha : M 0 0 ≠ 0 := by
        intro h0
        have hdet := M.det_coe
        rw [Matrix.det_fin_two, h0, hM] at hdet
        simp at hdet
      have h' : lower (1 : F) * M ∈ R := by
        apply mem_of_lower_left_ne_zero R hu hl
        simp [coe_lower, Matrix.mul_apply, Fin.sum_univ_two, hM, ha]
      have := R.mul_mem (R.inv_mem (hl 1)) h'
      simpa using this
    · exact mem_of_lower_left_ne_zero R hu hl M hM

private theorem dichotomy_of_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    {U R : Subgroup A}
    (h : R.map φ.toMonoidHom ≤ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup B) : Set B) ∨
      R.map φ.toMonoidHom = ⊤) :
    R ≤ Subgroup.normalizer (U : Set A) ∨ R = ⊤ := by
  have hmem : ∀ (K : Subgroup A) (x : A), φ x ∈ K.map φ.toMonoidHom ↔ x ∈ K := fun K x =>
    Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
  rcases h with h | h
  · left
    intro r hr
    have hr' : φ r ∈ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup B) : Set B) :=
      h ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hr' ⊢
    intro a
    have := hr' (φ a)
    rw [← map_mul, ← map_inv, ← map_mul, hmem U, hmem U] at this
    exact this
  · right
    refine eq_top_iff.2 fun x _ => ?_
    have hx : φ x ∈ R.map φ.toMonoidHom := h ▸ Subgroup.mem_top _
    exact (hmem R x).1 hx

private theorem card_range_unipotentHom :
    Nat.card (unipotentHom (F := F)).range = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective unipotentHom_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

private theorem factorization_card_sl2 [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) : (Nat.card SL(2, F)).factorization 2 = n := by
  rw [card_specialLinearGroup_fin_two, hF]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn.ne') two_ne_zero
  have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have hne : (2 ^ n) ^ 2 - 1 ≠ 0 := by omega
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

private theorem exists_equiv_map_sylow_eq [CharP F 2] [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) {Y : Type*} [Group Y] [Finite Y] (e' : Y ≃* SL(2, F))
    (U : Sylow 2 Y) :
    ∃ φ : Y ≃* SL(2, F),
      (U : Subgroup Y).map φ.toMonoidHom = (unipotentHom (F := F)).range := by
  have hY : Nat.card Y = Nat.card SL(2, F) := Nat.card_congr e'.toEquiv
  have hUcard : Nat.card (U : Subgroup Y) = Nat.card F := by
    rw [Sylow.card_eq_multiplicity, hY, factorization_card_sl2 hn hF, hF]
  have hU' : Nat.card ((U : Subgroup Y).map e'.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hUcard]
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hF hU'
  let φ : Y ≃* SL(2, F) := e'.trans (MulAut.conj g).symm
  have hle : (unipotentHom (F := F)).range ≤ (U : Subgroup Y).map φ.toMonoidHom := by
    rintro _ ⟨t, rfl⟩
    change unipotent (Multiplicative.toAdd t) ∈ _
    rw [Subgroup.mem_map_equiv]
    have := Subgroup.mem_map_equiv.mp (hg (Multiplicative.toAdd t))
    simpa [φ, MulEquiv.symm_trans_apply] using this
  refine ⟨φ, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hUcard,
    card_range_unipotentHom]

end Core

theorem le_normalizer_or_eq_top_of_sylow_psl2 {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (hn : 0 < n) (e : Y ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))
    (U : Sylow 2 Y) (R : Subgroup Y) (hUR : (U : Subgroup Y) ≤ R) :
    R ≤ Subgroup.normalizer ((U : Subgroup Y) : Set Y) ∨ R = ⊤ := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.ne'
  let e' : Y ≃* SL(2, GaloisField 2 n) :=
    e.trans ((CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 2 (GaloisField 2 n)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL (GaloisField 2 n)))
  obtain ⟨φ, hφ⟩ := exists_equiv_map_sylow_eq hn hF e' U
  refine dichotomy_of_equiv φ ?_
  rw [hφ]
  exact le_normalizer_or_eq_top_of_unipotent_le _ (hφ ▸ Subgroup.map_mono hUR)

end CFSG.RankThree.PartTwo.Sec20.SimsSL2
