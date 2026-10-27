module

public import CFSG.RankThree.PartOne.TAIL.KSideSyl
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix Polynomial

noncomputable def embMat34 (F : Type*) [Field F] (A : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F))

theorem embMat34_mul (F : Type*) [Field F] (A B : Matrix (Fin 3) (Fin 3) F) :
    embMat34 F (A * B) = embMat34 F A * embMat34 F B := by
  unfold embMat34
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

theorem embMat34_one (F : Type*) [Field F] : embMat34 F 1 = 1 := by
  unfold embMat34
  rw [Matrix.fromBlocks_one, map_one]

theorem det_embMat34 (F : Type*) [Field F] (A : Matrix (Fin 3) (Fin 3) F) :
    (embMat34 F A).det = A.det := by
  unfold embMat34
  rw [Matrix.coe_reindexAlgEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem embMat34_injective (F : Type*) [Field F] : Function.Injective (embMat34 F) := by
  intro A B h
  unfold embMat34 at h
  have h1 := (Matrix.reindexAlgEquiv F F finSumFinEquiv).injective h
  exact (Matrix.fromBlocks_inj.1 h1).1

@[expose] noncomputable def slEmbed34 (F : Type*) [Field F] :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 4) F where
  toFun x := ⟨embMat34 F (x : Matrix (Fin 3) (Fin 3) F), by rw [det_embMat34, x.2]⟩
  map_one' := by
    apply Subtype.ext
    exact embMat34_one F
  map_mul' x y := by
    apply Subtype.ext
    exact embMat34_mul F _ _

theorem slEmbed34_injective (F : Type*) [Field F] : Function.Injective (slEmbed34 F) := by
  intro x y h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin 4) F => (z : Matrix (Fin 4) (Fin 4) F)) h
  exact Subtype.ext (embMat34_injective F h1)

@[expose] noncomputable def diag2 (F : Type*) [Field F] (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

theorem coe_diag2 (F : Type*) [Field F] (a : Fˣ) :
    (diag2 F a : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F)] := rfl

@[expose] noncomputable def slDiag2 (F : Type*) [Field F] : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := diag2 F
  map_one' := by
    apply Subtype.ext
    rw [coe_diag2, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag2, coe_diag2, coe_diag2,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem slDiag2_injective (F : Type*) [Field F] : Function.Injective (slDiag2 F) := by
  intro a b h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F) 0 0) h
  apply Units.ext
  simpa [slDiag2, coe_diag2] using h1

theorem cubic_no_root {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ 7)
    (a : F) :
    ¬ (X ^ 3 + X + 1 : F[X]).IsRoot a := by
  intro h
  have := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have ha : a ^ 3 + a + 1 = 0 := by simpa using h
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h7 : a ^ 7 = 1 := by
    linear_combination (a ^ 4 + a ^ 2 + a + 1) * ha - (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * h2
  have h127 : a ^ 127 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [Fintype.card_eq_nat_card, hF] at h
  have ha1 : a = 1 := by
    have hg : a ^ Nat.gcd 7 127 = 1 := pow_gcd_eq_one.2 ⟨h7, h127⟩
    simpa using hg
  rw [ha1] at ha
  have : (1 : F) + 1 + 1 = 1 := by
    have : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    rw [this, zero_add]
  have h3 : (1 : F) ^ 3 + 1 + 1 = 1 := by simpa using this
  rw [h3] at ha
  exact one_ne_zero ha

theorem cubic_irred {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ 7) :
    Irreducible (X ^ 3 + X + 1 : F[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ (cubic_no_root hF)
  have : (X ^ 3 + X + 1 : F[X]).natDegree = 3 := by compute_degree!
  rw [this]
  simp

theorem exists_order49_sl3 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7) :
    ∃ x : SpecialLinearGroup (Fin 3) F, orderOf x = 49 := by
  classical
  have := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ 7 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  set g : F[X] := X ^ 3 + X + 1 with hg
  have hgirr : Irreducible g := cubic_irred hF
  have hgdeg : g.natDegree = 3 := by rw [hg]; compute_degree!
  have : Fact (Irreducible g) := ⟨hgirr⟩
  let pb := AdjoinRoot.powerBasis hgirr.ne_zero
  have hdim : pb.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, hgdeg]
  let b : Module.Basis (Fin 3) F (AdjoinRoot g) := pb.basis.reindex (finCongr hdim)
  have : Finite (AdjoinRoot g) := by
    have : Module.Finite F (AdjoinRoot g) := Module.Finite.of_basis b
    exact Module.finite_of_finite F
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hLcard : Nat.card (AdjoinRoot g) = 2 ^ 21 := by
    have h := Module.card_eq_pow_finrank (K := F) (V := AdjoinRoot g)
    rw [Module.finrank_eq_card_basis b, hFcard] at h
    rw [Nat.card_eq_fintype_card, h]
    simp
  have hLunits : Nat.card (AdjoinRoot g)ˣ = 2 ^ 21 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hLcard]
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (AdjoinRoot g)ˣ)
  rw [hLunits] at hu
  have h49 : (49 : ℕ) ∣ 2 ^ 21 - 1 := by norm_num
  obtain ⟨k, hk⟩ := h49
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hu0 : orderOf (u ^ k) = 49 := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hu, hk]; exact Dvd.intro_left 49 rfl), hu, hk]
    simp [hk0]
  set t : AdjoinRoot g := ((u ^ k : (AdjoinRoot g)ˣ) : AdjoinRoot g) with ht
  have ht49 : t ^ 49 = 1 := by
    have h1 : (u ^ k) ^ 49 = 1 := by
      rw [← hu0]
      exact pow_orderOf_eq_one _
    have h2 := congrArg (fun w : (AdjoinRoot g)ˣ => (w : AdjoinRoot g)) h1
    simpa [ht] using h2
  have ht7 : t ^ 7 ≠ 1 := by
    intro h
    have h1 : (u ^ k) ^ 7 = 1 := by
      apply Units.ext
      simpa [ht] using h
    have h2 : orderOf (u ^ k) ∣ 7 := orderOf_dvd_of_pow_eq_one h1
    rw [hu0] at h2
    omega
  let M : Matrix (Fin 3) (Fin 3) F := Algebra.leftMulMatrix b t
  have hM49 : M ^ 49 = 1 := by
    rw [← map_pow (Algebra.leftMulMatrix b), ht49, map_one]
  have hM7 : M ^ 7 ≠ 1 := by
    intro h
    apply ht7
    apply Algebra.leftMulMatrix_injective b
    rw [map_pow, map_one]
    exact h
  have hMdet : M.det = 1 := by
    have h1 : M.det ^ 49 = 1 := by rw [← Matrix.det_pow, hM49, Matrix.det_one]
    have h0 : M.det ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have h127 : M.det ^ 127 = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one M.det h0
      rwa [hFcard] at h
    have hg : M.det ^ Nat.gcd 49 127 = 1 := pow_gcd_eq_one.2 ⟨h1, h127⟩
    simpa using hg
  let X : SpecialLinearGroup (Fin 3) F := ⟨M, hMdet⟩
  have hXc : (X : Matrix (Fin 3) (Fin 3) F) = M := rfl
  refine ⟨X, ?_⟩
  have hnot : X ^ (7 ^ 1) ≠ 1 := by
    intro h
    apply hM7
    have := congrArg (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h
    simpa [Matrix.SpecialLinearGroup.coe_pow, hXc] using this
  have hfin : X ^ (7 ^ (1 + 1)) = 1 := by
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_pow, hXc] using hM49
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := orderOf_eq_prime_pow (p := 7) hnot hfin
  simpa using this

theorem exists_order49_sl4 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7) :
    ∃ x : SpecialLinearGroup (Fin 4) F, orderOf x = 49 := by
  obtain ⟨x, hx⟩ := exists_order49_sl3 hF
  exact ⟨slEmbed34 F x, by rw [orderOf_injective _ (slEmbed34_injective F) x, hx]⟩

theorem exists_order49_sl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 21) :
    ∃ x : SpecialLinearGroup (Fin 2) F, orderOf x = 49 := by
  classical
  have := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ 21 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hunits : Nat.card Fˣ = 2 ^ 21 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hFcard]
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [hunits] at hu
  have h49 : (49 : ℕ) ∣ 2 ^ 21 - 1 := by norm_num
  obtain ⟨k, hk⟩ := h49
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hu0 : orderOf (u ^ k) = 49 := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hu, hk]; exact Dvd.intro_left 49 rfl), hu, hk]
    simp [hk0]
  exact ⟨slDiag2 F (u ^ k), by rw [orderOf_injective _ (slDiag2_injective F) _, hu0]⟩

theorem card_sl_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 21) :
    ∃ r, Nat.card (SpecialLinearGroup (Fin 2) F) = 49 * r ∧ ¬ 7 ∣ r := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ 21 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_SL_field 2, hq]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  refine ⟨(2 ^ 21) * (2 ^ 21 + 1) * ((2 ^ 21 - 1) / 49), ?_, ?_⟩
  · norm_num
  · norm_num

theorem card_sl_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7) :
    ∃ r, Nat.card (SpecialLinearGroup (Fin 3) F) = 49 * r ∧ ¬ 7 ∣ r := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ 7 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_SL_field 3, hq]
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  refine ⟨(2 ^ 7) ^ 3 * ((2 ^ 7) ^ 2 - 1) * ((2 ^ 21 - 1) / 49), ?_, ?_⟩
  · norm_num
  · norm_num

theorem card_sl_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7) :
    ∃ r, Nat.card (SpecialLinearGroup (Fin 4) F) = 49 * r ∧ ¬ 7 ∣ r := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ 7 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_SL_field 4, hq]
  simp only [Fin.prod_univ_four]
  refine ⟨(2 ^ 7) ^ 6 * ((2 ^ 7) ^ 4 - 1) * ((2 ^ 7) ^ 2 - 1) * ((2 ^ 21 - 1) / 49), ?_, ?_⟩
  · norm_num
  · norm_num

theorem sylow_sl_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 21)
    (R : Subgroup (SpecialLinearGroup (Fin 2) F)) (hR : IsPGroup 7 R) :
    IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
  obtain ⟨r, hr, hr7⟩ := card_sl_two hF
  obtain ⟨x, hx⟩ := exists_order49_sl2 hF
  exact cyclic_sylow_seven hr hr7 hx R hR

theorem sylow_sl_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7)
    (R : Subgroup (SpecialLinearGroup (Fin 3) F)) (hR : IsPGroup 7 R) :
    IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
  obtain ⟨r, hr, hr7⟩ := card_sl_three hF
  obtain ⟨x, hx⟩ := exists_order49_sl3 hF
  exact cyclic_sylow_seven hr hr7 hx R hR

theorem sylow_sl_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7)
    (R : Subgroup (SpecialLinearGroup (Fin 4) F)) (hR : IsPGroup 7 R) :
    IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
  obtain ⟨r, hr, hr7⟩ := card_sl_four hF
  obtain ⟨x, hx⟩ := exists_order49_sl4 hF
  exact cyclic_sylow_seven hr hr7 hx R hR

end CFSG.RankThree.PartOne.TAIL
