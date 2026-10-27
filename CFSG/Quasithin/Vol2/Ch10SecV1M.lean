module

public import CFSG.Quasithin.Background.A3Structure319Defs
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Assembly.LowTwoRank Matrix

namespace V1C

variable {K : Type} [Field K]

@[expose] def diag3 (a b : Kˣ) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact mul_inv_cancel₀ (mul_ne_zero a.ne_zero b.ne_zero)⟩

theorem coe_diag3_pow (a b : Kˣ) (n : ℕ) :
    ((diag3 a b ^ n : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(a : K) ^ n, (b : K) ^ n, (((a : K) * b)⁻¹) ^ n] := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  change (diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹]) ^ n = _
  rw [diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diag3_commute (a b c d : Kˣ) : Commute (diag3 a b) (diag3 c d) := by
  show diag3 a b * diag3 c d = diag3 c d * diag3 a b
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹] *
      diagonal ![(c : K), (d : K), ((c : K) * d)⁻¹]) i j =
    (diagonal ![(c : K), (d : K), ((c : K) * d)⁻¹] *
      diagonal ![(a : K), (b : K), ((a : K) * b)⁻¹]) i j
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext k
  exact mul_comm _ _

theorem diag3_pow_three {ω : Kˣ} (h : ω ^ 3 = 1) : diag3 ω ω⁻¹ ^ 3 = 1 := by
  have hK : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hω : (ω : K) ≠ 0 := ω.ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_diag3_pow, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [hK, inv_pow, hω]

theorem diag3_one_pow_three {ω : Kˣ} (h : ω ^ 3 = 1) : diag3 1 ω ^ 3 = 1 := by
  have hK : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_diag3_pow, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [hK, inv_pow]

theorem diag3_ne_one {ω : Kˣ} (h : ω ≠ 1) : diag3 ω ω⁻¹ ≠ 1 := by
  intro h1
  have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp [diag3] at h2
  exact h h2

theorem diag3_pow_ne {ω : Kˣ} (h : ω ≠ 1) (n : ℕ) : diag3 ω ω⁻¹ ^ n ≠ diag3 1 ω := by
  intro h1
  have h2 : ((diag3 ω ω⁻¹ ^ n : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 2 2 =
      ((diag3 1 ω : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    rw [h1]
  have hω : (ω : K) ≠ 0 := ω.ne_zero
  rw [coe_diag3_pow] at h2
  simp [diag3, hω] at h2
  exact h h2

end V1C

open V1C

theorem a319SL3Facts_holds : A319SL3Facts := by
  refine ⟨fun K _ _ h4 => ?_, fun K _ _ => ?_, fun K _ _ h3 => ?_⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (specialLinearGroupEquivStatedSL 3 K)).1
      (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (by norm_num) h4)
  · rw [← Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 K)).toEquiv]
    exact CFSG.DesarguesianPlanes.card_center_SL3_le
  · classical
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card (G := Kˣ) 3 (by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
      exact h3)
    have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
    have hω1 : ω ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hω
      omega
    set e := specialLinearGroupEquivStatedSL 3 K
    refine A3Facts.two_le_pRank_of_gens (x := e (diag3 ω ω⁻¹)) (y := e (diag3 1 ω)) ?_ ?_
      ((diag3_commute _ _ _ _).map e) ?_ fun n h => diag3_pow_ne hω1 n (e.injective ?_)
    · rw [← map_pow, diag3_pow_three hω3, map_one]
    · rw [← map_pow, diag3_one_pow_three hω3, map_one]
    · rw [Ne, map_eq_one_iff e e.injective]
      exact diag3_ne_one hω1
    · rw [map_pow, h]

end CFSG.Quasithin.Vol2.Ch10
