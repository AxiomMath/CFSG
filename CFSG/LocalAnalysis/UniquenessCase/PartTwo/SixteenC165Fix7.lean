module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

private theorem exists_vecMulVec_of_det_eq_zero {K : Type} [Field K]
    {Z : Matrix (Fin 2) (Fin 2) K} (hZ : Z ≠ 0) (hd : Z.det = 0) :
    ∃ u v : Fin 2 → K, u ≠ 0 ∧ v ≠ 0 ∧ Z = Matrix.vecMulVec u v := by
  rw [Matrix.det_fin_two] at hd
  by_cases h00 : Z 0 0 = 0
  · by_cases h01 : Z 0 1 = 0
    · have h1 : Z 1 0 ≠ 0 ∨ Z 1 1 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hZ
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, hcon.1, hcon.2]
      refine ⟨![0, 1], ![Z 1 0, Z 1 1], ?_, ?_, ?_⟩
      · intro h
        have := congrFun h 1
        simp at this
      · intro h
        have h10 := congrFun h 0
        have h11 := congrFun h 1
        simp at h10 h11
        rcases h1 with h | h
        · exact h h10
        · exact h h11
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h01]
    · have h10 : Z 1 0 = 0 := by
        rw [h00, zero_mul, zero_sub, neg_eq_zero] at hd
        exact (mul_eq_zero.mp hd).resolve_left h01
      refine ⟨![1, Z 1 1 / Z 0 1], ![0, Z 0 1], ?_, ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · intro h
        have := congrFun h 1
        simp at this
        exact h01 this
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h10]
        field_simp
  · refine ⟨![1, Z 1 0 / Z 0 0], ![Z 0 0, Z 0 1], ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · intro h
      have := congrFun h 0
      simp at this
      exact h00 this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply]
      · field_simp
      · field_simp
        linear_combination hd

private theorem exists_sl2_mulVec_single_zero {K : Type} [Field K]
    {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 (1 : K) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      exact hv (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![v 0, -(v 1)⁻¹; v 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem diag2_pow_seven {K : Type} [Field K] {s : K} (hs : s ≠ 0) (hs7 : s ^ 7 = 1) :
    (Matrix.SpecialLinearGroup.diag2 s hs) ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    Matrix.SpecialLinearGroup.diag2_coe, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.pow_apply, hs7, inv_pow]

private theorem diag2_ne_one {K : Type} [Field K] {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    Matrix.SpecialLinearGroup.diag2 s hs ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have hs_eq : s = 1 := by
    simpa [Matrix.SpecialLinearGroup.diag2_coe'] using h00
  exact hs1 hs_eq

theorem exists_sl2_pair_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X ≠ 0) :
    ∃ p : SL(2, K) × SL(2, K), p ≠ 1 ∧ p ^ 7 = 1 ∧
      (p.1 : Matrix (Fin 2) (Fin 2) K) * X * (p.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by simpa [Nat.card_eq_fintype_card] using hK
  have hs : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
    have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
      have h2 : ({0, 1} : Finset K).card ≤ 2 := by
        calc ({0, 1} : Finset K).card ≤ ({1} : Finset K).card + 1 :=
              Finset.card_insert_le 0 {1}
          _ = 2 := by simp
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨s, -, hs'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs'
    exact ⟨s, hs'.1, hs'.2⟩
  obtain ⟨s, hs0, hs1⟩ := hs
  have hs7 : s ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one s hs0
    simpa [hcard] using this
  have hsi7 : (s⁻¹) ^ 7 = 1 := by rw [inv_pow, hs7, inv_one]
  let d : SL(2, K) := Matrix.SpecialLinearGroup.diag2 s hs0
  have hd7 : d ^ 7 = 1 := diag2_pow_seven hs0 hs7
  have hd_ne : d ≠ 1 := diag2_ne_one hs0 hs1
  by_cases hdet : X.det = 0
  · obtain ⟨u, v, hu, hv, hXuv⟩ := exists_vecMulVec_of_det_eq_zero hX hdet
    obtain ⟨g, hg⟩ := exists_sl2_mulVec_single_zero hu
    obtain ⟨h, hh⟩ := exists_sl2_mulVec_single_zero hv
    let d' : SL(2, K) := Matrix.SpecialLinearGroup.diag2 s⁻¹ (inv_ne_zero hs0)
    have hd'7 : d' ^ 7 = 1 := diag2_pow_seven (inv_ne_zero hs0) hsi7
    let b : SL(2, K) := g * d * g⁻¹
    let a : SL(2, K) := h * d' * h⁻¹
    have hb7 : b ^ 7 = 1 := by
      rw [show b = g * d * g⁻¹ from rfl]
      simp [hd7]
    have ha7 : a ^ 7 = 1 := by
      rw [show a = h * d' * h⁻¹ from rfl]
      simp [hd'7]
    have hb_ne : b ≠ 1 := by
      intro hb1
      apply hd_ne
      have hconj : g⁻¹ * b * g = d := by
        rw [show b = g * d * g⁻¹ from rfl]
        group
      rw [← hconj, hb1]
      group
    have hbg : (b : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) =
        (g : Matrix (Fin 2) (Fin 2) K) * (d : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, show b * g = g * d by
        rw [show b = g * d * g⁻¹ from rfl]; group,
        Matrix.SpecialLinearGroup.coe_mul]
    have hbu : (b : Matrix (Fin 2) (Fin 2) K) *ᵥ u = s • u := by
      rw [← hg, Matrix.mulVec_mulVec, hbg, ← Matrix.mulVec_mulVec]
      have hde1 : (d : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 (1 : K) =
          s • Pi.single 0 (1 : K) := by
        simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using
          Matrix.SpecialLinearGroup.diag2_smul_single_i₁ (a := s) hs0
      rw [hde1, Matrix.mulVec_smul, hg]
    have hah : (a : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) =
        (h : Matrix (Fin 2) (Fin 2) K) * (d' : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, show a * h = h * d' by
        rw [show a = h * d' * h⁻¹ from rfl]; group,
        Matrix.SpecialLinearGroup.coe_mul]
    have hav : (a : Matrix (Fin 2) (Fin 2) K) *ᵥ v = s⁻¹ • v := by
      rw [← hh, Matrix.mulVec_mulVec, hah, ← Matrix.mulVec_mulVec]
      have hd'e1 : (d' : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 (1 : K) =
          s⁻¹ • Pi.single 0 (1 : K) := by
        simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using
          Matrix.SpecialLinearGroup.diag2_smul_single_i₁ (a := s⁻¹) (inv_ne_zero hs0)
      rw [hd'e1, Matrix.mulVec_smul, hh]
    refine ⟨(b, a), ?_, ?_, ?_⟩
    · intro hp
      exact hb_ne (Prod.ext_iff.mp hp).1
    · apply Prod.ext
      · exact hb7
      · exact ha7
    · rw [hXuv, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hbu, hav,
        Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  · have hXdet : IsUnit X.det := isUnit_iff_ne_zero.mpr hdet
    have hXmul : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXdet
    have hXmul' : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXdet
    let D : Matrix (Fin 2) (Fin 2) K := (d⁻¹ : SL(2, K)).1
    have hDdet : D.det = 1 := by
      dsimp [D]
      exact Matrix.SpecialLinearGroup.det_coe (d⁻¹)
    let Y : Matrix (Fin 2) (Fin 2) K := X⁻¹ * D * X
    have hYdet : Y.det = 1 := by
      dsimp [Y]
      rw [Matrix.det_mul, Matrix.det_mul, hDdet, mul_one,
        Matrix.det_nonsing_inv_mul_det X hXdet]
    let u : (Matrix (Fin 2) (Fin 2) K)ˣ := ⟨X, X⁻¹, hXmul, hXmul'⟩
    have hu : (u : Matrix (Fin 2) (Fin 2) K) = X := rfl
    have hu' : ((u⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) =
        X⁻¹ := rfl
    have hD7 : D ^ 7 = 1 := by
      have hd7' : (d⁻¹ : SL(2, K)) ^ 7 = 1 := by rw [inv_pow, hd7, inv_one]
      have h := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K)) hd7'
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
      simpa [D] using h
    have hY7 : Y ^ 7 = 1 := by
      have hconj := Units.conj_pow' u D 7
      rw [hu, hu'] at hconj
      rw [hD7, mul_one, hXmul'] at hconj
      dsimp [Y]
      exact hconj
    let a : SL(2, K) := ⟨Yᵀ, by rw [Matrix.det_transpose]; exact hYdet⟩
    have ha_coe : (a : Matrix (Fin 2) (Fin 2) K) = Yᵀ := rfl
    have ha7 : a ^ 7 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ha_coe]
      rw [← Matrix.transpose_pow, hY7, Matrix.transpose_one]
    refine ⟨(d, a), ?_, ?_, ?_⟩
    · intro hp
      exact hd_ne (Prod.ext_iff.mp hp).1
    · apply Prod.ext
      · exact hd7
      · exact ha7
    · rw [ha_coe, Matrix.transpose_transpose]
      have hXY : X * Y = D * X := by
        calc X * Y = X * (X⁻¹ * D * X) := by rw [show Y = X⁻¹ * D * X from rfl]
          _ = (X * X⁻¹) * (D * X) := by simp only [Matrix.mul_assoc]
          _ = D * X := by rw [hXmul, Matrix.one_mul]
      calc (d : Matrix (Fin 2) (Fin 2) K) * X * Y
          = (d : Matrix (Fin 2) (Fin 2) K) * (X * Y) := by rw [Matrix.mul_assoc]
        _ = (d : Matrix (Fin 2) (Fin 2) K) * (D * X) := by rw [hXY]
        _ = ((d : Matrix (Fin 2) (Fin 2) K) * D) * X := by rw [← Matrix.mul_assoc]
        _ = X := by
              have hdD : (d : Matrix (Fin 2) (Fin 2) K) * D = 1 := by
                rw [show D = (d⁻¹ : SL(2, K)).1 from rfl,
                  ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                  Matrix.SpecialLinearGroup.coe_one]
              rw [hdD, Matrix.one_mul]

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem exists_orderOf_eq_seven_of_ne_one (hK : Nat.card S.K = 8) {w : W} (hw : w ≠ 1) :
    ∃ g ∈ S.omega0, orderOf g = 7 ∧ g w = w := by
  let X : Matrix (Fin 2) (Fin 2) S.K := toMat (S.vec w)
  have hX : X ≠ 0 := by
    intro h0
    apply hw
    apply S.vec_injective
    rw [S.vec_one]
    have h := congrArg ofMat h0
    rw [show X = toMat (S.vec w) from rfl] at h
    rw [ofMat_toMat] at h
    have h0' : ofMat (0 : Matrix (Fin 2) (Fin 2) S.K) = 0 := by
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [ofMat]
    rwa [h0'] at h
  obtain ⟨p, hp_ne, hp7, hpX⟩ := exists_sl2_pair_fix (K := S.K) hK hX
  refine ⟨S.jHom p, ?_, ?_, ?_⟩
  · exact MonoidHom.mem_range.mpr ⟨p, rfl⟩
  · have hpow : (S.jHom p) ^ 7 = 1 := by
      rw [← map_pow, hp7, map_one]
    have hne : S.jHom p ≠ 1 := by
      intro h
      apply hp_ne
      apply S.jHom_injective
      rw [h, map_one]
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hpow hne
  · apply S.vec_injective
    rw [S.vec_jHom]
    have hpX' : (p.1 : Matrix (Fin 2) (Fin 2) S.K) * toMat (S.vec w) *
        (p.2 : Matrix (Fin 2) (Fin 2) S.K)ᵀ = toMat (S.vec w) := by
      simpa [X] using hpX
    rw [hpX', ofMat_toMat]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
