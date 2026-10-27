module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGH
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4B
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.Vol2.Ch11.SecS
  CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat spLine spHyp gmapSp spJ psiSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

namespace C11P9B

variable {K : Type} [Field K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem col_of_mem_spLine {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : M *ᵥ Pi.single (.inl 0) 1 ∈ spLine K) :
    M (.inl 1) (.inl 0) = 0 ∧ M (.inr 0) (.inl 0) = 0 ∧ M (.inr 1) (.inl 0) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [mulVec_e0_apply] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem shape_of_conjT (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) {τ : MulAut W} {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w))
    (horth : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T x) (T y) = 0)
    (hU : τ ∈ stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hM : ∀ v, M *ᵥ v = conjT T g v)
    (hM0 : M (.inl 0) (.inl 0) ≠ 0) :
    M (.inl 1) (.inl 0) = 0 ∧ M (.inr 1) (.inl 0) = 0 ∧ M (.inr 0) (.inl 1) = 0 ∧
      M (.inr 0) (.inr 1) = 0 := by
  have he₀ : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ spLine K :=
    ⟨by simp, by simp, by simp⟩
  obtain ⟨c1, c2, c3⟩ := col_of_mem_spLine (M := M)
    (by rw [hM]; exact conjT_mem_spLine hf g hTf hU he₀)
  have hTe : conjT T g (Pi.single (.inl 0) 1) = M (.inl 0) (.inl 0) • Pi.single (.inl 0) 1 := by
    rw [← hM]
    funext a
    rw [mulVec_e0_apply]
    rcases a with i | i <;> fin_cases i <;> simp [c1, c2, c3]
  have hrow : ∀ b : Fin 2 ⊕ Fin 2, (Pi.single b 1 : Fin 2 ⊕ Fin 2 → K) ∈ spHyp K →
      M (.inr 0) b = 0 := by
    intro b hb
    have h1 := mem_spHyp_of_orth (fun x y h => conjT_orth horth g h) hM0 hTe hb
    rw [← hM] at h1
    have h2 : (M *ᵥ Pi.single b 1) (.inr 0) = M (.inr 0) b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← h2]
    exact h1
  exact ⟨c1, c3, hrow _ (by simp [CFSG.Quasithin.Vol2.KGNat.mem_spHyp]),
    hrow _ (by simp [CFSG.Quasithin.Vol2.KGNat.mem_spHyp])⟩

theorem shape_of_mem_Q0 {X : StatedSp 2 K} (hX : X ∈ Q2 K 0) :
    mat 2 K X (.inl 1) (.inl 0) = 0 ∧ mat 2 K X (.inr 1) (.inl 0) = 0 ∧
      mat 2 K X (.inr 0) (.inl 1) = 0 ∧ mat 2 K X (.inr 0) (.inr 1) = 0 ∧
        mat 2 K X (.inr 0) (.inl 0) = 0 :=
  ⟨spMat_col_zero_of_mem_Q2_zero hX _ (by simp), spMat_col_zero_of_mem_Q2_zero hX _ (by simp),
    spMat_inr_zero_of_mem_Q2_zero hX (by simp), spMat_inr_zero_of_mem_Q2_zero hX (by simp),
    spMat_col_zero_of_mem_Q2_zero hX _ (by simp)⟩

theorem inner_of_linear_sp [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {τ : MulAut W}
    {T T' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w)) (hT'f : ∀ w, T' (f w) = f (τ⁻¹ w))
    (hT : ∀ (c : K) x, T (c • x) = c • T x) (hT' : ∀ (c : K) x, T' (c • x) = c • T' x)
    (horth : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T x) (T y) = 0)
    (horth' : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T' x) (T' y) = 0)
    (hU : τ ∈ stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))
    (hτN : ∀ X ∈ perfectCore (Q2 K 0), ∃ X' ∈ perfectCore (Q2 K 0),
      psiSp π g X' = τ * psiSp π g X * τ⁻¹) :
    ∃ γ ∈ (perfectCore (Q2 K 0)).map (psiSp π g),
      ∀ x ∈ (perfectCore (Q2 K 0)).map (psiSp π g),
        τ * x * τ⁻¹ * (γ * x * γ⁻¹)⁻¹ ∈ (pCoreOf 2 (perfectCore (Q2 K 0))).map (psiSp π g) := by
  obtain ⟨Mg, hMg⟩ := exists_mat_conjT hT g
  obtain ⟨Mg', hMg'⟩ := exists_mat_conjT hT' g
  have hTT' : ∀ x, T (T' x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT'f, hTf, MulAut.apply_inv_self]
  have hMM : Mg * Mg' = 1 := matrix_eq_of_mulVec_sp fun u => by
    rw [← Matrix.mulVec_mulVec, hMg', hMg, conjT_conjT hTT', Matrix.one_mulVec]
  have he₀ : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ spLine K :=
    ⟨by simp, by simp, by simp⟩
  obtain ⟨-, c20', -⟩ := col_of_mem_spLine (M := Mg')
    (by rw [hMg']; exact conjT_mem_spLine hf g hT'f (Subgroup.inv_mem _ hU) he₀)
  obtain ⟨c10', -, c30'⟩ := col_of_mem_spLine (M := Mg')
    (by rw [hMg']; exact conjT_mem_spLine hf g hT'f (Subgroup.inv_mem _ hU) he₀)
  have h00 : Mg (.inl 0) (.inl 0) * Mg' (.inl 0) (.inl 0) = 1 := by
    have := congrFun (congrFun hMM (.inl 0)) (.inl 0)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, c10', c20', c30']
      using this
  obtain ⟨m1, m2, m3, m4⟩ := shape_of_conjT hf g hTf horth hU hMg (left_ne_zero_of_mul_eq_one h00)
  obtain ⟨m1', m2', m3', m4'⟩ := shape_of_conjT hf g hT'f horth' (Subgroup.inv_mem _ hU) hMg'
    (right_ne_zero_of_mul_eq_one h00)
  set N := blkIdx (sigma2 0) Mg with hN
  set N' := blkIdx (sigma2 0) Mg' with hN'
  have hNN : N * N' = 1 := by
    rw [hN, hN', ← blkIdx_mul_of_shape m1 m2 m3' m4', hMM, blkIdx_one (sigma2_injective 0)]
  have hdet : N.det * N'.det = 1 := by rw [← Matrix.det_mul, hNN, Matrix.det_one]
  have hd0 : N.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' N.det
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hd0 hs
  let A : SL(2, K) := ⟨s⁻¹ • N, by
    rw [Matrix.det_smul, Fintype.card_fin, hs]
    field_simp⟩
  obtain ⟨⟨B₀, hB₀⟩, hlev0⟩ := blkN_surjective hK4 0 A
  have hB₀Q : B₀ ∈ Q2 K 0 := perfectCore_le _ hB₀
  have hblkB₀ : blkIdx (sigma2 0) (mat 2 K B₀) = s⁻¹ • N := by
    have h := congrArg Subtype.val hlev0
    rw [blkN_coe] at h
    exact h
  have hinv : blkIdx (sigma2 0) (mat 2 K B₀⁻¹) = s • N' := by
    have h1 : (s⁻¹ • N) * blkIdx (sigma2 0) (mat 2 K B₀⁻¹) = 1 := by
      rw [← hblkB₀]
      exact blkQ_mul_inv 0 hB₀Q
    have h2 : (s • N') * (s⁻¹ • N) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs0, one_smul,
        mul_eq_one_comm.mp hNN]
    calc blkIdx (sigma2 0) (mat 2 K B₀⁻¹)
        = ((s • N') * (s⁻¹ • N)) * blkIdx (sigma2 0) (mat 2 K B₀⁻¹) := by rw [h2, Matrix.one_mul]
      _ = (s • N') * ((s⁻¹ • N) * blkIdx (sigma2 0) (mat 2 K B₀⁻¹)) := by rw [Matrix.mul_assoc]
      _ = s • N' := by rw [h1, Matrix.mul_one]
  refine ⟨psiSp π g B₀, ⟨B₀, hB₀, rfl⟩, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨X', hX', hXX'⟩ := hτN X hX
  have hXQ : X ∈ Q2 K 0 := perfectCore_le _ hX
  have hX'Q : X' ∈ Q2 K 0 := perfectCore_le _ hX'
  obtain ⟨x1, x2, x3, x4, x5⟩ := shape_of_mem_Q0 hXQ
  obtain ⟨b1, b2, -, -, -⟩ := shape_of_mem_Q0 hB₀Q
  obtain ⟨-, -, b3', b4', -⟩ := shape_of_mem_Q0 ((Q2 K 0).inv_mem hB₀Q)
  have hmat : mat 2 K X' = Mg * mat 2 K X * Mg' := matrix_eq_of_mulVec_sp fun v => by
    rw [mat_conj_apply hf g hTf hT'f hXX', ← hMg', ← hMg, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : (Mg * mat 2 K X) (.inl 1) (.inl 0) = 0 := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, m1, x1, x2, x5]
  have hc2 : (Mg * mat 2 K X) (.inr 1) (.inl 0) = 0 := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, m2, x1, x2, x5]
  have hd1 : (mat 2 K B₀ * mat 2 K X) (.inl 1) (.inl 0) = 0 := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, b1, x1, x2, x5]
  have hd2 : (mat 2 K B₀ * mat 2 K X) (.inr 1) (.inl 0) = 0 := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, b2, x1, x2, x5]
  have hY : B₀ * X * B₀⁻¹ ∈ perfectCore (Q2 K 0) :=
    (perfectCore (Q2 K 0)).mul_mem ((perfectCore (Q2 K 0)).mul_mem hB₀ hX)
      ((perfectCore (Q2 K 0)).inv_mem hB₀)
  have hYQ : B₀ * X * B₀⁻¹ ∈ Q2 K 0 := perfectCore_le _ hY
  have hEq : blkIdx (sigma2 0) (mat 2 K X') = blkIdx (sigma2 0) (mat 2 K (B₀ * X * B₀⁻¹)) := by
    rw [hmat, blkIdx_mul_of_shape hc1 hc2 m3' m4', blkIdx_mul_of_shape m1 m2 x3 x4, map_mul,
      map_mul, blkIdx_mul_of_shape hd1 hd2 b3' b4', blkIdx_mul_of_shape b1 b2 x3 x4, hblkB₀,
      hinv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0,
      one_smul]
  have hC : X' * (B₀ * X * B₀⁻¹)⁻¹ ∈ perfectCore (Q2 K 0) :=
    (perfectCore (Q2 K 0)).mul_mem hX' ((perfectCore (Q2 K 0)).inv_mem hY)
  obtain ⟨y1, y2, -, -, -⟩ := shape_of_mem_Q0 hX'Q
  obtain ⟨-, -, y3, y4, -⟩ := shape_of_mem_Q0 ((Q2 K 0).inv_mem hYQ)
  have hCO : X' * (B₀ * X * B₀⁻¹)⁻¹ ∈ pCoreOf 2 (perfectCore (Q2 K 0)) := by
    rw [mem_pCoreOf_N_iff hK4 0 hC]
    show blkIdx (sigma2 0) (mat 2 K (X' * (B₀ * X * B₀⁻¹)⁻¹)) = 1
    rw [map_mul, blkIdx_mul_of_shape y1 y2 y3 y4, hEq]
    exact blkQ_mul_inv 0 hYQ
  refine ⟨X' * (B₀ * X * B₀⁻¹)⁻¹, hCO, ?_⟩
  rw [map_mul, map_inv, hXX', map_mul, map_mul, map_inv]

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
