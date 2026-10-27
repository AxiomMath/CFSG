module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSLAut
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSym2
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj conjAut fieldAut dualAut
  conjAut_proj coe_slConjugation dualAut_proj proj_eq_one_iff mem_scalars)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (sym2Form)

private def D3 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 0, 0; 0, 1, 0; 0, 0, 2]

private def S3 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private def g1 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![2, 1, 2; 2, 2, 2; 0, 2, 2]

private def g1inv : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 2, 1; 2, 1, 0; 1, 2, 2]

private def g2 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 0, 1; 1, 1, 2; 2, 0, 2]

private def g2inv : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![2, 0, 2; 2, 1, 1; 1, 0, 0]

private def a1 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 2, 1; 0, 1, 0; 0, 1, 1]

private def a1inv : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 2, 2; 0, 1, 0; 0, 2, 1]

private def a2 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![2, 0, 2; 2, 1, 1; 0, 0, 2]

private def a2inv : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![2, 0, 1; 2, 1, 2; 0, 0, 2]

private def Ymat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 2, 1; 0, 1, 2; 2, 2, 2]

private def ymat : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 0, 1; 1, 0, 0; 1, 1, 0]

private def ymatinv : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 1, 0; 0, 2, 1; 1, 0, 0]

private lemma D3_sq : D3 * D3 = 1 := by decide

private lemma S3_sq : S3 * S3 = 1 := by decide

private lemma g1_det : g1.det = 1 := by decide

private lemma g2_det : g2.det = 1 := by decide

private lemma g1inv_det : g1inv.det = 1 := by decide

private lemma g2inv_det : g2inv.det = 1 := by decide

private lemma a1_det : a1.det = 1 := by decide

private lemma a2_det : a2.det = 1 := by decide

private lemma a1inv_det : a1inv.det = 1 := by decide

private lemma a2inv_det : a2inv.det = 1 := by decide

private lemma Ymat_det : Ymat.det = 1 := by decide

private lemma ymat_det : ymat.det = 1 := by decide

private lemma ymatinv_det : ymatinv.det = 1 := by decide

private lemma g1_mul_inv : g1 * g1inv = 1 := by decide

private lemma g2_mul_inv : g2 * g2inv = 1 := by decide

private lemma a1_mul_inv : a1 * a1inv = 1 := by decide

private lemma a2_mul_inv : a2 * a2inv = 1 := by decide

private lemma ymat_mul_inv : ymat * ymatinv = 1 := by decide

private lemma a1_eq : g1inv * (D3 * g1 * D3) = a1 := by decide

private lemma a2_eq : g2inv * (D3 * g2 * D3) = a2 := by decide

private lemma Y_eq : a1 * a2 * a1inv * a2inv = Ymat := by decide

private lemma Y_pow : Ymat ^ 13 = 1 := by decide

private lemma y_pow : ymat ^ 13 = 1 := by decide

private lemma S3_conj : S3 * ymatinvᵀ * S3 = ymatinv := by decide

variable {K : Type*} [Field K]

private def sl3 (f : ZMod 3 →+* K) (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (hM : M.det = 1) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨f.mapMatrix M, by rw [← RingHom.map_det, hM, map_one]⟩

private lemma sl3_mul (f : ZMod 3 →+* K) (M N : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hM : M.det = 1) (hN : N.det = 1) (hMN : (M * N).det = 1) :
    sl3 f (M * N) hMN = sl3 f M hM * sl3 f N hN := by
  apply Subtype.ext
  change f.mapMatrix (M * N) = f.mapMatrix M * f.mapMatrix N
  exact map_mul f.mapMatrix M N

private lemma sl3_one (f : ZMod 3 →+* K) (h : (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1) :
    sl3 f 1 h = 1 := by
  apply Subtype.ext
  change f.mapMatrix 1 = 1
  exact map_one f.mapMatrix

private lemma sl3_congr (f : ZMod 3 →+* K) {M N : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (hM : M.det = 1) (hN : N.det = 1) (h : M = N) :
    sl3 f M hM = sl3 f N hN := by
  cases h
  apply Subtype.ext
  rfl

private lemma sl3_inv (f : ZMod 3 →+* K) {M N : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (hM : M.det = 1) (hN : N.det = 1) (h : M * N = 1) :
    (sl3 f M hM)⁻¹ = sl3 f N hN := by
  have hMN : (M * N).det = 1 := by rw [h, Matrix.det_one]
  have h1 : (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := Matrix.det_one
  have hmul : sl3 f M hM * sl3 f N hN = 1 := by
    rw [← sl3_mul f M N hM hN hMN, sl3_congr f hMN h1 h, sl3_one f h1]
  exact inv_eq_of_mul_eq_one_right hmul

theorem isGenGood_conjAut_diag_three (hK : Nat.card K = 3) (D : GL (Fin 3) K)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, 1, -1]) :
    IsGenGood (conjAut 3 K D) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using hK
  have : CharP K 3 := charP_of_card_eq_prime hK'
  let f : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have h2 : (2 : K) = -1 := by
    have h0 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    have h : (2 : K) + 1 = 0 := by rw [← h0]; norm_num
    exact eq_neg_of_add_eq_zero_left h
  have hf2 : f 2 = -1 := by
    have h1 : f 2 = (2 : K) := map_ofNat f 2
    rw [h1, h2]
  have hmapD : f.mapMatrix D3 = diagonal ![1, 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D3, RingHom.mapMatrix_apply, hf2]
  have hDmat : (D : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix D3 := by
    rw [hD, hmapD]
  have hD2 : D * D = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hDmat, ← map_mul, D3_sq, map_one]
  have hDinv : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix D3 := by
    rw [inv_eq_of_mul_eq_one_right hD2, hDmat]
  have hG1inv : (sl3 f g1 g1_det)⁻¹ = sl3 f g1inv g1inv_det :=
    sl3_inv f g1_det g1inv_det g1_mul_inv
  have hG2inv : (sl3 f g2 g2_det)⁻¹ = sl3 f g2inv g2inv_det :=
    sl3_inv f g2_det g2inv_det g2_mul_inv
  have hA1inv : (sl3 f a1 a1_det)⁻¹ = sl3 f a1inv a1inv_det :=
    sl3_inv f a1_det a1inv_det a1_mul_inv
  have hA2inv : (sl3 f a2 a2_det)⁻¹ = sl3 f a2inv a2inv_det :=
    sl3_inv f a2_det a2inv_det a2_mul_inv
  have hA1 : (proj 3 K (sl3 f g1 g1_det))⁻¹ *
      conjAut 3 K D (proj 3 K (sl3 f g1 g1_det)) = proj 3 K (sl3 f a1 a1_det) := by
    rw [← map_inv, conjAut_proj, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, hG1inv, hDmat, hDinv]
    rw [show (sl3 f g1inv g1inv_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix g1inv from rfl,
      show (sl3 f g1 g1_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix g1 from rfl,
      show (sl3 f a1 a1_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a1 from rfl]
    conv_rhs => rw [← a1_eq]
    simp only [map_mul]
  have hA2 : (proj 3 K (sl3 f g2 g2_det))⁻¹ *
      conjAut 3 K D (proj 3 K (sl3 f g2 g2_det)) = proj 3 K (sl3 f a2 a2_det) := by
    rw [← map_inv, conjAut_proj, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, hG2inv, hDmat, hDinv]
    rw [show (sl3 f g2inv g2inv_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix g2inv from rfl,
      show (sl3 f g2 g2_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix g2 from rfl,
      show (sl3 f a2 a2_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a2 from rfl]
    conv_rhs => rw [← a2_eq]
    simp only [map_mul]
  let g : Fin 2 → projectiveSL 3 K :=
    ![(proj 3 K (sl3 f g1 g1_det)), proj 3 K (sl3 f g2 g2_det)]
  have hgen0 : (g 0)⁻¹ * conjAut 3 K D (g 0) = proj 3 K (sl3 f a1 a1_det) := by
    change (proj 3 K (sl3 f g1 g1_det))⁻¹ *
      conjAut 3 K D (proj 3 K (sl3 f g1 g1_det)) = proj 3 K (sl3 f a1 a1_det)
    exact hA1
  have hgen1 : (g 1)⁻¹ * conjAut 3 K D (g 1) = proj 3 K (sl3 f a2 a2_det) := by
    change (proj 3 K (sl3 f g2 g2_det))⁻¹ *
      conjAut 3 K D (proj 3 K (sl3 f g2 g2_det)) = proj 3 K (sl3 f a2 a2_det)
    exact hA2
  have h1 : proj 3 K (sl3 f a1 a1_det) ∈
      Subgroup.closure (Set.range fun i : Fin 2 => (g i)⁻¹ * conjAut 3 K D (g i)) := by
    simpa [hgen0] using Subgroup.subset_closure
      (Set.mem_range_self (f := fun i : Fin 2 => (g i)⁻¹ * conjAut 3 K D (g i)) (0 : Fin 2))
  have h2mem : proj 3 K (sl3 f a2 a2_det) ∈
      Subgroup.closure (Set.range fun i : Fin 2 => (g i)⁻¹ * conjAut 3 K D (g i)) := by
    simpa [hgen1] using Subgroup.subset_closure
      (Set.mem_range_self (f := fun i : Fin 2 => (g i)⁻¹ * conjAut 3 K D (g i)) (1 : Fin 2))
  have hYSL : sl3 f Ymat Ymat_det =
      sl3 f a1 a1_det * sl3 f a2 a2_det * (sl3 f a1 a1_det)⁻¹ *
        (sl3 f a2 a2_det)⁻¹ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hA1inv, hA2inv]
    rw [show (sl3 f a1inv a1inv_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a1inv from rfl,
      show (sl3 f a2inv a2inv_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a2inv from rfl,
      show (sl3 f a1 a1_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a1 from rfl,
      show (sl3 f a2 a2_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix a2 from rfl,
      show (sl3 f Ymat Ymat_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix Ymat from rfl]
    conv_lhs => rw [← Y_eq]
    simp only [map_mul]
  have hYeq : proj 3 K (sl3 f Ymat Ymat_det) =
      proj 3 K (sl3 f a1 a1_det) * proj 3 K (sl3 f a2 a2_det) *
        (proj 3 K (sl3 f a1 a1_det))⁻¹ * (proj 3 K (sl3 f a2 a2_det))⁻¹ := by
    rw [hYSL]
    simp only [map_mul, map_inv]
  have hYpow : (sl3 f Ymat Ymat_det) ^ 13 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [show (sl3 f Ymat Ymat_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix Ymat from rfl,
      ← map_pow, Y_pow, map_one]
  have hYne : proj 3 K (sl3 f Ymat Ymat_det) ≠ 1 := by
    intro h
    rw [proj_eq_one_iff] at h
    rw [mem_scalars] at h
    obtain ⟨c, -, hmat⟩ := h
    have h20 : (sl3 f Ymat Ymat_det : Matrix (Fin 3) (Fin 3) K) 2 0 = f 2 := by
      rw [show (sl3 f Ymat Ymat_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix Ymat from rfl,
        RingHom.mapMatrix_apply]
      simp [Ymat]
    have h20' : (sl3 f Ymat Ymat_det : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      rw [hmat]
      simp [Matrix.scalar_apply]
    rw [h20] at h20'
    rw [h20'] at hf2
    exact (neg_ne_zero.mpr one_ne_zero) hf2.symm
  have hy : orderOf (proj 3 K (sl3 f Ymat Ymat_det)) = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · rw [← map_pow, hYpow, map_one]
    · exact hYne
  have hmem : proj 3 K (sl3 f Ymat Ymat_det) ∈
      Subgroup.closure (Set.range fun i : Fin 2 => (g i)⁻¹ * conjAut 3 K D (g i)) := by
    rw [hYeq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2mem)
      (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2mem)
  have hd : 3 * (2 + 1) < dParam 13 := by
    have hord : dParam 13 = 12 := by
      show orderOf (2 : ZMod 13) = 12
      rw [orderOf_eq_iff (by norm_num : 0 < 12)]
      refine ⟨by decide, ?_⟩
      intro k hk _
      interval_cases k <;> decide
    rw [hord]
    norm_num
  refine ⟨2, g, proj 3 K (sl3 f Ymat Ymat_det), 13, by norm_num, hy, hmem, hd⟩

theorem isGenGood_conjAut_sym2Form_dualAut_three (hK : Nat.card K = 3) (S : GL (Fin 3) K)
    (hS : (S : Matrix (Fin 3) (Fin 3) K) = sym2Form K) :
    IsGenGood (conjAut 3 K S * fieldAut 3 K 1 * dualAut 3 K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using hK
  have : CharP K 3 := charP_of_card_eq_prime hK'
  let f : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hneg2 : (-2 : K) = 1 := by
    have h0 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    have h : (-2 : K) + 3 = 1 := by ring
    rw [h0, add_zero] at h
    exact h
  have hmapS : f.mapMatrix S3 = sym2Form K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S3, sym2Form, RingHom.mapMatrix_apply, hneg2]
  have hSmat : (S : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix S3 := hS.trans hmapS.symm
  have hS2 : S * S = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hSmat, ← map_mul, S3_sq, map_one]
  have hSinv : ((S⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix S3 := by
    rw [inv_eq_of_mul_eq_one_right hS2, hSmat]
  have hyinv : (sl3 f ymat ymat_det)⁻¹ = sl3 f ymatinv ymatinv_det :=
    sl3_inv f ymat_det ymatinv_det ymat_mul_inv
  have htrans : ((f.mapMatrix ymatinv)ᵀ) = f.mapMatrix (ymatinvᵀ) := by
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  have hpow : (sl3 f ymat ymat_det) ^ 13 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [show (sl3 f ymat ymat_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix ymat from rfl,
      ← map_pow, y_pow, map_one]
  have hne : proj 3 K (sl3 f ymat ymat_det) ≠ 1 := by
    intro h
    rw [proj_eq_one_iff] at h
    rw [mem_scalars] at h
    obtain ⟨c, -, hmat⟩ := h
    have h20 : (sl3 f ymat ymat_det : Matrix (Fin 3) (Fin 3) K) 2 0 = 1 := by
      rw [show (sl3 f ymat ymat_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix ymat from rfl,
        RingHom.mapMatrix_apply]
      simp [ymat]
    have h20' : (sl3 f ymat ymat_det : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      rw [hmat]
      simp [Matrix.scalar_apply]
    rw [h20] at h20'
    exact one_ne_zero h20'
  have hyord : orderOf (proj 3 K (sl3 f ymat ymat_det)) = 13 := by
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · rw [← map_pow, hpow, map_one]
    · exact hne
  have hact : (conjAut 3 K S * fieldAut 3 K 1 * dualAut 3 K)
      (proj 3 K (sl3 f ymat ymat_det)) = (proj 3 K (sl3 f ymat ymat_det))⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, map_one, MulAut.one_apply]
    rw [dualAut_proj, conjAut_proj, ← map_inv]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
    rw [hyinv, hSmat, hSinv]
    rw [show (sl3 f ymatinv ymatinv_det : Matrix (Fin 3) (Fin 3) K) = f.mapMatrix ymatinv
      from rfl]
    rw [htrans]
    conv_rhs => rw [← S3_conj]
    simp only [map_mul]
  have hd : 6 < dParam 13 := by
    have hord : dParam 13 = 12 := by
      show orderOf (2 : ZMod 13) = 12
      rw [orderOf_eq_iff (by norm_num : 0 < 12)]
      refine ⟨by decide, ?_⟩
      intro k hk _
      interval_cases k <;> decide
    rw [hord]
    norm_num
  exact isGenGood_of_inv (S := projectiveSL 3 K) (r := 13) (by norm_num) hyord hact hd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
