module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.LinearAlgebra.AnisotropicBinaryPlane
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (coe_quadMinus)
open CFSG.Blueprint (LieModel)
open QuadraticAlgebra
open scoped Matrix
open scoped commutatorElement

private theorem k328r8p_ofNat_mod2 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : F) = ((n % 2 : ℕ) : F) := by
  rw [show (OfNat.ofNat n : F) = ((n : ℕ) : F) from rfl]
  exact (CharP.natCast_eq_natCast (R := F) (p := 2) (a := n) (b := n % 2)).mpr
    (Nat.mod_mod n 2).symm

private theorem k328r8p_charP_two (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : CharP F 2 := by
  have : Finite F := Finite.of_fintype F
  obtain ⟨p, hp, n, hp', hcard⟩ := FiniteField.card' (K := F)
  have : Fact p.Prime := ⟨hp'⟩
  have h1 : p ^ (n : ℕ) = 2 ^ 3 := by rw [← hcard, hF]; norm_num
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 3 := by rw [← h1]; exact dvd_pow_self p n.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 (hp'.dvd_of_dvd_pow hdvd)
  subst hp2; exact hp

private theorem k328r8p_aniso (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    ∀ x y : F, x ^ 2 + 1 * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  have : CharP F 2 := k328r8p_charP_two F hF
  intro x y h
  by_cases hy : y = 0
  · subst hy
    have hx2 : x ^ 2 = 0 := by linear_combination h
    exact ⟨sq_eq_zero_iff.mp hx2, rfl⟩
  · exfalso
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    set t := x * y⁻¹ with ht
    have hx_eq : x = t * y := by rw [ht, mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hxy : t ^ 2 + t + 1 = 0 := by
      have hmul : y ^ 2 * (t ^ 2 + t + 1) = 0 := by
        rw [← h, hx_eq]; ring
      exact (mul_eq_zero.mp hmul).resolve_left hy2
    have ht3 : t ^ 3 = 1 := by
      have h0 : (t + 1) * (t ^ 2 + t + 1) = 0 := by rw [hxy, mul_zero]
      have h1 : t ^ 3 + 1 = 0 := by
        linear_combination h0 - (t ^ 2 + t) * CharTwo.two_eq_zero (R := F)
      have h2 : t ^ 3 = -1 := eq_neg_of_add_eq_zero_left h1
      rwa [CharTwo.neg_eq] at h2
    have hx : x ≠ 0 := by
      intro hx0
      rw [hx0] at h
      simp at h
      exact hy h
    have htne : t ≠ 0 := by rw [ht]; exact mul_ne_zero hx (inv_ne_zero hy)
    have ht7 : t ^ 7 = 1 := by
      have hq := FiniteField.pow_card_sub_one_eq_one (K := F) t htne
      have hcard : Fintype.card F - 1 = 7 := by rw [hF]
      rwa [hcard] at hq
    have h1 : orderOf t ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr ht3) (orderOf_dvd_iff_pow_eq_one.mpr ht7)
      simpa using this
    have ht1 : t = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    rw [ht1] at hxy
    exact one_ne_zero (by linear_combination hxy - CharTwo.two_eq_zero (R := F))

private theorem k328r8p_fact (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  refine ⟨fun r h => ?_⟩
  have h0 : r ^ 2 + 1 * r * 1 + 1 ^ 2 = 0 := by
    rw [h]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc (1 + 1 * r) + 1 * r * 1 + 1 ^ 2 = (2 : F) * (1 + r) := by ring
      _ = 0 := by rw [h2, zero_mul]
  exact one_ne_zero (k328r8p_aniso F hF r 1 h0).2

private theorem k328r8p_card_L (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : Nat.card (QuadraticAlgebra F 1 1) = 64 := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    CFSG.LinearAlgebra.anisotropic_binary_plane_norm_field (K := F) (ε := 1) (k328r8p_aniso F hF)
  have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  have := (hlast 3 (by norm_num) (by rw [hF8]; norm_num)).1
  simpa using this

private theorem k328r8p_star_pow (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z : QuadraticAlgebra F 1 1) : star z = z ^ 8 := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    CFSG.LinearAlgebra.anisotropic_binary_plane_norm_field (K := F) (ε := 1) (k328r8p_aniso F hF)
  have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  exact (hlast 3 (by norm_num) (by rw [hF8]; norm_num)).2 z

private theorem k328r8p_re_sum (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} (s : Finset ι) (f : ι → QuadraticAlgebra F 1 1) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, QuadraticAlgebra.re_add, ih]

private theorem k328r8p_im_sum (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} (s : Finset ι) (f : ι → QuadraticAlgebra F 1 1) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, QuadraticAlgebra.im_add, ih]

private theorem k328r8p_map_re_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    (A * B).map QuadraticAlgebra.re =
      A.map QuadraticAlgebra.re * B.map QuadraticAlgebra.re +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [k328r8p_re_sum]
  simp only [QuadraticAlgebra.re_mul]
  rw [Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; ring

private theorem k328r8p_map_im_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    (A * B).map QuadraticAlgebra.im =
      A.map QuadraticAlgebra.re * B.map QuadraticAlgebra.im +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.re +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [k328r8p_im_sum]
  simp only [QuadraticAlgebra.im_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; ring

private def k328r8p_rhoMat (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) →*
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F where
  toFun A := Matrix.fromBlocks (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)
    (A.map QuadraticAlgebra.im) (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im)
  map_one' := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases h : i = j <;>
        simp [Matrix.one_apply, h, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
          QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_mul' A B := by
    rw [k328r8p_map_re_mul, k328r8p_map_im_mul, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

private def k328r8p_rho (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    GL (Fin 3) (QuadraticAlgebra F 1 1) →* GL (Fin 3 ⊕ Fin 3) F :=
  Units.map (k328r8p_rhoMat F)

private theorem k328r8p_rho_apply (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    ((k328r8p_rho F A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
          QuadraticAlgebra.re)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re +
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im) :=
  rfl

private def k328r8p_ofBlocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) :=
  Matrix.of fun i j => (⟨P i j, Q i j⟩ : QuadraticAlgebra F 1 1)

private theorem k328r8p_ofBlocks_re (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    (k328r8p_ofBlocks F P Q).map QuadraticAlgebra.re = P := by
  ext i j; rfl

private theorem k328r8p_ofBlocks_im (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    (k328r8p_ofBlocks F P Q).map QuadraticAlgebra.im = Q := by
  ext i j; rfl

private theorem k328r8p_rhoMat_injective (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Function.Injective (k328r8p_rhoMat F) := by
  intro A B h
  have h1 : A.map QuadraticAlgebra.re = B.map QuadraticAlgebra.re :=
    (Matrix.fromBlocks_inj.mp h).1
  have h2 : A.map QuadraticAlgebra.im = B.map QuadraticAlgebra.im :=
    (Matrix.fromBlocks_inj.mp h).2.1
  ext i j
  · simpa [Matrix.map_apply] using congrFun (congrFun h1 i) j
  · simpa [Matrix.map_apply] using congrFun (congrFun h2 i) j

private theorem k328r8p_eq_rho_of_commute (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (h : g * Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 * g) :
    g = k328r8p_rhoMat F (k328r8p_ofBlocks F g.toBlocks₁₁ g.toBlocks₁₂) := by
  have hg : g = Matrix.fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks g).symm
  rw [hg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, Matrix.one_mul, zero_add] at h
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp h
  rw [hg]
  change Matrix.fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ =
    Matrix.fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₁₂
      (g.toBlocks₁₁ + g.toBlocks₁₂)
  rw [← h11, ← h12]

private noncomputable def k328r8p_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : GL (Fin 3) (QuadraticAlgebra F 1 1) :=
  letI : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  Matrix.GeneralLinearGroup.scalar (Fin 3)
    (Units.mk0 (ω : QuadraticAlgebra F 1 1) (by
      intro h
      have h' : (1 : F) = 0 := by
        simpa using congrArg QuadraticAlgebra.im h
      exact one_ne_zero h'))

private theorem k328r8p_rho_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    ((k328r8p_rho F (k328r8p_omegaUnit F hF) : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  rw [k328r8p_rho_apply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k328r8p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, h, QuadraticAlgebra.re_omega]
  · rw [k328r8p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.one_apply, h, QuadraticAlgebra.im_omega]
  · rw [k328r8p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.one_apply, h, QuadraticAlgebra.im_omega]
  · rw [k328r8p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.one_apply, h, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

private theorem k328r8p_sp_iff_unitary_blocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    (Matrix.fromBlocks P Q Q (P + Q))ᵀ *
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 0 *
        Matrix.fromBlocks P Q Q (P + Q) =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 0 ↔
    (Matrix.fromBlocks (P + Q) Q Q P)ᵀ * Matrix.fromBlocks P Q Q (P + Q) = 1 := by
  have hT1 : (Matrix.fromBlocks P Q Q (P + Q))ᵀ =
      Matrix.fromBlocks Pᵀ Qᵀ Qᵀ (P + Q)ᵀ := Matrix.fromBlocks_transpose _ _ _ _
  have hT2 : (Matrix.fromBlocks (P + Q) Q Q P)ᵀ =
      Matrix.fromBlocks (P + Q)ᵀ Qᵀ Qᵀ Pᵀ := Matrix.fromBlocks_transpose _ _ _ _
  have hT3 : (P + Q)ᵀ = Pᵀ + Qᵀ := Matrix.transpose_add P Q
  rw [hT1, hT2, hT3]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
  rw [← Matrix.fromBlocks_one]
  rw [Matrix.fromBlocks_inj, Matrix.fromBlocks_inj]
  constructor <;> rintro ⟨h11, h12, h21, h22⟩ <;>
    exact ⟨h21, h22, h11, h12⟩

private theorem k328r8p_ofBlocks_self (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r8p_ofBlocks F (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im) = A := by
  ext i j <;> simp [k328r8p_ofBlocks, Matrix.map_apply]

private theorem k328r8p_map_star_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    A.map star = k328r8p_ofBlocks F (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im)
      (A.map QuadraticAlgebra.im) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  ext i j
  · simp [k328r8p_ofBlocks, Matrix.map_apply]
  · simp [k328r8p_ofBlocks, Matrix.map_apply, QuadraticAlgebra.im_star, CharTwo.neg_eq]

private theorem k328r8p_rhoMat_ofBlocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    k328r8p_rhoMat F (k328r8p_ofBlocks F P Q) = Matrix.fromBlocks P Q Q (P + Q) := by
  change Matrix.fromBlocks ((k328r8p_ofBlocks F P Q).map QuadraticAlgebra.re)
      ((k328r8p_ofBlocks F P Q).map QuadraticAlgebra.im)
      ((k328r8p_ofBlocks F P Q).map QuadraticAlgebra.im)
      ((k328r8p_ofBlocks F P Q).map QuadraticAlgebra.re +
        (k328r8p_ofBlocks F P Q).map QuadraticAlgebra.im) =
    Matrix.fromBlocks P Q Q (P + Q)
  rw [k328r8p_ofBlocks_re, k328r8p_ofBlocks_im]

private theorem k328r8p_rhoMat_transpose (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r8p_rhoMat F Aᵀ = (k328r8p_rhoMat F A)ᵀ := by
  change Matrix.fromBlocks (Aᵀ.map QuadraticAlgebra.re) (Aᵀ.map QuadraticAlgebra.im)
      (Aᵀ.map QuadraticAlgebra.im) (Aᵀ.map QuadraticAlgebra.re + Aᵀ.map QuadraticAlgebra.im) =
    (Matrix.fromBlocks (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)
      (A.map QuadraticAlgebra.im) (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im))ᵀ
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_add, Matrix.transpose_map]

private theorem k328r8p_mem_statedSp_iff (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r8p_rho F A ∈ StatedSp 3 F ↔
      ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) = 1 := by
  have : CharP F 2 := k328r8p_charP_two F hF
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  simp only [CharTwo.neg_eq]
  rw [k328r8p_rho_apply]
  rw [k328r8p_sp_iff_unitary_blocks]
  have h1 : Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.re + (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re) =
      k328r8p_rhoMat F ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star) := by
    rw [k328r8p_map_star_eq F hF, k328r8p_rhoMat_ofBlocks]
    congr 1
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h2 : Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.re)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re +
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im) =
      k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) := by
    rw [← k328r8p_rhoMat_ofBlocks, k328r8p_ofBlocks_self]
  have h3 : (k328r8p_rhoMat F ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        star))ᵀ =
      k328r8p_rhoMat F (((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)ᵀ) :=
    (k328r8p_rhoMat_transpose F
      ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)).symm
  rw [h1, h2, h3, ← map_mul]
  constructor
  · intro h
    exact k328r8p_rhoMat_injective F (by rw [map_one]; exact h)
  · intro h
    rw [h, map_one]

private def k328r8p_GU (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Subgroup (GL (Fin 3) (QuadraticAlgebra F 1 1)) :=
  Subgroup.comap (k328r8p_rho F) (StatedSp 3 F)

private abbrev k328r8p_SU (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] : Subgroup (GL (Fin 3) (QuadraticAlgebra F 1 1)) :=
  StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1)

private theorem k328r8p_statedSU_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    k328r8p_SU F =
      k328r8p_GU F ⊓ (Matrix.GeneralLinearGroup.det :
        GL (Fin 3) (QuadraticAlgebra F 1 1) →* (QuadraticAlgebra F 1 1)ˣ).ker := by
  have : CharP F 2 := k328r8p_charP_two F hF
  obtain ⟨hset, -, -⟩ := CFSG.LinearGroups.unitary_scalar_kernel (K := QuadraticAlgebra F 1 1)
    (p := 2) (f := 3) Nat.prime_two (by rw [k328r8p_card_L F hF]; norm_num) (n := 3)
    (by norm_num)
  have hmem : ∀ A : GL (Fin 3) (QuadraticAlgebra F 1 1),
      A ∈ k328r8p_SU F ↔
      (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).det = 1 ∧
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map (· ^ 8))ᵀ *
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) = 1 := by
    intro A
    rw [← SetLike.mem_coe, hset]
    rfl
  apply le_antisymm
  · intro A hA
    rw [hmem] at hA
    constructor
    · show k328r8p_rho F A ∈ StatedSp 3 F
      exact (k328r8p_mem_statedSp_iff F hF A).mpr (by
        rw [show (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star =
            (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map (· ^ 8) from by
          ext i j
          · exact congrArg QuadraticAlgebra.re (k328r8p_star_pow F hF (A i j))
          · exact congrArg QuadraticAlgebra.im (k328r8p_star_pow F hF (A i j))]
        exact hA.2)
    · show (Matrix.GeneralLinearGroup.det :
          GL (Fin 3) (QuadraticAlgebra F 1 1) →* (QuadraticAlgebra F 1 1)ˣ) A = 1
      rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]
      exact hA.1
  · intro A hA
    rw [hmem]
    constructor
    · simpa [Matrix.GeneralLinearGroup.val_det_apply, Units.ext_iff] using hA.2
    · have hsp : k328r8p_rho F A ∈ StatedSp 3 F := hA.1
      rw [← (k328r8p_mem_statedSp_iff F hF A).mp hsp]
      have hstar : (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star =
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map (· ^ 8) := by
        ext i j
        · exact congrArg QuadraticAlgebra.re (k328r8p_star_pow F hF (A i j))
        · exact congrArg QuadraticAlgebra.im (k328r8p_star_pow F hF (A i j))
      rw [hstar]

private theorem k328r8p_commutator_GU_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    ⁅k328r8p_GU F, k328r8p_GU F⁆ = k328r8p_SU F := by
  have : CharP F 2 := k328r8p_charP_two F hF
  apply le_antisymm
  · rw [k328r8p_statedSU_eq F hF]
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (k328r8p_GU F).mul_mem ((k328r8p_GU F).mul_mem
        ((k328r8p_GU F).mul_mem ha hb) ((k328r8p_GU F).inv_mem ha))
        ((k328r8p_GU F).inv_mem hb)
    · rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      simp [mul_assoc]
  · have : Finite (QuadraticAlgebra F 1 1) :=
      Nat.finite_of_card_ne_zero (by rw [k328r8p_card_L F hF]; norm_num)
    have hperf : commutator (k328r8p_SU F) = ⊤ := by
      have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
          (F := QuadraticAlgebra F 1 1) (p := 2) (f := 3)
          (by rw [k328r8p_card_L F hF]; norm_num) (n := 3) le_rfl (by norm_num)).1
      exact ((fun h => ⟨h.1.1, h.2.1⟩ : CFSG.IsQuasisimple
          (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1)) →
        CFSG.Open.IsQuasisimple (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1))) h).1
    have hSU : k328r8p_SU F ≤ k328r8p_GU F := by
      rw [k328r8p_statedSU_eq F hF]; exact inf_le_left
    rw [← commutator_self_of_perfect hperf]
    exact Subgroup.commutator_mono hSU hSU

private theorem k328r8p_omega_pow_three (F : Type) [Field F] [CharP F 2] :
    (ω : QuadraticAlgebra F 1 1) ^ 3 = 1 := by
  have h2 : (ω : QuadraticAlgebra F 1 1) ^ 2 = 1 + ω := by
    rw [QuadraticAlgebra.omega_pow_two_eq_add]; simp
  have h2L : (2 : QuadraticAlgebra F 1 1) = 0 := by
    apply QuadraticAlgebra.ext
    · exact CharTwo.two_eq_zero
    · rfl
  calc (ω : QuadraticAlgebra F 1 1) ^ 3 = ω * ω ^ 2 := by ring
    _ = ω * (1 + ω) := by rw [h2]
    _ = 1 := by
      rw [mul_add, mul_one, ← pow_two, h2]
      calc ω + (1 + ω) = (1 : QuadraticAlgebra F 1 1) + 2 * ω := by ring
        _ = 1 + 0 := by rw [h2L, zero_mul]
        _ = 1 := by rw [add_zero]

private theorem k328r8p_omega_ne_one (F : Type) [Field F] :
    (ω : QuadraticAlgebra F 1 1) ≠ 1 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_omega, QuadraticAlgebra.im_one] at him
  exact one_ne_zero (α := F) him

private theorem k328r8p_omega_ne_zero (F : Type) [Field F] :
    (ω : QuadraticAlgebra F 1 1) ≠ 0 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_omega, QuadraticAlgebra.im_zero] at him
  exact one_ne_zero (α := F) him

private theorem k328r8p_orderOf_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : orderOf (k328r8p_omegaUnit F hF) = 3 := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  have h3 : (ω : QuadraticAlgebra F 1 1) ^ 3 = 1 := k328r8p_omega_pow_three F
  have hne : (ω : QuadraticAlgebra F 1 1) ≠ 1 := k328r8p_omega_ne_one F
  have h0 : (ω : QuadraticAlgebra F 1 1) ≠ 0 := k328r8p_omega_ne_zero F
  have h3u : (Units.mk0 (ω : QuadraticAlgebra F 1 1) h0) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h3
  have hne1u : Units.mk0 (ω : QuadraticAlgebra F 1 1) h0 ≠ 1 := by
    intro h
    apply hne
    have := congrArg (fun u : (QuadraticAlgebra F 1 1)ˣ => (u : QuadraticAlgebra F 1 1)) h
    simpa using this
  have hω : orderOf (Units.mk0 (ω : QuadraticAlgebra F 1 1) h0) = 3 :=
    orderOf_eq_prime h3u hne1u
  have hEq : k328r8p_omegaUnit F hF =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (ω : QuadraticAlgebra F 1 1) h0) := by
    rw [k328r8p_omegaUnit]
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
      (QuadraticAlgebra F 1 1)ˣ →* GL (Fin 3) (QuadraticAlgebra F 1 1)) := by
    intro c c' hcc'
    have := congrArg (fun g : GL (Fin 3) (QuadraticAlgebra F 1 1) =>
      (g : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) hcc'
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] at this
    exact Units.ext this
  rw [hEq]
  exact (orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin 3)) hinj _).trans hω

private theorem k328r8p_omegaUnit_mem_SU (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    k328r8p_omegaUnit F hF ∈ k328r8p_SU F := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have hcard : Nat.card (QuadraticAlgebra F 1 1) = (2 ^ 3) ^ 2 := by
    rw [k328r8p_card_L F hF]; norm_num
  rw [show k328r8p_SU F = StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1) from rfl]
  rw [k328r8p_omegaUnit]
  rw [CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hcard (n := 3) (by norm_num)]
  refine ⟨?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact k328r8p_omega_pow_three F
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    rw [show (2 : ℕ) ^ 3 + 1 = 9 from by norm_num, show (9 : ℕ) = 3 * 3 from rfl, pow_mul,
      k328r8p_omega_pow_three F, one_pow]

private abbrev k328r8p_Ix := Fin 3 ⊕ Fin 3 ⊕ Fin 2

private def k328r8p_v8 (F : Type) [Field F] (a0 a1 a2 b0 b1 b2 c0 c1 : F) : k328r8p_Ix → F :=
  Sum.elim ![a0, a1, a2] (Sum.elim ![b0, b1, b2] ![c0, c1])

private def k328r8p_col (F : Type) [Field F] [Fintype F] [DecidableEq F] (b _c α : F) :
    k328r8p_Ix → (k328r8p_Ix → F) :=
  Sum.elim
    ![k328r8p_v8 F 1 0 0 1 0 0 0 0, k328r8p_v8 F 1 1 0 1 0 0 0 0,
      k328r8p_v8 F 0 0 0 0 0 0 1 0]
    (Sum.elim
      ![k328r8p_v8 F 1 1 0 0 1 0 0 0, k328r8p_v8 F 1 0 0 1 1 0 0 0,
        k328r8p_v8 F 0 0 0 0 0 0 α b⁻¹]
      ![k328r8p_v8 F 0 0 1 0 0 0 0 0, k328r8p_v8 F 0 0 0 0 0 1 0 0])

private def k328r8p_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    Matrix k328r8p_Ix k328r8p_Ix F :=
  Matrix.of fun r k => k328r8p_col F b c α k r

private def k328r8p_qrow (F : Type) [Field F] [Fintype F] [DecidableEq F] (b _c α : F) :
    k328r8p_Ix → (k328r8p_Ix → F) :=
  Sum.elim
    ![k328r8p_v8 F 0 1 0 1 1 0 0 0, k328r8p_v8 F 1 1 0 0 0 0 0 0,
      k328r8p_v8 F 0 0 0 0 0 0 1 0]
    (Sum.elim
      ![k328r8p_v8 F 1 1 0 1 1 0 0 0, k328r8p_v8 F 1 0 0 0 1 0 0 0,
        k328r8p_v8 F 0 0 0 0 0 0 0 1]
      ![k328r8p_v8 F 0 0 1 0 0 0 0 0, k328r8p_v8 F 0 0 (b * α) 0 0 b 0 0])

private def k328r8p_Qmat (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    Matrix k328r8p_Ix k328r8p_Ix F :=
  Matrix.of fun k r => k328r8p_qrow F b c α r k

private theorem k328r8p_Qmat_mul_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) :
    k328r8p_Qmat F b c α * k328r8p_Pmat F b c α = 1 := by
  have h2 : (2 : F) = 0 := by
    have := k328r8p_charP_two F hF
    exact_mod_cast CharP.cast_eq_zero F 2
  have hself : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, h2, zero_mul]
  have hbx : ∀ x : F, b * x * b⁻¹ = x := fun x => by
    rw [mul_assoc, mul_comm x b⁻¹, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  ext i j
  rw [Matrix.mul_apply]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [k328r8p_Qmat, k328r8p_qrow, k328r8p_Pmat, k328r8p_col, k328r8p_v8,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val, mul_inv_cancel₀ hb, hself, hbx]

private theorem k328r8p_Pmat_mul_Qmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) :
    k328r8p_Pmat F b c α * k328r8p_Qmat F b c α = 1 :=
  (mul_eq_one_comm).mp (k328r8p_Qmat_mul_Pmat F hF b c α hb)

private theorem k328r8p_Pmat_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (x : k328r8p_Ix → F) :
    k328r8p_Pmat F b c α *ᵥ x =
      k328r8p_v8 F
        (x (Sum.inl 0) + x (Sum.inr (Sum.inl 0)) + x (Sum.inl 1) + x (Sum.inr (Sum.inl 1)))
        (x (Sum.inr (Sum.inl 0)) + x (Sum.inl 1))
        (x (Sum.inr (Sum.inr 0)))
        (x (Sum.inl 0) + x (Sum.inl 1) + x (Sum.inr (Sum.inl 1)))
        (x (Sum.inr (Sum.inl 0)) + x (Sum.inr (Sum.inl 1)))
        (x (Sum.inr (Sum.inr 1)))
        (x (Sum.inl 2) + α * x (Sum.inr (Sum.inl 2)))
        (b⁻¹ * x (Sum.inr (Sum.inl 2))) := by
  funext r
  rw [Matrix.mulVec_apply_eq_sum]
  rcases r with i | i | i <;> fin_cases i <;>
    simp [k328r8p_Pmat, k328r8p_col, k328r8p_v8, Matrix.of_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr] <;>
    abel

private def k328r8p_N (F : Type) [Field F] (x : k328r8p_Ix → F) : F :=
  (x (Sum.inl 0)) ^ 2 + x (Sum.inl 0) * x (Sum.inr (Sum.inl 0)) + (x (Sum.inr (Sum.inl 0))) ^ 2 +
  (x (Sum.inl 1)) ^ 2 + x (Sum.inl 1) * x (Sum.inr (Sum.inl 1)) + (x (Sum.inr (Sum.inl 1))) ^ 2 +
  (x (Sum.inl 2)) ^ 2 + x (Sum.inl 2) * x (Sum.inr (Sum.inl 2)) + (x (Sum.inr (Sum.inl 2))) ^ 2 +
  x (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1))

private theorem k328r8p_Q_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (x : k328r8p_Ix → F) :
    StatedQuadMinus 4 F b c (k328r8p_Pmat F b c α *ᵥ x) = k328r8p_N F x := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hc : c = b ^ 2 * (α ^ 2 + α + 1) := by
    have h := hα
    rw [div_eq_mul_inv] at h
    have hm : b ^ 2 * (α ^ 2 + α) = b ^ 2 + c := by
      rw [h]; field_simp [hb]
    rw [mul_add, mul_one, hm]
    linear_combination (-(b ^ 2)) * h2
  rw [StatedQuadMinus, k328r8p_Pmat_mulVec]
  simp only [k328r8p_v8, k328r8p_N, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val]
  rw [hc]
  field_simp [hb]
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring_nf
  simp only [k328r8p_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero, Nat.cast_one]
  ring

private def k328r8p_J6 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.fromBlocks 0 1 1 0

private theorem k328r8p_J6_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (y : Fin 3 ⊕ Fin 3 → F) :
    k328r8p_J6 F *ᵥ y = Sum.elim (fun a => y (Sum.inr a)) (fun a => y (Sum.inl a)) := by
  rw [k328r8p_J6, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  rfl

private def k328r8p_N6 (F : Type) [Field F] (x : Fin 3 ⊕ Fin 3 → F) : F :=
  (x (Sum.inl 0)) ^ 2 + x (Sum.inl 0) * x (Sum.inr 0) + (x (Sum.inr 0)) ^ 2 +
  (x (Sum.inl 1)) ^ 2 + x (Sum.inl 1) * x (Sum.inr 1) + (x (Sum.inr 1)) ^ 2 +
  (x (Sum.inl 2)) ^ 2 + x (Sum.inl 2) * x (Sum.inr 2) + (x (Sum.inr 2)) ^ 2

private def k328r8p_polarN6 (F : Type) [Field F] (x y : Fin 3 ⊕ Fin 3 → F) : F :=
  k328r8p_N6 F (x + y) + k328r8p_N6 F x + k328r8p_N6 F y

private theorem k328r8p_polarN6_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (x y : Fin 3 ⊕ Fin 3 → F) :
    k328r8p_polarN6 F x y = x ⬝ᵥ (k328r8p_J6 F *ᵥ y) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  rw [k328r8p_J6_mulVec]
  simp only [k328r8p_polarN6, k328r8p_N6, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three]
  ring_nf
  simp only [k328r8p_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero]
  ring

private theorem k328r8p_spForm_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (x y : Fin 3 ⊕ Fin 3 → F) :
    CFSG.RankThree.SubgroupLists.spForm 3 F x y = k328r8p_polarN6 F x y := by
  have : CharP F 2 := k328r8p_charP_two F hF
  rw [CFSG.RankThree.SubgroupLists.spForm_apply, k328r8p_polarN6_eq F hF, k328r8p_J6_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three, sub_eq_add_neg,
    CharTwo.neg_eq]
  ring

private theorem k328r8p_mem_statedSp_of_preserves_N6 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : GL (Fin 3 ⊕ Fin 3) F)
    (hA : ∀ x, k328r8p_N6 F (A *ᵥ x) = k328r8p_N6 F x) :
    A ∈ StatedSp 3 F := by
  rw [CFSG.RankThree.SubgroupLists.mem_statedSp_iff_preserves]
  intro x y
  rw [k328r8p_spForm_eq F hF, k328r8p_spForm_eq F hF]
  simp only [k328r8p_polarN6, ← Matrix.mulVec_add, hA (x + y), hA x, hA y]

private def k328r8p_Mω (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.fromBlocks 0 1 1 1

private def k328r8p_mzcol (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r8p_Ix → (k328r8p_Ix → F) :=
  Sum.elim
    ![k328r8p_v8 F 0 0 0 1 0 0 0 0, k328r8p_v8 F 0 0 0 0 1 0 0 0,
      k328r8p_v8 F 0 0 0 0 0 1 0 0]
    (Sum.elim
      ![k328r8p_v8 F 1 0 0 1 0 0 0 0, k328r8p_v8 F 0 1 0 0 1 0 0 0,
        k328r8p_v8 F 0 0 1 0 0 1 0 0]
      ![k328r8p_v8 F 0 0 0 0 0 0 1 0, k328r8p_v8 F 0 0 0 0 0 0 0 1])

private def k328r8p_Mz (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix k328r8p_Ix k328r8p_Ix F :=
  ofColumns F (k328r8p_mzcol F)

private def k328r8p_zcol (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c α : F) :
    k328r8p_Ix → (k328r8p_Ix → F) :=
  Sum.elim
    ![k328r8p_v8 F 1 0 0 0 1 0 0 0, k328r8p_v8 F 0 1 0 1 0 0 0 0,
      k328r8p_v8 F 0 0 1 0 0 0 0 0]
    (Sum.elim
      ![k328r8p_v8 F 0 1 0 0 0 0 0 0, k328r8p_v8 F 1 0 0 0 0 0 0 0,
        k328r8p_v8 F 0 0 0 0 0 1 0 0]
      ![k328r8p_v8 F 0 0 0 0 0 0 α b⁻¹,
        k328r8p_v8 F 0 0 0 0 0 0 (c / b) (α + 1)])

private theorem k328r8p_zmat_mul_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) (hz : z₀ = ofColumns F (k328r8p_zcol F b c α)) :
    z₀ * k328r8p_Pmat F b c α = k328r8p_Pmat F b c α * k328r8p_Mz F := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hc : c = b ^ 2 * (α ^ 2 + α + 1) := by
    have h := hα
    rw [div_eq_mul_inv] at h
    have hm : b ^ 2 * (α ^ 2 + α) = b ^ 2 + c := by
      rw [h]; field_simp [hb]
    rw [mul_add, mul_one, hm]
    linear_combination (-(b ^ 2)) * h2
  have hcb : c / b = b * (α ^ 2 + α + 1) := by
    rw [hc]; field_simp [hb]; try ring
  rw [hz]
  ext r k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases r with i | i | i <;> rcases k with j | j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [ofColumns, k328r8p_zcol, k328r8p_Pmat, k328r8p_col, k328r8p_Mz,
      k328r8p_v8, k328r8p_mzcol, Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val, Sum.elim_inl, Sum.elim_inr, hcb,
      ]
  all_goals (try (field_simp [hb]))
  all_goals (try ring_nf)
  all_goals (try (simp only [k328r8p_ofNat_mod2 F, Nat.reduceMod, Nat.cast_zero]))
  all_goals (try ring)

private theorem k328r8p_Qmat_zmat_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) (hz : z₀ = ofColumns F (k328r8p_zcol F b c α)) :
    k328r8p_Qmat F b c α * z₀ * k328r8p_Pmat F b c α = k328r8p_Mz F := by
  rw [Matrix.mul_assoc, k328r8p_zmat_mul_Pmat F hF b c α hb hα z₀ hz, ← Matrix.mul_assoc,
    k328r8p_Qmat_mul_Pmat F hF b c α hb, Matrix.one_mul]

private noncomputable abbrev k328r8p_Qa {F : Type} [Field F] (b c : F) :
    QuadraticForm F (k328r8p_Ix → F) :=
  CFSG.LieType.Universal.Spin.quadMinus 4 F b c

private noncomputable abbrev k328r8p_O {F : Type} [Field F] (b c : F) :
    Subgroup (GL k328r8p_Ix F) :=
  (TauCeti.QuadraticMap.orthogonalGroup (k328r8p_Qa b c)).comap
    (toLinEquiv k328r8p_Ix F).toMonoidHom

private theorem k328r8p_mem_O {F : Type} [Field F] (b c : F) (g : GL k328r8p_Ix F) :
    g ∈ k328r8p_O b c ↔ ∀ v, StatedQuadMinus 4 F b c ((g : Matrix _ _ F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
  rw [Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact forall_congr' fun v => by
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, coe_quadMinus]

private theorem k328r8p_Omega_le_O {F : Type} [Field F] (b c : F) :
    StatedOmega (StatedQuadMinus 4 F b c) ≤ k328r8p_O b c := by
  rw [statedOmega_eq_comap (coe_quadMinus 4 F b c)]
  refine Subgroup.comap_mono (Subgroup.commutator_le.2 fun x hx y hy => ?_)
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
    (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)

private def k328r8p_wpart (F : Type) [Field F] (x : k328r8p_Ix → F) : Fin 3 ⊕ Fin 3 → F :=
  Sum.elim (fun i => x (Sum.inl i)) (fun i => x (Sum.inr (Sum.inl i)))

private def k328r8p_ppart (F : Type) [Field F] (x : k328r8p_Ix → F) : Fin 2 → F :=
  fun k => x (Sum.inr (Sum.inr k))

private def k328r8p_block (F : Type) [Field F] [DecidableEq F]
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) : Matrix k328r8p_Ix k328r8p_Ix F :=
  Matrix.of fun k r =>
    match k, r with
    | Sum.inl i, Sum.inl j => A (Sum.inl i) (Sum.inl j)
    | Sum.inl i, Sum.inr (Sum.inl j) => A (Sum.inl i) (Sum.inr j)
    | Sum.inr (Sum.inl i), Sum.inl j => A (Sum.inr i) (Sum.inl j)
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => A (Sum.inr i) (Sum.inr j)
    | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => if i = j then 1 else 0
    | _, _ => 0

private theorem k328r8p_block_one (F : Type) [Field F] [DecidableEq F] :
    k328r8p_block F 1 = 1 := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    simp [k328r8p_block, Matrix.one_apply]

private theorem k328r8p_block_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) :
    k328r8p_block F (A * B) = k328r8p_block F A * k328r8p_block F B := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    simp [k328r8p_block, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      ]

private theorem k328r8p_block_wpart (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (x : k328r8p_Ix → F) :
    k328r8p_wpart F (k328r8p_block F A *ᵥ x) = A *ᵥ k328r8p_wpart F x := by
  funext i
  rcases i with i | i <;>
    simp [k328r8p_block, k328r8p_wpart, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_three]

private theorem k328r8p_block_ppart (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (x : k328r8p_Ix → F) :
    k328r8p_ppart F (k328r8p_block F A *ᵥ x) = k328r8p_ppart F x := by
  funext i
  fin_cases i <;>
    simp [k328r8p_block, k328r8p_ppart, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      ]

private noncomputable def k328r8p_ιMat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) →* Matrix k328r8p_Ix k328r8p_Ix F where
  toFun A := k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F A) *
    k328r8p_Qmat F b c α
  map_one' := by
    rw [map_one, k328r8p_block_one, Matrix.mul_one, k328r8p_Pmat_mul_Qmat F hF b c α hb]
  map_mul' A B := by
    rw [map_mul, k328r8p_block_mul]
    have h1 := k328r8p_Qmat_mul_Pmat F hF b c α hb
    calc k328r8p_Pmat F b c α *
            (k328r8p_block F (k328r8p_rhoMat F A) * k328r8p_block F (k328r8p_rhoMat F B)) *
            k328r8p_Qmat F b c α
        = (k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F A)) *
            (k328r8p_block F (k328r8p_rhoMat F B) * k328r8p_Qmat F b c α) := by noncomm_ring
      _ = (k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F A)) *
            (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) *
            (k328r8p_block F (k328r8p_rhoMat F B) * k328r8p_Qmat F b c α) := by
            rw [h1, Matrix.mul_one]
      _ = (k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F A) *
              k328r8p_Qmat F b c α) *
            (k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F B) *
              k328r8p_Qmat F b c α) := by noncomm_ring

private noncomputable def k328r8p_ι (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    GL (Fin 3) (QuadraticAlgebra F 1 1) →* GL k328r8p_Ix F :=
  Units.map (k328r8p_ιMat F b c α hF hb)

private theorem k328r8p_N6_eq_spForm (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (x : Fin 3 ⊕ Fin 3 → F) :
    k328r8p_N6 F x = CFSG.RankThree.SubgroupLists.spForm 3 F x (k328r8p_Mω F *ᵥ x) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  rw [CFSG.RankThree.SubgroupLists.spForm_apply, k328r8p_Mω, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, Sum.elim_inl, Sum.elim_inr]
  simp only [k328r8p_N6, Fin.sum_univ_three, Pi.add_apply, Function.comp_apply]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  ring

private theorem k328r8p_rho_commute_Mω (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r8p_rhoMat F A * k328r8p_Mω F = k328r8p_Mω F * k328r8p_rhoMat F A := by
  show Matrix.fromBlocks (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)
      (A.map QuadraticAlgebra.im) (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im) *
      Matrix.fromBlocks 0 1 1 1 =
    Matrix.fromBlocks 0 1 1 1 *
      Matrix.fromBlocks (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)
        (A.map QuadraticAlgebra.im) (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im)
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, Matrix.one_mul, zero_add,
    Matrix.mul_add]

private theorem k328r8p_rho_preserves_N6 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : GL (Fin 3) (QuadraticAlgebra F 1 1))
    (hA : A ∈ k328r8p_GU F) (x : Fin 3 ⊕ Fin 3 → F) :
    k328r8p_N6 F (k328r8p_rhoMat F (A : Matrix _ _ _) *ᵥ x) = k328r8p_N6 F x := by
  have hsp : k328r8p_rho F A ∈ StatedSp 3 F := hA
  rw [k328r8p_N6_eq_spForm F hF, k328r8p_N6_eq_spForm F hF]
  have hcomm : k328r8p_rhoMat F (A : Matrix _ _ _) *ᵥ (k328r8p_Mω F *ᵥ x) =
      k328r8p_Mω F *ᵥ (k328r8p_rhoMat F (A : Matrix _ _ _) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k328r8p_rho_commute_Mω]
  rw [← hcomm]
  exact (CFSG.RankThree.SubgroupLists.mem_statedSp_iff_preserves.mp hsp) x (k328r8p_Mω F *ᵥ x)

private theorem k328r8p_N_eq (F : Type) [Field F] (x : k328r8p_Ix → F) :
    k328r8p_N F x = k328r8p_N6 F (k328r8p_wpart F x) +
      k328r8p_ppart F x 0 * k328r8p_ppart F x 1 := rfl

private theorem k328r8p_N_block (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : GL (Fin 3) (QuadraticAlgebra F 1 1))
    (hA : A ∈ k328r8p_GU F) (x : k328r8p_Ix → F) :
    k328r8p_N F (k328r8p_block F (k328r8p_rhoMat F (A : Matrix _ _ _)) *ᵥ x) =
      k328r8p_N F x := by
  rw [k328r8p_N_eq, k328r8p_N_eq, k328r8p_block_wpart, k328r8p_block_ppart,
    k328r8p_rho_preserves_N6 F hF A hA]

private theorem k328r8p_iota_isometry (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) (hA : A ∈ k328r8p_GU F)
    (w : k328r8p_Ix → F) :
    StatedQuadMinus 4 F b c
      (((k328r8p_ι F b c α hF hb A : GL k328r8p_Ix F) :
        Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ w) =
      StatedQuadMinus 4 F b c w := by
  have h1 : Matrix.mulVec ((k328r8p_ι F b c α hF hb A : GL k328r8p_Ix F) :
      Matrix k328r8p_Ix k328r8p_Ix F) w =
      k328r8p_Pmat F b c α *ᵥ
        (k328r8p_block F (k328r8p_rhoMat F (A : Matrix _ _ _)) *ᵥ (k328r8p_Qmat F b c α *ᵥ w)) := by
    change (k328r8p_Pmat F b c α *
        k328r8p_block F (k328r8p_rhoMat F (A : Matrix _ _ _)) * k328r8p_Qmat F b c α) *ᵥ w = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hw : w = k328r8p_Pmat F b c α *ᵥ (k328r8p_Qmat F b c α *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, k328r8p_Pmat_mul_Qmat F hF b c α hb, Matrix.one_mulVec]
  rw [h1, k328r8p_Q_Pmat F hF b c α hb hα, k328r8p_N_block F hF A hA]
  conv_rhs => rw [hw, k328r8p_Q_Pmat F hF b c α hb hα]

private theorem k328r8p_statement_zcol (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) :
    (Sum.elim
      ![bv F (Sum.inl 0) + bv F (Sum.inr (Sum.inl 1)),
        bv F (Sum.inr (Sum.inl 0)) + bv F (Sum.inl 1),
        bv F (Sum.inl 2)]
      (Sum.elim
        ![bv F (Sum.inl 1), bv F (Sum.inl 0), bv F (Sum.inr (Sum.inl 2))]
        ![α • bv F (Sum.inr (Sum.inr 0)) + b⁻¹ • bv F (Sum.inr (Sum.inr 1)),
          (c / b) • bv F (Sum.inr (Sum.inr 0)) + (α + 1) • bv F (Sum.inr (Sum.inr 1))]))
    = k328r8p_zcol F b c α := by
  funext k
  rcases k with i | i | i <;> fin_cases i <;>
    funext r <;>
    rcases r with j | j | j <;> fin_cases j <;>
    simp [k328r8p_zcol, k328r8p_v8, bv]

private theorem k328r8p_not_mem_O_of_b_zero (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b = 0)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    z₀ ∉ k328r8p_O b c := by
  have : CharP F 2 := k328r8p_charP_two F hF
  intro hzO
  have hc : c ≠ 0 := by simpa [hb] using hbc 0
  have hv := (k328r8p_mem_O b c z₀).1 hzO (bv F (Sum.inr (Sum.inr 1)))
  have hcol : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ bv F (Sum.inr (Sum.inr 1)) =
      k328r8p_v8 F 0 0 0 0 0 0 (c / b) (α + 1) := by
    rw [hz]
    simp only [bv, Matrix.mulVec_single_one]
    rfl
  have hQ1 : StatedQuadMinus 4 F b c (k328r8p_v8 F 0 0 0 0 0 0 (c / b) (α + 1)) =
      c * (α + 1) ^ 2 := by
    simp [StatedQuadMinus, k328r8p_v8, hb, Fin.sum_univ_three]
  have hQ2 : StatedQuadMinus 4 F b c (bv F (Sum.inr (Sum.inr 1))) = c := by
    simp [StatedQuadMinus, bv, hb]
  rw [hcol, hQ1, hQ2] at hv
  have hsq : (α + 1) ^ 2 = 1 :=
    mul_left_cancel₀ hc (by rw [hv, mul_one])
  have hα' : α ^ 2 + α = 1 := by simpa [hb] using hα
  obtain h | h := sq_eq_one_iff.mp hsq
  · have hα0 : α = 0 := by
      exact add_right_cancel (show α + 1 = (0 : F) + 1 by simpa using h)
    rw [hα0] at hα'
    simp at hα'
  · rw [CharTwo.neg_eq] at h
    have hα0 : α = 0 := by
      exact add_right_cancel (show α + 1 = (0 : F) + 1 by simpa using h)
    rw [hα0] at hα'
    simp at hα'

private theorem k328r8p_block_injective (F : Type) [Field F] [DecidableEq F] :
    Function.Injective (k328r8p_block F) := by
  intro A B h
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simpa [k328r8p_block] using congrFun (congrFun h (Sum.inl a)) (Sum.inl b)
  · simpa [k328r8p_block] using congrFun (congrFun h (Sum.inl a)) (Sum.inr (Sum.inl b))
  · simpa [k328r8p_block] using congrFun (congrFun h (Sum.inr (Sum.inl a))) (Sum.inl b)
  · simpa [k328r8p_block] using congrFun (congrFun h (Sum.inr (Sum.inl a))) (Sum.inr (Sum.inl b))

private theorem k328r8p_Qmat_ιMat_Pmat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r8p_Qmat F b c α * k328r8p_ιMat F b c α hF hb A * k328r8p_Pmat F b c α =
      k328r8p_block F (k328r8p_rhoMat F A) := by
  show k328r8p_Qmat F b c α *
      (k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F A) *
        k328r8p_Qmat F b c α) * k328r8p_Pmat F b c α = _
  calc k328r8p_Qmat F b c α * (k328r8p_Pmat F b c α *
          k328r8p_block F (k328r8p_rhoMat F A) * k328r8p_Qmat F b c α) *
          k328r8p_Pmat F b c α
      = k328r8p_Qmat F b c α * k328r8p_Pmat F b c α *
          k328r8p_block F (k328r8p_rhoMat F A) *
          (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) := by noncomm_ring
    _ = k328r8p_block F (k328r8p_rhoMat F A) := by
        rw [k328r8p_Qmat_mul_Pmat F hF b c α hb]; simp

private theorem k328r8p_ιMat_injective (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Function.Injective (k328r8p_ιMat F b c α hF hb) := by
  intro A B h
  have hA := k328r8p_Qmat_ιMat_Pmat F b c α hF hb A
  have hB := k328r8p_Qmat_ιMat_Pmat F b c α hF hb B
  have h1 : k328r8p_block F (k328r8p_rhoMat F A) = k328r8p_block F (k328r8p_rhoMat F B) :=
    hA.symm.trans ((congrArg (fun M => k328r8p_Qmat F b c α * M * k328r8p_Pmat F b c α) h).trans hB)
  exact k328r8p_rhoMat_injective F (k328r8p_block_injective F h1)

private theorem k328r8p_ι_injective (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Function.Injective (k328r8p_ι F b c α hF hb) :=
  Units.map_injective (k328r8p_ιMat_injective F b c α hF hb)

private theorem k328r8p_orderOf_ι (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    orderOf (k328r8p_ι F b c α hF hb A) = orderOf A :=
  orderOf_injective (k328r8p_ι F b c α hF hb) (k328r8p_ι_injective F b c α hF hb) A

private theorem k328r8p_Mz_eq_block_Mω (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r8p_Mz F = k328r8p_block F (k328r8p_Mω F) := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [k328r8p_Mz, ofColumns, k328r8p_mzcol, k328r8p_block, k328r8p_Mω, k328r8p_v8,
      Matrix.fromBlocks, Matrix.one_apply]

private theorem k328r8p_rhoMat_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    k328r8p_rhoMat F (k328r8p_omegaUnit F hF :
      Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) = k328r8p_Mω F := by
  simpa [k328r8p_rho, k328r8p_Mω] using k328r8p_rho_omegaUnit F hF

private theorem k328r8p_z0_eq_ι (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    z₀ = k328r8p_ι F b c α hF hb (k328r8p_omegaUnit F hF) := by
  let : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  have hcomp : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) =
      k328r8p_Pmat F b c α * k328r8p_Mz F * k328r8p_Qmat F b c α := by
    have h := k328r8p_Qmat_zmat_Pmat F hF b c α hb hα z₀ hz
    have h2 : k328r8p_Pmat F b c α *
        (k328r8p_Qmat F b c α * (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
          k328r8p_Pmat F b c α) * k328r8p_Qmat F b c α =
        (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) := by
      calc k328r8p_Pmat F b c α * (k328r8p_Qmat F b c α *
              (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α) *
              k328r8p_Qmat F b c α
          = (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) *
              (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
              (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) := by noncomm_ring
        _ = (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) := by
            rw [k328r8p_Pmat_mul_Qmat F hF b c α hb]; simp
    exact h2.symm.trans (by rw [h])
  apply Units.ext
  change (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) =
    k328r8p_Pmat F b c α * k328r8p_block F (k328r8p_rhoMat F
      (k328r8p_omegaUnit F hF : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) *
      k328r8p_Qmat F b c α
  rw [hcomp, k328r8p_rhoMat_omegaUnit F hF, ← k328r8p_Mz_eq_block_Mω F]

private theorem k328r8p_orderOf_z0 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    orderOf z₀ = 3 := by
  let : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  rw [k328r8p_z0_eq_ι F hF b c α hb hα z₀ hz, k328r8p_orderOf_ι F b c α hF hb,
    k328r8p_orderOf_omegaUnit F hF]

private noncomputable abbrev k328r8p_Y (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Subgroup (GL k328r8p_Ix F) :=
  (k328r8p_SU F).map (k328r8p_ι F b c α hF hb)

private theorem k328r8p_SU_perfect (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    commutator (k328r8p_SU F) = ⊤ := by
  have : Finite (QuadraticAlgebra F 1 1) :=
    Nat.finite_of_card_ne_zero (by rw [k328r8p_card_L F hF]; norm_num)
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (F := QuadraticAlgebra F 1 1) (p := 2) (f := 3)
      (by rw [k328r8p_card_L F hF]; norm_num) (n := 3) le_rfl (by norm_num)).1
  exact ((fun h => ⟨h.1.1, h.2.1⟩ : CFSG.IsQuasisimple
      (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1)) →
      CFSG.Open.IsQuasisimple (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1))) h).1

private theorem k328r8p_Y_perfect (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    ⁅k328r8p_Y F b c α hF hb, k328r8p_Y F b c α hF hb⁆ = k328r8p_Y F b c α hF hb := by
  rw [← Subgroup.map_commutator, commutator_self_of_perfect (k328r8p_SU_perfect F hF)]

private theorem k328r8p_Y_isometry (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (g : GL k328r8p_Ix F) (hg : g ∈ k328r8p_Y F b c α hF hb) (v : k328r8p_Ix → F) :
    StatedQuadMinus 4 F b c ((g : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ v) =
      StatedQuadMinus 4 F b c v := by
  obtain ⟨A, hA, rfl⟩ := hg
  have hA' : A ∈ k328r8p_GU F := by
    rw [k328r8p_statedSU_eq F hF] at hA
    exact hA.1
  exact k328r8p_iota_isometry F hF b c α hb hα A hA' v

private theorem k328r8p_Y_le (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    k328r8p_Y F b c α hF hb ≤ StatedOmega (StatedQuadMinus 4 F b c) := by
  have hY : ∀ g ∈ k328r8p_Y F b c α hF hb, ∀ v,
      StatedQuadMinus 4 F b c ((g : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ v) =
        StatedQuadMinus 4 F b c v :=
    fun g hg v => k328r8p_Y_isometry F b c α hF hb hα g hg v
  have hle : k328r8p_Y F b c α hF hb ≤ Subgroup.closure
      {A : GL k328r8p_Ix F |
        ∀ v, StatedQuadMinus 4 F b c ((A : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ v) =
          StatedQuadMinus 4 F b c v} :=
    fun g hg => Subgroup.subset_closure (hY g hg)
  rw [← k328r8p_Y_perfect F b c α hF hb]
  exact Subgroup.commutator_mono hle hle

private theorem k328r8p_z0_mem_Y (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    z₀ ∈ k328r8p_Y F b c α hF hb := by
  rw [k328r8p_z0_eq_ι F hF b c α hb hα z₀ hz]
  exact Subgroup.mem_map_of_mem _ (k328r8p_omegaUnit_mem_SU F hF)

private theorem k328r8p_Y_le_stdComp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    k328r8p_Y F b c α hF hb ≤ stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  have hYC : k328r8p_Y F b c α hF hb ≤
      StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {z₀} := by
    refine le_inf (k328r8p_Y_le F b c α hF hb hα) ?_
    rintro _ ⟨A, hA, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [k328r8p_z0_eq_ι F hF b c α hb hα z₀ hz, ← map_mul, ← map_mul]
    congr 1
    rw [k328r8p_omegaUnit]
    exact (Matrix.GeneralLinearGroup.scalar_commute _ A).symm
  have h := Subgroup.commutator_mono hYC hYC
  rwa [k328r8p_Y_perfect F b c α hF hb] at h

private def k328r8p_planeBlock (F : Type) [Field F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F) : Matrix k328r8p_Ix k328r8p_Ix F :=
  Matrix.of fun k r =>
    match k, r with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => if i = j then 1 else 0
    | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => D i j
    | _, _ => 0

private theorem k328r8p_planeBlock_one (F : Type) [Field F] [DecidableEq F] :
    k328r8p_planeBlock F 1 = 1 := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    simp [k328r8p_planeBlock, Matrix.one_apply]

private theorem k328r8p_planeBlock_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_planeBlock F (A * B) = k328r8p_planeBlock F A * k328r8p_planeBlock F B := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    simp [k328r8p_planeBlock, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]

private def k328r8p_wIdx (F : Type) [Field F] [DecidableEq F] :
    (Fin 3 ⊕ Fin 3) → k328r8p_Ix :=
  Sum.elim Sum.inl (fun i => Sum.inr (Sum.inl i))

private def k328r8p_wBlock (F : Type) [Field F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.of fun a b => g (k328r8p_wIdx F a) (k328r8p_wIdx F b)

private def k328r8p_pBlock (F : Type) [Field F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => g (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))

private theorem k328r8p_g_mul_Mz_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (k : k328r8p_Ix) (b : Fin 3) :
    (g * k328r8p_Mz F) k (Sum.inl b) = g k (Sum.inr (Sum.inl b)) := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_g_mul_Mz_inl_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (k : k328r8p_Ix) (b : Fin 3) :
    (g * k328r8p_Mz F) k (Sum.inr (Sum.inl b)) =
      g k (Sum.inl b) + g k (Sum.inr (Sum.inl b)) := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_g_mul_Mz_inr_inr (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (k : k328r8p_Ix) (b : Fin 2) :
    (g * k328r8p_Mz F) k (Sum.inr (Sum.inr b)) = g k (Sum.inr (Sum.inr b)) := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_Mz_mul_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (a : Fin 3) (r : k328r8p_Ix) :
    (k328r8p_Mz F * g) (Sum.inl a) r = g (Sum.inr (Sum.inl a)) r := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_Mz_mul_inl_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (a : Fin 3) (r : k328r8p_Ix) :
    (k328r8p_Mz F * g) (Sum.inr (Sum.inl a)) r =
      g (Sum.inl a) r + g (Sum.inr (Sum.inl a)) r := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_Mz_mul_inr_inr (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F) (a : Fin 2) (r : k328r8p_Ix) :
    (k328r8p_Mz F * g) (Sum.inr (Sum.inr a)) r = g (Sum.inr (Sum.inr a)) r := by
  rw [Matrix.mul_apply]
  simp [k328r8p_Mz_eq_block_Mω, k328r8p_block, k328r8p_Mω, Matrix.fromBlocks, Matrix.one_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_blockDiag_off_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F)
    (hg : g * k328r8p_Mz F = k328r8p_Mz F * g) (a : Fin 3) (b : Fin 2) :
    g (Sum.inl a) (Sum.inr (Sum.inr b)) = 0 := by
  have h1 := congrFun (congrFun hg (Sum.inr (Sum.inl a))) (Sum.inr (Sum.inr b))
  rw [k328r8p_g_mul_Mz_inr_inr F g (Sum.inr (Sum.inl a)) b,
    k328r8p_Mz_mul_inl_inl F g a (Sum.inr (Sum.inr b))] at h1
  have h2 := add_right_cancel (show g (Sum.inl a) (Sum.inr (Sum.inr b)) +
      g (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) =
      (0 : F) + g (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) by rw [← h1, zero_add])
  exact h2

private theorem k328r8p_blockDiag_off_inr_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F)
    (hg : g * k328r8p_Mz F = k328r8p_Mz F * g) (a : Fin 3) (b : Fin 2) :
    g (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) = 0 := by
  have h0 := k328r8p_blockDiag_off_inl F g hg a b
  have h1 := congrFun (congrFun hg (Sum.inl a)) (Sum.inr (Sum.inr b))
  rw [k328r8p_g_mul_Mz_inr_inr F g (Sum.inl a) b,
    k328r8p_Mz_mul_inl F g a (Sum.inr (Sum.inr b))] at h1
  rw [h0] at h1
  exact h1.symm

private theorem k328r8p_blockDiag_off_inr_inr_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F)
    (hg : g * k328r8p_Mz F = k328r8p_Mz F * g) (a : Fin 2) (b : Fin 3) :
    g (Sum.inr (Sum.inr a)) (Sum.inl b) = 0 := by
  have h1 := congrFun (congrFun hg (Sum.inr (Sum.inr a))) (Sum.inr (Sum.inl b))
  rw [k328r8p_g_mul_Mz_inl_inl F g (Sum.inr (Sum.inr a)) b,
    k328r8p_Mz_mul_inr_inr F g a (Sum.inr (Sum.inl b))] at h1
  exact add_right_cancel (show g (Sum.inr (Sum.inr a)) (Sum.inl b) +
      g (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) =
      (0 : F) + g (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) by rw [h1, zero_add])

private theorem k328r8p_blockDiag_off_inr_inr_inl_ (F : Type) [Field F] [Fintype F]
    [DecidableEq F] (g : Matrix k328r8p_Ix k328r8p_Ix F)
    (hg : g * k328r8p_Mz F = k328r8p_Mz F * g) (a : Fin 2) (b : Fin 3) :
    g (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) = 0 := by
  have h0 := k328r8p_blockDiag_off_inr_inr_inl F g hg a b
  have h1 := congrFun (congrFun hg (Sum.inr (Sum.inr a))) (Sum.inl b)
  rw [k328r8p_g_mul_Mz_inl F g (Sum.inr (Sum.inr a)) b,
    k328r8p_Mz_mul_inr_inr F g a (Sum.inl b)] at h1
  rw [h1, h0]

private theorem k328r8p_blockDiag (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix k328r8p_Ix k328r8p_Ix F)
    (hg : g * k328r8p_Mz F = k328r8p_Mz F * g) :
    g = k328r8p_block F (k328r8p_wBlock F g) *
      k328r8p_planeBlock F (k328r8p_pBlock F g) := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j
  · simp [k328r8p_block, k328r8p_planeBlock, k328r8p_wBlock, k328r8p_wIdx, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · simp [k328r8p_block, k328r8p_planeBlock, k328r8p_wBlock, k328r8p_wIdx, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · rw [k328r8p_blockDiag_off_inl F g hg i j]
    simp [k328r8p_block, k328r8p_planeBlock, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · simp [k328r8p_block, k328r8p_planeBlock, k328r8p_wBlock, k328r8p_wIdx, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · simp [k328r8p_block, k328r8p_planeBlock, k328r8p_wBlock, k328r8p_wIdx, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · rw [k328r8p_blockDiag_off_inr_inl F g hg i j]
    simp [k328r8p_block, k328r8p_planeBlock, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · rw [k328r8p_blockDiag_off_inr_inr_inl F g hg i j]
    simp [k328r8p_block, k328r8p_planeBlock, k328r8p_pBlock, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · rw [k328r8p_blockDiag_off_inr_inr_inl_ F g hg i j]
    simp [k328r8p_block, k328r8p_planeBlock, k328r8p_pBlock, Matrix.mul_apply,
      Fintype.sum_sum_type]
  · simp [k328r8p_block, k328r8p_planeBlock, k328r8p_pBlock, Matrix.mul_apply,
      Fintype.sum_sum_type]

private def k328r8p_swapGL (F : Type) [Field F] : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)

private theorem k328r8p_block_planeBlock_commute (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (D : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_block F A * k328r8p_planeBlock F D =
      k328r8p_planeBlock F D * k328r8p_block F A := by
  ext k r
  rcases k with i | i | i <;> rcases r with j | j | j <;>
    simp [k328r8p_block, k328r8p_planeBlock, Matrix.mul_apply, Fintype.sum_sum_type,
      ]

private noncomputable def k328r8p_δMat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Matrix (Fin 2) (Fin 2) F →* Matrix k328r8p_Ix k328r8p_Ix F where
  toFun D := k328r8p_Pmat F b c α * k328r8p_planeBlock F D * k328r8p_Qmat F b c α
  map_one' := by
    rw [k328r8p_planeBlock_one, Matrix.mul_one, k328r8p_Pmat_mul_Qmat F hF b c α hb]
  map_mul' D E := by
    show k328r8p_Pmat F b c α * k328r8p_planeBlock F (D * E) * k328r8p_Qmat F b c α =
      (k328r8p_Pmat F b c α * k328r8p_planeBlock F D * k328r8p_Qmat F b c α) *
      (k328r8p_Pmat F b c α * k328r8p_planeBlock F E * k328r8p_Qmat F b c α)
    rw [k328r8p_planeBlock_mul]
    calc k328r8p_Pmat F b c α *
            (k328r8p_planeBlock F D * k328r8p_planeBlock F E) * k328r8p_Qmat F b c α
        = k328r8p_Pmat F b c α * k328r8p_planeBlock F D *
            (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) *
            (k328r8p_planeBlock F E * k328r8p_Qmat F b c α) := by
            rw [k328r8p_Qmat_mul_Pmat F hF b c α hb]; noncomm_ring
      _ = (k328r8p_Pmat F b c α * k328r8p_planeBlock F D * k328r8p_Qmat F b c α) *
            (k328r8p_Pmat F b c α * k328r8p_planeBlock F E * k328r8p_Qmat F b c α) := by
            noncomm_ring

private noncomputable def k328r8p_δ (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    GL (Fin 2) F →* GL k328r8p_Ix F :=
  Units.map (k328r8p_δMat F b c α hF hb)

private theorem k328r8p_conj_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (X Y : Matrix k328r8p_Ix k328r8p_Ix F) :
    (k328r8p_Pmat F b c α * X * k328r8p_Qmat F b c α) *
      (k328r8p_Pmat F b c α * Y * k328r8p_Qmat F b c α) =
      k328r8p_Pmat F b c α * (X * Y) * k328r8p_Qmat F b c α := by
  calc (k328r8p_Pmat F b c α * X * k328r8p_Qmat F b c α) *
        (k328r8p_Pmat F b c α * Y * k328r8p_Qmat F b c α)
      = k328r8p_Pmat F b c α * X * (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) * Y *
          k328r8p_Qmat F b c α := by noncomm_ring
    _ = k328r8p_Pmat F b c α * X * (1 : Matrix k328r8p_Ix k328r8p_Ix F) * Y *
          k328r8p_Qmat F b c α := by rw [k328r8p_Qmat_mul_Pmat F hF b c α hb]
    _ = k328r8p_Pmat F b c α * (X * Y) * k328r8p_Qmat F b c α := by noncomm_ring

private theorem k328r8p_ι_comm_δ (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0)
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) (D : GL (Fin 2) F) :
    k328r8p_ι F b c α hF hb A * k328r8p_δ F b c α hF hb D =
      k328r8p_δ F b c α hF hb D * k328r8p_ι F b c α hF hb A := by
  apply Units.ext
  change (k328r8p_Pmat F b c α *
        k328r8p_block F (k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) *
        k328r8p_Qmat F b c α) *
      (k328r8p_Pmat F b c α * k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) *
        k328r8p_Qmat F b c α) =
    (k328r8p_Pmat F b c α * k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) *
        k328r8p_Qmat F b c α) *
      (k328r8p_Pmat F b c α *
        k328r8p_block F (k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) *
        k328r8p_Qmat F b c α)
  rw [k328r8p_conj_mul F b c α hF hb
        (k328r8p_block F (k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))))
        (k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F)),
      k328r8p_conj_mul F b c α hF hb
        (k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F))
        (k328r8p_block F (k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)))),
      k328r8p_block_planeBlock_commute F
        (k328r8p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)))
        (D : Matrix (Fin 2) (Fin 2) F)]

private noncomputable def k328r8p_conjMat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (hF : Fintype.card F = 8) (hb : b ≠ 0) :
    Matrix k328r8p_Ix k328r8p_Ix F →* Matrix k328r8p_Ix k328r8p_Ix F where
  toFun X := k328r8p_Qmat F b c α * X * k328r8p_Pmat F b c α
  map_one' := by
    rw [Matrix.mul_one, k328r8p_Qmat_mul_Pmat F hF b c α hb]
  map_mul' X Y := by
    show k328r8p_Qmat F b c α * (X * Y) * k328r8p_Pmat F b c α =
      (k328r8p_Qmat F b c α * X * k328r8p_Pmat F b c α) *
        (k328r8p_Qmat F b c α * Y * k328r8p_Pmat F b c α)
    calc k328r8p_Qmat F b c α * (X * Y) * k328r8p_Pmat F b c α
        = k328r8p_Qmat F b c α * X * Y * k328r8p_Pmat F b c α := by noncomm_ring
      _ = (k328r8p_Qmat F b c α * X * k328r8p_Pmat F b c α) *
            (k328r8p_Qmat F b c α * Y * k328r8p_Pmat F b c α) := by
            rw [show (k328r8p_Qmat F b c α * X * k328r8p_Pmat F b c α) *
                (k328r8p_Qmat F b c α * Y * k328r8p_Pmat F b c α) =
              k328r8p_Qmat F b c α * X *
                (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) * Y *
                k328r8p_Pmat F b c α by noncomm_ring,
              k328r8p_Pmat_mul_Qmat F hF b c α hb]
            noncomm_ring

private theorem k328r8p_wBlock_block_mul_planeBlock (F : Type) [Field F] [Fintype F]
    [DecidableEq F] (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (D : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_wBlock F (k328r8p_block F X * k328r8p_planeBlock F D) = X := by
  ext a b
  simp only [k328r8p_wBlock, Matrix.of_apply]
  rw [Matrix.mul_apply, Finset.sum_eq_single (k328r8p_wIdx F b)]
  · rcases a with a | a <;> rcases b with b | b <;>
      simp [k328r8p_block, k328r8p_planeBlock, k328r8p_wIdx]
  · intro l _ hl
    have hz : k328r8p_planeBlock F D l (k328r8p_wIdx F b) = 0 := by
      rcases l with i | i | i <;> rcases b with j | j <;>
        simp_all [k328r8p_wIdx, k328r8p_planeBlock]
    rw [hz, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ (k328r8p_wIdx F b)) hb

private theorem k328r8p_pBlock_block_mul_planeBlock (F : Type) [Field F] [Fintype F]
    [DecidableEq F] (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (D : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_pBlock F (k328r8p_block F X * k328r8p_planeBlock F D) = D := by
  ext i j
  simp [k328r8p_pBlock, k328r8p_block, k328r8p_planeBlock, Matrix.mul_apply,
    Fintype.sum_sum_type]

private theorem k328r8p_wBlock_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r8p_wBlock F (1 : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [k328r8p_wBlock, k328r8p_wIdx, Matrix.one_apply]

private theorem k328r8p_pBlock_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r8p_pBlock F (1 : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
  ext i j
  simp [k328r8p_pBlock, Matrix.one_apply]

private theorem k328r8p_wBlock_mul_block (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (G : Matrix k328r8p_Ix k328r8p_Ix F)
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) :
    k328r8p_wBlock F (G * k328r8p_block F A) = k328r8p_wBlock F G * A := by
  ext a b
  simp only [k328r8p_wBlock, Matrix.of_apply, Matrix.mul_apply, k328r8p_block, k328r8p_wIdx,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr]
  rcases a with a | a <;> rcases b with b | b <;> simp

private theorem k328r8p_wBlock_block_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (G : Matrix k328r8p_Ix k328r8p_Ix F) :
    k328r8p_wBlock F (k328r8p_block F A * G) = A * k328r8p_wBlock F G := by
  ext a b
  simp only [k328r8p_wBlock, Matrix.of_apply, Matrix.mul_apply, k328r8p_block, k328r8p_wIdx,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr]
  rcases a with a | a <;> rcases b with b | b <;> simp

private theorem k328r8p_wBlock_comm_Mω (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (G : Matrix k328r8p_Ix k328r8p_Ix F)
    (hG : G * k328r8p_Mz F = k328r8p_Mz F * G) :
    k328r8p_wBlock F G * k328r8p_Mω F = k328r8p_Mω F * k328r8p_wBlock F G := by
  have h1 := congrArg (fun M => k328r8p_wBlock F M) hG
  rw [k328r8p_Mz_eq_block_Mω, k328r8p_wBlock_mul_block, k328r8p_wBlock_block_mul] at h1
  exact h1

private theorem k328r8p_exists_chi (F : Type) [Field F] [Fintype F]
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ χ : k328r8p_O b c →* ℤˣ,
      (∀ g : k328r8p_O b c, (g : GL k328r8p_Ix F) ∈
        StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1) ∧
      ∀ v : k328r8p_Ix → F, k328r8p_Qa b c v ≠ 0 →
        ∀ g : k328r8p_O b c,
          toLinEquiv k328r8p_Ix F (g : GL k328r8p_Ix F) =
            reflect (k328r8p_Qa b c) v → χ g = -1 := by
  obtain ⟨hnd, hT⟩ := regular_quadMinus (n := 4) (by norm_num) hbc
  obtain ⟨-, -, -, -, -, -, -, ⟨χ, hχ1, hχ2⟩, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  refine ⟨χ.comp ((toLinEquiv k328r8p_Ix F).toMonoidHom.subgroupComap _),
    fun g hg => ?_, fun v hv g hg => ?_⟩
  · rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap] at hg
    exact hχ1 _ hg
  · exact (congrArg χ (Subtype.ext hg)).trans (hχ2 v hv)

private theorem k328r8p_wpart_planeBlock (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F) (x : k328r8p_Ix → F) :
    k328r8p_wpart F (k328r8p_planeBlock F D *ᵥ x) = k328r8p_wpart F x := by
  funext a
  rcases a with a | a <;>
    simp [k328r8p_wpart, k328r8p_planeBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr]

private theorem k328r8p_ppart_planeBlock (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F) (x : k328r8p_Ix → F) :
    k328r8p_ppart F (k328r8p_planeBlock F D *ᵥ x) = D *ᵥ k328r8p_ppart F x := by
  funext i
  fin_cases i <;>
    simp [k328r8p_ppart, k328r8p_planeBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two]

private theorem k328r8p_N_planeBlock (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F)
    (hD : ∀ p : Fin 2 → F, (D *ᵥ p) 0 * (D *ᵥ p) 1 = p 0 * p 1) (x : k328r8p_Ix → F) :
    k328r8p_N F (k328r8p_planeBlock F D *ᵥ x) = k328r8p_N F x := by
  rw [k328r8p_N_eq, k328r8p_N_eq, k328r8p_wpart_planeBlock, k328r8p_ppart_planeBlock,
    hD (k328r8p_ppart F x)]

private theorem k328r8p_δ_mem_O (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (D : GL (Fin 2) F)
    (hD : ∀ p : Fin 2 → F,
      ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 0 * ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 1 =
        p 0 * p 1) :
    k328r8p_δ F b c α hF hb D ∈ k328r8p_O b c := by
  rw [k328r8p_mem_O]
  intro v
  have h1 : (k328r8p_δ F b c α hF hb D : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ v =
      k328r8p_Pmat F b c α *ᵥ
        (k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) *ᵥ
          (k328r8p_Qmat F b c α *ᵥ v)) := by
    rw [show (k328r8p_δ F b c α hF hb D : Matrix k328r8p_Ix k328r8p_Ix F) =
        k328r8p_Pmat F b c α * k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) *
          k328r8p_Qmat F b c α from rfl]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [h1, k328r8p_Q_Pmat F hF b c α hb hα,
    k328r8p_N_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) hD]
  rw [show StatedQuadMinus 4 F b c v =
      StatedQuadMinus 4 F b c (k328r8p_Pmat F b c α *ᵥ (k328r8p_Qmat F b c α *ᵥ v)) by
        rw [Matrix.mulVec_mulVec, k328r8p_Pmat_mul_Qmat F hF b c α hb, Matrix.one_mulVec],
    k328r8p_Q_Pmat F hF b c α hb hα]

private theorem k328r8p_plane_diag_or_anti (F : Type) [Field F]
    (D : Matrix (Fin 2) (Fin 2) F)
    (hD : ∀ p : Fin 2 → F, (D *ᵥ p) 0 * (D *ᵥ p) 1 = p 0 * p 1) :
    (D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 0 0 * D 1 1 = 1) ∨
      (D 0 0 = 0 ∧ D 1 1 = 0 ∧ D 0 1 * D 1 0 = 1) := by
  have h0 : D 0 0 * D 1 0 = 0 := by
    have h := hD (Pi.single (0 : Fin 2) 1)
    rw [Matrix.mulVec_single_one] at h
    simpa [Matrix.col_apply, Pi.single_apply] using h
  have h1 : D 0 1 * D 1 1 = 0 := by
    have h := hD (Pi.single (1 : Fin 2) 1)
    rw [Matrix.mulVec_single_one] at h
    simpa [Matrix.col_apply, Pi.single_apply] using h
  have h2 : (D 0 0 + D 0 1) * (D 1 0 + D 1 1) = 1 := by
    have h := hD (fun _ : Fin 2 => 1)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  by_cases h01 : D 0 1 = 0
  · left
    have hD00 : D 0 0 ≠ 0 := by
      intro h
      rw [h, h01, zero_add, zero_mul] at h2
      exact one_ne_zero h2.symm
    have hD10 : D 1 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hD00
      · exact h
    have hD00D11 : D 0 0 * D 1 1 = 1 := by
      rw [h01, add_zero, hD10, zero_add] at h2
      exact h2
    exact ⟨h01, hD10, hD00D11⟩
  · right
    have hD11 : D 1 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h h01
      · exact h
    have hD00 : D 0 0 = 0 := by
      by_contra h
      have hD10 : D 1 0 = 0 := by
        rcases mul_eq_zero.mp h0 with h' | h'
        · exact absurd h' h
        · exact h'
      rw [hD10, hD11, add_zero, mul_zero] at h2
      exact one_ne_zero h2.symm
    have hprod : D 0 1 * D 1 0 = 1 := by
      rw [hD00, hD11, zero_add, add_zero] at h2
      exact h2
    exact ⟨hD00, hD11, hprod⟩

private theorem k328r8p_Q_e2f2 (F : Type) [Field F] [Fintype F] [DecidableEq F] (b c : F) :
    k328r8p_Qa b c (k328r8p_v8 F 0 0 1 0 0 1 0 0) = 1 := by
  rw [k328r8p_Qa, coe_quadMinus]
  simp [StatedQuadMinus, k328r8p_v8,
    Fin.sum_univ_three]

private theorem k328r8p_polar_e2f2 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c : F) (z : k328r8p_Ix → F) :
    QuadraticMap.polar (k328r8p_Qa b c) (k328r8p_v8 F 0 0 1 0 0 1 0 0) z =
      z (Sum.inl 2) + z (Sum.inr (Sum.inl 2)) := by
  rw [k328r8p_Qa, CFSG.LieType.Universal.Spin.polar_quadMinus]
  simp [k328r8p_v8, Fin.sum_univ_three]
  ring

private theorem k328r8p_reflect_e2f2 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F) (z : k328r8p_Ix → F) :
    reflect (k328r8p_Qa b c) (k328r8p_v8 F 0 0 1 0 0 1 0 0) z =
      z + (z (Sum.inl 2) + z (Sum.inr (Sum.inl 2))) • (k328r8p_v8 F 0 0 1 0 0 1 0 0) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  have hQ : k328r8p_Qa b c (k328r8p_v8 F 0 0 1 0 0 1 0 0) = 1 := k328r8p_Q_e2f2 F b c
  have hv : k328r8p_Qa b c (k328r8p_v8 F 0 0 1 0 0 1 0 0) ≠ 0 := by
    rw [hQ]; exact one_ne_zero
  rw [reflect_apply hv, k328r8p_polar_e2f2 F b c z, hQ, div_one, sub_eq_add_neg,
    CharTwo.neg_eq]

private theorem k328r8p_Pmat_mulVec_bv_sum (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) :
    k328r8p_Pmat F b c α *ᵥ (bv F (Sum.inr (Sum.inr 0)) + bv F (Sum.inr (Sum.inr 1))) =
      k328r8p_v8 F 0 0 1 0 0 1 0 0 := by
  rw [k328r8p_Pmat_mulVec]
  simp [bv, Pi.add_apply, k328r8p_v8]

private theorem k328r8p_planeBlock_swap_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (y : k328r8p_Ix → F) :
    k328r8p_planeBlock F (k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) *ᵥ y =
      y + (y (Sum.inr (Sum.inr 0)) + y (Sum.inr (Sum.inr 1))) •
        (bv F (Sum.inr (Sum.inr 0)) + bv F (Sum.inr (Sum.inr 1))) := by
  have : CharP F 2 := k328r8p_charP_two F hF
  funext k
  rcases k with i | i | i <;> fin_cases i <;>
    simp [k328r8p_planeBlock, k328r8p_swapGL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, bv, Pi.add_apply]
  all_goals try rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  all_goals try rw [← add_assoc, add_comm (y (Sum.inr (Sum.inr 1))) (y (Sum.inr (Sum.inr 0))),
    add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem k328r8p_Qmat_inr_inr_zero (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (r : k328r8p_Ix) :
    k328r8p_Qmat F b c α (Sum.inr (Sum.inr 0)) r = if r = Sum.inl 2 then 1 else 0 := by
  rcases r with i | i | i <;> fin_cases i <;>
    simp [k328r8p_Qmat, k328r8p_qrow, k328r8p_v8]

private theorem k328r8p_Qmat_inr_inr_one (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (r : k328r8p_Ix) :
    k328r8p_Qmat F b c α (Sum.inr (Sum.inr 1)) r =
      if r = Sum.inr (Sum.inl 2) then 1 else 0 := by
  rcases r with i | i | i <;> fin_cases i <;>
    simp [k328r8p_Qmat, k328r8p_qrow, k328r8p_v8]

private theorem k328r8p_Qmat_swap_coords (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (b c α : F) (z : k328r8p_Ix → F) :
    (k328r8p_Qmat F b c α *ᵥ z) (Sum.inr (Sum.inr 0)) +
        (k328r8p_Qmat F b c α *ᵥ z) (Sum.inr (Sum.inr 1)) =
      z (Sum.inl 2) + z (Sum.inr (Sum.inl 2)) := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
  simp only [k328r8p_Qmat_inr_inr_zero, k328r8p_Qmat_inr_inr_one, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private theorem k328r8p_δ_swap_reflect (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (_hα : α ^ 2 + α = 1 + c / b ^ 2) :
    toLinEquiv k328r8p_Ix F
        (k328r8p_δ F b c α hF hb (k328r8p_swapGL F)) =
      reflect (k328r8p_Qa b c) (k328r8p_v8 F 0 0 1 0 0 1 0 0) := by
  apply LinearEquiv.ext
  intro z
  rw [toLinEquiv_apply,
    show (k328r8p_δ F b c α hF hb (k328r8p_swapGL F) : GL k328r8p_Ix F) =
        k328r8p_δMat F b c α hF hb (k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) from rfl,
    show k328r8p_δMat F b c α hF hb (k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) =
        k328r8p_Pmat F b c α *
          k328r8p_planeBlock F (k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) *
          k328r8p_Qmat F b c α from rfl,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    k328r8p_planeBlock_swap_mulVec F hF, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, k328r8p_Pmat_mul_Qmat F hF b c α hb, Matrix.one_mulVec,
    k328r8p_Pmat_mulVec_bv_sum, k328r8p_Qmat_swap_coords F b c α z,
    k328r8p_reflect_e2f2 F hF b c z]

private theorem k328r8p_chi_ι (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (χ : k328r8p_O b c →* ℤˣ)
    (hχ : ∀ g : k328r8p_O b c, (g : GL k328r8p_Ix F) ∈
      StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1)
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) (hA : A ∈ k328r8p_GU F) :
    χ ⟨k328r8p_ι F b c α hF hb A,
      (k328r8p_mem_O b c _).2 (fun v =>
        k328r8p_iota_isometry F hF b c α hb hα A hA v)⟩ = 1 := by
  let : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  have hsp := (k328r8p_mem_statedSp_iff F hF A).1 hA
  have hstar : Matrix.det
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star) =
      star ((Matrix.GeneralLinearGroup.det A : (QuadraticAlgebra F 1 1)ˣ) :
        QuadraticAlgebra F 1 1) := by
    have h := (starRingEnd (QuadraticAlgebra F 1 1)).map_det
      (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))
    have h' : Matrix.det ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star) =
        star ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).det) := by
      rw [show (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star =
          (starRingEnd (QuadraticAlgebra F 1 1)).mapMatrix
            (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) from rfl,
        ← h, starRingEnd_apply]
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h'
  have hdet : star ((Matrix.GeneralLinearGroup.det A : (QuadraticAlgebra F 1 1)ˣ) :
        QuadraticAlgebra F 1 1) *
      ((Matrix.GeneralLinearGroup.det A : (QuadraticAlgebra F 1 1)ˣ) :
        QuadraticAlgebra F 1 1) = 1 := by
    have := congrArg Matrix.det hsp
    rw [Matrix.det_mul, Matrix.det_transpose, hstar, Matrix.det_one] at this
    exact this
  have h9 : ((Matrix.GeneralLinearGroup.det A : (QuadraticAlgebra F 1 1)ˣ) :
      QuadraticAlgebra F 1 1) ^ 9 = 1 := by
    rw [k328r8p_star_pow F hF] at hdet
    rwa [← pow_succ] at hdet
  have hA9SU : A ^ 9 ∈ k328r8p_SU F := by
    rw [k328r8p_statedSU_eq F hF, Subgroup.mem_inf]
    refine ⟨(k328r8p_GU F).pow_mem hA 9, ?_⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_pow_eq_pow_val, Matrix.det_pow, ← Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one]
    exact h9
  have h9χ : χ ⟨k328r8p_ι F b c α hF hb A,
      (k328r8p_mem_O b c _).2 (fun v =>
        k328r8p_iota_isometry F hF b c α hb hα A hA v)⟩ ^ 9 = 1 := by
    rw [← map_pow]
    apply hχ
    change (k328r8p_ι F b c α hF hb A ^ 9 : GL k328r8p_Ix F) ∈
      StatedOmega (StatedQuadMinus 4 F b c)
    rw [← map_pow]
    exact k328r8p_Y_le F b c α hF hb hα (Subgroup.mem_map_of_mem _ hA9SU)
  rcases Int.units_eq_one_or (χ ⟨k328r8p_ι F b c α hF hb A,
      (k328r8p_mem_O b c _).2 (fun v =>
        k328r8p_iota_isometry F hF b c α hb hα A hA v)⟩) with h | h
  · exact h
  · rw [h] at h9χ
    exact absurd h9χ (by decide)

private theorem k328r8p_chi_diag (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (_hα : α ^ 2 + α = 1 + c / b ^ 2)
    (χ : k328r8p_O b c →* ℤˣ)
    (hχ : ∀ g : k328r8p_O b c, (g : GL k328r8p_Ix F) ∈
      StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1)
    (K : GL (Fin 2) F) (hK01 : (K : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (hK10 : (K : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hKdet : (K : Matrix (Fin 2) (Fin 2) F) 0 0 * (K : Matrix (Fin 2) (Fin 2) F) 1 1 = 1)
    (hKO : k328r8p_δ F b c α hF hb K ∈ k328r8p_O b c) :
    χ ⟨k328r8p_δ F b c α hF hb K, hKO⟩ = 1 := by
  have ha0 : (K : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h; rw [h, zero_mul] at hKdet; exact one_ne_zero hKdet.symm
  have hb0 : (K : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hKdet; exact one_ne_zero hKdet.symm
  have ha7 : (K : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (K := F) ((K : Matrix (Fin 2) (Fin 2) F) 0 0) ha0
    rwa [hF] at this
  have hb7 : (K : Matrix (Fin 2) (Fin 2) F) 1 1 ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (K := F) ((K : Matrix (Fin 2) (Fin 2) F) 1 1) hb0
    rwa [hF] at this
  have hKmat : (K : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![K 0 0, K 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, hK01, hK10]
  have hK7mat : (K : Matrix (Fin 2) (Fin 2) F) ^ 7 = 1 := by
    rw [hKmat, Matrix.diagonal_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, ha7, hb7]
  have hK7 : K ^ 7 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hK7mat
  have h7 : χ ⟨k328r8p_δ F b c α hF hb K, hKO⟩ ^ 7 = 1 := by
    rw [← map_pow]
    apply hχ
    change (k328r8p_δ F b c α hF hb K ^ 7 : GL k328r8p_Ix F) ∈
      StatedOmega (StatedQuadMinus 4 F b c)
    rw [← map_pow, hK7, map_one]
    exact Subgroup.one_mem _
  rcases Int.units_eq_one_or (χ ⟨k328r8p_δ F b c α hF hb K, hKO⟩) with h | h
  · exact h
  · rw [h] at h7
    exact absurd h7 (by decide)

private theorem k328r8p_D_diag (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (χ : k328r8p_O b c →* ℤˣ)
    (hχΩ : ∀ g : k328r8p_O b c, (g : GL k328r8p_Ix F) ∈
      StatedOmega (StatedQuadMinus 4 F b c) → χ g = 1)
    (hχr : ∀ v : k328r8p_Ix → F, k328r8p_Qa b c v ≠ 0 →
      ∀ g : k328r8p_O b c,
        toLinEquiv k328r8p_Ix F (g : GL k328r8p_Ix F) =
          reflect (k328r8p_Qa b c) v → χ g = -1)
    (D : GL (Fin 2) F)
    (hD : ∀ p : Fin 2 → F,
      ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 0 * ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 1 =
        p 0 * p 1)
    (hχδD : χ ⟨k328r8p_δ F b c α hF hb D,
      k328r8p_δ_mem_O F hF b c α hb hα D hD⟩ = 1) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (D : Matrix (Fin 2) (Fin 2) F) 0 0 * (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  rcases k328r8p_plane_diag_or_anti F (D : Matrix (Fin 2) (Fin 2) F) hD with h | h
  · exact h
  · exfalso
    obtain ⟨h00, h11, hprod⟩ := h
    have hswapplane : ∀ p : Fin 2 → F,
        ((k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 0 *
            ((k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 1 = p 0 * p 1 := by
      intro p
      simp [k328r8p_swapGL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    have hOswap : k328r8p_δ F b c α hF hb (k328r8p_swapGL F) ∈ k328r8p_O b c :=
      k328r8p_δ_mem_O F hF b c α hb hα (k328r8p_swapGL F) hswapplane
    have hχswap : χ ⟨k328r8p_δ F b c α hF hb (k328r8p_swapGL F), hOswap⟩ = -1 :=
      hχr _ (by rw [k328r8p_Q_e2f2 F b c]; exact one_ne_zero) _
        (k328r8p_δ_swap_reflect F hF b c α hb hα)
    let K : GL (Fin 2) F := k328r8p_swapGL F * D
    have hK01 : (K : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      show ((k328r8p_swapGL F * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
      rw [Units.val_mul]
      simp [k328r8p_swapGL, Matrix.mul_apply, Fin.sum_univ_two, h11]
    have hK10 : (K : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      show ((k328r8p_swapGL F * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      rw [Units.val_mul]
      simp [k328r8p_swapGL, Matrix.mul_apply, Fin.sum_univ_two, h00]
    have hK00 : (K : Matrix (Fin 2) (Fin 2) F) 0 0 = (D : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      show ((k328r8p_swapGL F * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
      rw [Units.val_mul]
      simp [k328r8p_swapGL, Matrix.mul_apply, Fin.sum_univ_two]
    have hK11 : (K : Matrix (Fin 2) (Fin 2) F) 1 1 = (D : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      show ((k328r8p_swapGL F * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = _
      rw [Units.val_mul]
      simp [k328r8p_swapGL, Matrix.mul_apply, Fin.sum_univ_two]
    have hKdet : (K : Matrix (Fin 2) (Fin 2) F) 0 0 * (K : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      rw [hK00, hK11, mul_comm, hprod]
    have hKplane : ∀ p : Fin 2 → F,
        ((K : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 0 * ((K : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 1 =
          p 0 * p 1 := by
      intro p
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hK01, hK10, zero_mul, add_zero,
        zero_add]
      rw [show (K : Matrix (Fin 2) (Fin 2) F) 0 0 * p 0 * ((K : Matrix (Fin 2) (Fin 2) F) 1 1 * p 1) =
          ((K : Matrix (Fin 2) (Fin 2) F) 0 0 * (K : Matrix (Fin 2) (Fin 2) F) 1 1) * (p 0 * p 1)
        by ring, hKdet, one_mul]
    have hKO : k328r8p_δ F b c α hF hb K ∈ k328r8p_O b c :=
      k328r8p_δ_mem_O F hF b c α hb hα K hKplane
    have hχK : χ ⟨k328r8p_δ F b c α hF hb K, hKO⟩ = 1 :=
      k328r8p_chi_diag F hF b c α hb hα χ hχΩ K hK01 hK10 hKdet hKO
    have hDswap : D = k328r8p_swapGL F * K := by
      apply Units.ext
      change (D : Matrix (Fin 2) (Fin 2) F) =
        (k328r8p_swapGL F : Matrix (Fin 2) (Fin 2) F) *
          ((k328r8p_swapGL F * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      rw [Units.val_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [k328r8p_swapGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    have hδD : (⟨k328r8p_δ F b c α hF hb D,
        k328r8p_δ_mem_O F hF b c α hb hα D hD⟩ : k328r8p_O b c) =
        ⟨k328r8p_δ F b c α hF hb (k328r8p_swapGL F), hOswap⟩ *
          ⟨k328r8p_δ F b c α hF hb K, hKO⟩ := by
      apply Subtype.ext
      change (k328r8p_δ F b c α hF hb D : GL k328r8p_Ix F) =
        k328r8p_δ F b c α hF hb (k328r8p_swapGL F) *
          k328r8p_δ F b c α hF hb K
      rw [← map_mul, hDswap]
    have : χ ⟨k328r8p_δ F b c α hF hb D,
        k328r8p_δ_mem_O F hF b c α hb hα D hD⟩ = -1 := by
      rw [hδD, map_mul, hχswap, hχK, mul_one]
    rw [this] at hχδD
    exact absurd hχδD (by decide)

private def k328r8p_vecOfW (F : Type) [Field F] [DecidableEq F]
    (w : Fin 3 ⊕ Fin 3 → F) : k328r8p_Ix → F :=
  Sum.elim (fun i => w (Sum.inl i)) (Sum.elim (fun i => w (Sum.inr i)) (fun _ => 0))

private def k328r8p_vecOfP (F : Type) [Field F] [DecidableEq F]
    (p : Fin 2 → F) : k328r8p_Ix → F :=
  Sum.elim (fun _ : Fin 3 => 0) (Sum.elim (fun _ : Fin 3 => 0) p)

private theorem k328r8p_wpart_vecOfW (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (w : Fin 3 ⊕ Fin 3 → F) : k328r8p_wpart F (k328r8p_vecOfW F w) = w := by
  ext a; rcases a with a | a <;> rfl

private theorem k328r8p_ppart_vecOfW (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (w : Fin 3 ⊕ Fin 3 → F) : k328r8p_ppart F (k328r8p_vecOfW F w) = 0 := by
  funext i; fin_cases i <;> rfl

private theorem k328r8p_wpart_vecOfP (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (p : Fin 2 → F) : k328r8p_wpart F (k328r8p_vecOfP F p) = 0 := by
  ext a; rcases a with a | a <;> rfl

private theorem k328r8p_ppart_vecOfP (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (p : Fin 2 → F) : k328r8p_ppart F (k328r8p_vecOfP F p) = p := by
  funext i; fin_cases i <;> rfl

private theorem k328r8p_planeBlock_vecOfW (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F) (w : Fin 3 ⊕ Fin 3 → F) :
    k328r8p_planeBlock F D *ᵥ k328r8p_vecOfW F w = k328r8p_vecOfW F w := by
  funext k
  rcases k with i | i | i <;> fin_cases i <;>
    simp [k328r8p_planeBlock, k328r8p_vecOfW, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr]

private theorem k328r8p_planeBlock_vecOfP (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (D : Matrix (Fin 2) (Fin 2) F) (p : Fin 2 → F) :
    k328r8p_planeBlock F D *ᵥ k328r8p_vecOfP F p = k328r8p_vecOfP F (D *ᵥ p) := by
  funext k
  rcases k with i | i | i <;> fin_cases i <;>
    simp [k328r8p_planeBlock, k328r8p_vecOfP, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr]

private theorem k328r8p_blockDiag_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (DX DY : Matrix (Fin 2) (Fin 2) F) :
    (k328r8p_block F X * k328r8p_planeBlock F DX) *
      (k328r8p_block F Y * k328r8p_planeBlock F DY) =
    k328r8p_block F (X * Y) * k328r8p_planeBlock F (DX * DY) := by
  calc (k328r8p_block F X * k328r8p_planeBlock F DX) *
        (k328r8p_block F Y * k328r8p_planeBlock F DY)
      = k328r8p_block F X * (k328r8p_planeBlock F DX * k328r8p_block F Y) *
          k328r8p_planeBlock F DY := by noncomm_ring
    _ = k328r8p_block F X * (k328r8p_block F Y * k328r8p_planeBlock F DX) *
          k328r8p_planeBlock F DY := by
          rw [k328r8p_block_planeBlock_commute F Y DX]
    _ = k328r8p_block F (X * Y) * k328r8p_planeBlock F (DX * DY) := by
          rw [show k328r8p_block F X *
                (k328r8p_block F Y * k328r8p_planeBlock F DX) *
                k328r8p_planeBlock F DY =
              k328r8p_block F X * k328r8p_block F Y *
                (k328r8p_planeBlock F DX * k328r8p_planeBlock F DY) by noncomm_ring,
            ← k328r8p_block_mul, ← k328r8p_planeBlock_mul]

private theorem k328r8p_wBlock_blockDiag_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (DX DY : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_wBlock F ((k328r8p_block F X * k328r8p_planeBlock F DX) *
      (k328r8p_block F Y * k328r8p_planeBlock F DY)) = X * Y := by
  rw [k328r8p_blockDiag_mul, k328r8p_wBlock_block_mul_planeBlock]

private theorem k328r8p_pBlock_blockDiag_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (DX DY : Matrix (Fin 2) (Fin 2) F) :
    k328r8p_pBlock F ((k328r8p_block F X * k328r8p_planeBlock F DX) *
      (k328r8p_block F Y * k328r8p_planeBlock F DY)) = DX * DY := by
  rw [k328r8p_blockDiag_mul, k328r8p_pBlock_block_mul_planeBlock]

private theorem k328r8p_decomp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0)
    (hα : α ^ 2 + α = 1 + c / b ^ 2) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α))
    (g : GL k328r8p_Ix F) (hg : g * z₀ = z₀ * g)
    (hiso : g ∈ k328r8p_O b c) :
    ∃ (B : GL (Fin 3) (QuadraticAlgebra F 1 1)) (D : GL (Fin 2) F),
      B ∈ k328r8p_GU F ∧
      (∀ p : Fin 2 → F,
        ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 0 * ((D : Matrix (Fin 2) (Fin 2) F) *ᵥ p) 1 =
          p 0 * p 1) ∧
      (g : Matrix k328r8p_Ix k328r8p_Ix F) =
        k328r8p_ιMat F b c α hF hb (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) *
          k328r8p_δMat F b c α hF hb (D : Matrix (Fin 2) (Fin 2) F) := by
  have hQzP := k328r8p_Qmat_zmat_Pmat F hF b c α hb hα z₀ hz
  have hgmat : (g : Matrix k328r8p_Ix k328r8p_Ix F) *
      (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) =
      (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
      (g : Matrix k328r8p_Ix k328r8p_Ix F) := by
    rw [← Units.val_mul, ← Units.val_mul, hg]
  have hPMQ : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) =
      k328r8p_Pmat F b c α * k328r8p_Mz F * k328r8p_Qmat F b c α := by
    calc (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) =
        (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) *
          (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
          (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) := by
          rw [k328r8p_Pmat_mul_Qmat F hF b c α hb]; simp
      _ = k328r8p_Pmat F b c α * (k328r8p_Qmat F b c α *
          (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α) *
          k328r8p_Qmat F b c α := by noncomm_ring
      _ = k328r8p_Pmat F b c α * k328r8p_Mz F * k328r8p_Qmat F b c α := by rw [hQzP]
  set g' : GL k328r8p_Ix F := Units.map (k328r8p_conjMat F b c α hF hb) g with hg'def
  have hg'mat : (g' : Matrix k328r8p_Ix k328r8p_Ix F) =
      k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
        k328r8p_Pmat F b c α := rfl
  have hg'Mz : (g' : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Mz F =
      k328r8p_Mz F * (g' : Matrix k328r8p_Ix k328r8p_Ix F) := by
    rw [hg'mat]
    calc k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
            k328r8p_Pmat F b c α * k328r8p_Mz F
        = k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
            k328r8p_Pmat F b c α * k328r8p_Mz F *
            (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) := by
            rw [k328r8p_Qmat_mul_Pmat F hF b c α hb, Matrix.mul_one]
      _ = k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
            (k328r8p_Pmat F b c α * k328r8p_Mz F * k328r8p_Qmat F b c α) *
            k328r8p_Pmat F b c α := by noncomm_ring
      _ = k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
            (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α := by rw [← hPMQ]
      _ = k328r8p_Qmat F b c α * (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
            (g : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α := by
            calc k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
                  (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α
                = k328r8p_Qmat F b c α *
                    ((g : Matrix k328r8p_Ix k328r8p_Ix F) *
                      (z₀ : Matrix k328r8p_Ix k328r8p_Ix F)) * k328r8p_Pmat F b c α := by
                    noncomm_ring
              _ = k328r8p_Qmat F b c α *
                    ((z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
                      (g : Matrix k328r8p_Ix k328r8p_Ix F)) * k328r8p_Pmat F b c α := by rw [← hgmat]
              _ = k328r8p_Qmat F b c α * (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) *
                    (g : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α := by
                    noncomm_ring
      _ = k328r8p_Mz F * (k328r8p_Qmat F b c α *
            (g : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α) := by
            rw [hPMQ]
            rw [show k328r8p_Qmat F b c α *
                  (k328r8p_Pmat F b c α * k328r8p_Mz F * k328r8p_Qmat F b c α) *
                  (g : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α =
                (k328r8p_Qmat F b c α * k328r8p_Pmat F b c α) * k328r8p_Mz F *
                  (k328r8p_Qmat F b c α * (g : Matrix k328r8p_Ix k328r8p_Ix F) *
                    k328r8p_Pmat F b c α) by noncomm_ring,
              k328r8p_Qmat_mul_Pmat F hF b c α hb, Matrix.one_mul]
  have hbd : (g' : Matrix k328r8p_Ix k328r8p_Ix F) =
      k328r8p_block F (k328r8p_wBlock F (g' : Matrix k328r8p_Ix k328r8p_Ix F)) *
        k328r8p_planeBlock F (k328r8p_pBlock F (g' : Matrix k328r8p_Ix k328r8p_Ix F)) :=
    k328r8p_blockDiag F _ hg'Mz
  set A6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    k328r8p_wBlock F (g' : Matrix k328r8p_Ix k328r8p_Ix F) with hA6def
  set D2 : Matrix (Fin 2) (Fin 2) F :=
    k328r8p_pBlock F (g' : Matrix k328r8p_Ix k328r8p_Ix F) with hD2def
  have hA6Mz : A6 * k328r8p_Mω F = k328r8p_Mω F * A6 := by
    rw [hA6def]
    exact k328r8p_wBlock_comm_Mω F _ hg'Mz
  have hhMz : ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Mz F =
      k328r8p_Mz F * ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) := by
    have h1 : ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) *
        (g' : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (g' : Matrix k328r8p_Ix k328r8p_Ix F) *
        ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e1 := congrArg (fun M : Matrix k328r8p_Ix k328r8p_Ix F =>
      ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) * M) hg'Mz
    simp only [← Matrix.mul_assoc] at e1
    rw [h1, Matrix.one_mul] at e1
    have e2 : k328r8p_Mz F * ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) =
        (((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) *
          k328r8p_Mz F * (g' : Matrix k328r8p_Ix k328r8p_Ix F)) *
          ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) :=
      congrArg (fun M => M *
        ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F)) e1
    rw [Matrix.mul_assoc, h2, Matrix.mul_one] at e2
    exact e2.symm
  have hbdh : ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) =
      k328r8p_block F (k328r8p_wBlock F
        ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F)) *
        k328r8p_planeBlock F (k328r8p_pBlock F
          ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F)) :=
    k328r8p_blockDiag F _ hhMz
  set A6' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    k328r8p_wBlock F ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) with hA6'def
  set D2' : Matrix (Fin 2) (Fin 2) F :=
    k328r8p_pBlock F ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) with hD2'def
  have hA6'Mz : A6' * k328r8p_Mω F = k328r8p_Mω F * A6' := by
    rw [hA6'def]
    exact k328r8p_wBlock_comm_Mω F _ hhMz
  have hAA : A6 * A6' = 1 := by
    have e : (k328r8p_block F A6 * k328r8p_planeBlock F D2) *
        (k328r8p_block F A6' * k328r8p_planeBlock F D2') = 1 := by
      have e0 : (g' : Matrix k328r8p_Ix k328r8p_Ix F) *
          ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rwa [hbd, hbdh] at e0
    have e2 := congrArg (fun M => k328r8p_wBlock F M) e
    rw [k328r8p_wBlock_one, k328r8p_wBlock_blockDiag_mul] at e2
    exact e2
  have hA'A : A6' * A6 = 1 := by
    have e : (k328r8p_block F A6' * k328r8p_planeBlock F D2') *
        (k328r8p_block F A6 * k328r8p_planeBlock F D2) = 1 := by
      have e0 : ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) *
          (g' : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rwa [hbd, hbdh] at e0
    have e2 := congrArg (fun M => k328r8p_wBlock F M) e
    rw [k328r8p_wBlock_one, k328r8p_wBlock_blockDiag_mul] at e2
    exact e2
  have hDD : D2 * D2' = 1 := by
    have e : (k328r8p_block F A6 * k328r8p_planeBlock F D2) *
        (k328r8p_block F A6' * k328r8p_planeBlock F D2') = 1 := by
      have e0 : (g' : Matrix k328r8p_Ix k328r8p_Ix F) *
          ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rwa [hbd, hbdh] at e0
    have e2 := congrArg (fun M => k328r8p_pBlock F M) e
    rw [k328r8p_pBlock_one, k328r8p_pBlock_blockDiag_mul] at e2
    exact e2
  have hD'D : D2' * D2 = 1 := by
    have e : (k328r8p_block F A6' * k328r8p_planeBlock F D2') *
        (k328r8p_block F A6 * k328r8p_planeBlock F D2) = 1 := by
      have e0 : ((g'⁻¹ : GL k328r8p_Ix F) : Matrix k328r8p_Ix k328r8p_Ix F) *
          (g' : Matrix k328r8p_Ix k328r8p_Ix F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rwa [hbd, hbdh] at e0
    have e2 := congrArg (fun M => k328r8p_pBlock F M) e
    rw [k328r8p_pBlock_one, k328r8p_pBlock_blockDiag_mul] at e2
    exact e2
  have hA6rho : k328r8p_rhoMat F (k328r8p_ofBlocks F A6.toBlocks₁₁ A6.toBlocks₁₂) = A6 :=
    (k328r8p_eq_rho_of_commute F A6 hA6Mz).symm
  have hA6'rho : k328r8p_rhoMat F (k328r8p_ofBlocks F A6'.toBlocks₁₁ A6'.toBlocks₁₂) = A6' :=
    (k328r8p_eq_rho_of_commute F A6' hA6'Mz).symm
  let B : GL (Fin 3) (QuadraticAlgebra F 1 1) :=
    ⟨k328r8p_ofBlocks F A6.toBlocks₁₁ A6.toBlocks₁₂,
      k328r8p_ofBlocks F A6'.toBlocks₁₁ A6'.toBlocks₁₂, by
        apply k328r8p_rhoMat_injective F
        rw [map_mul, map_one, hA6rho, hA6'rho, hAA],
      by
        apply k328r8p_rhoMat_injective F
        rw [map_mul, map_one, hA6rho, hA6'rho, hA'A]⟩
  let D : GL (Fin 2) F := ⟨D2, D2', hDD, hD'D⟩
  have hBmat : k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) = A6 := by
    rw [show (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) =
        k328r8p_ofBlocks F A6.toBlocks₁₁ A6.toBlocks₁₂ from rfl, hA6rho]
  have hg'N : ∀ x, k328r8p_N F ((g' : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ x) =
      k328r8p_N F x := by
    intro x
    have hiso' := (k328r8p_mem_O b c g).1 hiso
    calc k328r8p_N F ((g' : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ x)
        = k328r8p_N F (k328r8p_Qmat F b c α *ᵥ
            ((g : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ (k328r8p_Pmat F b c α *ᵥ x))) := by
            rw [hg'mat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = StatedQuadMinus 4 F b c (k328r8p_Pmat F b c α *ᵥ
            (k328r8p_Qmat F b c α *ᵥ
              ((g : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ (k328r8p_Pmat F b c α *ᵥ x)))) :=
            (k328r8p_Q_Pmat F hF b c α hb hα _).symm
      _ = StatedQuadMinus 4 F b c
            ((g : Matrix k328r8p_Ix k328r8p_Ix F) *ᵥ (k328r8p_Pmat F b c α *ᵥ x)) := by
            rw [Matrix.mulVec_mulVec, k328r8p_Pmat_mul_Qmat F hF b c α hb, Matrix.one_mulVec]
      _ = StatedQuadMinus 4 F b c (k328r8p_Pmat F b c α *ᵥ x) := hiso' _
      _ = k328r8p_N F x := k328r8p_Q_Pmat F hF b c α hb hα x
  have hA6N : ∀ w : Fin 3 ⊕ Fin 3 → F, k328r8p_N6 F (A6 *ᵥ w) = k328r8p_N6 F w := by
    intro w
    have hx := hg'N (k328r8p_vecOfW F w)
    rw [hbd] at hx
    rw [← Matrix.mulVec_mulVec] at hx
    rw [k328r8p_planeBlock_vecOfW] at hx
    simp only [k328r8p_N_eq, k328r8p_block_wpart, k328r8p_block_ppart,
      k328r8p_wpart_vecOfW, k328r8p_ppart_vecOfW] at hx
    simpa [k328r8p_N6] using hx
  have hDN : ∀ p : Fin 2 → F, ((D2 *ᵥ p) 0) * ((D2 *ᵥ p) 1) = p 0 * p 1 := by
    intro p
    have hx := hg'N (k328r8p_vecOfP F p)
    rw [hbd] at hx
    rw [← Matrix.mulVec_mulVec] at hx
    rw [k328r8p_planeBlock_vecOfP] at hx
    simp only [k328r8p_N_eq, k328r8p_block_wpart, k328r8p_block_ppart,
      k328r8p_wpart_vecOfP, k328r8p_ppart_vecOfP, Matrix.mulVec_zero] at hx
    simpa [k328r8p_N6] using hx
  refine ⟨B, D, ?_, ?_, ?_⟩
  · rw [k328r8p_GU, Subgroup.mem_comap]
    refine k328r8p_mem_statedSp_of_preserves_N6 F hF (k328r8p_rho F B) fun x => ?_
    rw [show (k328r8p_rho F B : GL (Fin 3 ⊕ Fin 3) F) =
        k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) from rfl,
      hBmat]
    exact hA6N x
  · intro p
    exact hDN p
  · have hP : (g : Matrix k328r8p_Ix k328r8p_Ix F) =
        k328r8p_Pmat F b c α * (g' : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Qmat F b c α := by
      rw [hg'mat]
      calc (g : Matrix k328r8p_Ix k328r8p_Ix F)
          = (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) *
              (g : Matrix k328r8p_Ix k328r8p_Ix F) *
              (k328r8p_Pmat F b c α * k328r8p_Qmat F b c α) := by
              rw [k328r8p_Pmat_mul_Qmat F hF b c α hb]; simp
        _ = k328r8p_Pmat F b c α * (k328r8p_Qmat F b c α *
              (g : Matrix k328r8p_Ix k328r8p_Ix F) * k328r8p_Pmat F b c α) *
              k328r8p_Qmat F b c α := by noncomm_ring
    have hblockA6 : k328r8p_block F A6 =
        k328r8p_block F
          (k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) := by
      rw [hBmat]
    have hexp : k328r8p_ιMat F b c α hF hb
          (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) *
          k328r8p_δMat F b c α hF hb (D : Matrix (Fin 2) (Fin 2) F) =
        k328r8p_Pmat F b c α * (k328r8p_block F
            (k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) *
          k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F)) * k328r8p_Qmat F b c α := by
      show (k328r8p_Pmat F b c α * k328r8p_block F
              (k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) *
              k328r8p_Qmat F b c α) *
            (k328r8p_Pmat F b c α * k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F) *
              k328r8p_Qmat F b c α) = _
      rw [k328r8p_conj_mul F b c α hF hb
          (k328r8p_block F
            (k328r8p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))))
          (k328r8p_planeBlock F (D : Matrix (Fin 2) (Fin 2) F))]
    rw [hP, hbd, hblockA6, hexp]

private theorem k328r8p_comm_le (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ ≤ k328r8p_Y F b c α hF hb := by
  obtain ⟨χ, hχΩ, hχr⟩ := k328r8p_exists_chi F b c hbc
  let Φ : GL (Fin 3) (QuadraticAlgebra F 1 1) × GL (Fin 2) F →* GL k328r8p_Ix F :=
    (k328r8p_ι F b c α hF hb).noncommCoprod (k328r8p_δ F b c α hF hb)
      (k328r8p_ι_comm_δ F b c α hF hb)
  have hΦ : ∀ (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) (D : GL (Fin 2) F),
      Φ (A, D) = k328r8p_ι F b c α hF hb A * k328r8p_δ F b c α hF hb D := fun A D => rfl
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  obtain ⟨hg₁Ω, hg₁C⟩ := Subgroup.mem_inf.mp hg₁
  obtain ⟨hg₂Ω, hg₂C⟩ := Subgroup.mem_inf.mp hg₂
  have hg₁comm : g₁ * z₀ = z₀ * g₁ := Subgroup.mem_centralizer_singleton_iff.mp hg₁C
  have hg₂comm : g₂ * z₀ = z₀ * g₂ := Subgroup.mem_centralizer_singleton_iff.mp hg₂C
  obtain ⟨B₁, D₁, hB₁, hD₁, hg₁eq⟩ :=
    k328r8p_decomp F hF b c α hb hα z₀ hz g₁ hg₁comm (k328r8p_Omega_le_O b c hg₁Ω)
  obtain ⟨B₂, D₂, hB₂, hD₂, hg₂eq⟩ :=
    k328r8p_decomp F hF b c α hb hα z₀ hz g₂ hg₂comm (k328r8p_Omega_le_O b c hg₂Ω)
  have hD₁O : k328r8p_δ F b c α hF hb D₁ ∈ k328r8p_O b c :=
    k328r8p_δ_mem_O F hF b c α hb hα D₁ hD₁
  have hD₂O : k328r8p_δ F b c α hF hb D₂ ∈ k328r8p_O b c :=
    k328r8p_δ_mem_O F hF b c α hb hα D₂ hD₂
  have hι₁O : k328r8p_ι F b c α hF hb B₁ ∈ k328r8p_O b c :=
    (k328r8p_mem_O b c _).2 fun v => k328r8p_iota_isometry F hF b c α hb hα B₁ hB₁ v
  have hι₂O : k328r8p_ι F b c α hF hb B₂ ∈ k328r8p_O b c :=
    (k328r8p_mem_O b c _).2 fun v => k328r8p_iota_isometry F hF b c α hb hα B₂ hB₂ v
  have hg₁O : g₁ ∈ k328r8p_O b c := k328r8p_Omega_le_O b c hg₁Ω
  have hg₂O : g₂ ∈ k328r8p_O b c := k328r8p_Omega_le_O b c hg₂Ω
  have hgeq₁ : g₁ = k328r8p_ι F b c α hF hb B₁ * k328r8p_δ F b c α hF hb D₁ := by
    apply Units.ext
    rw [Units.val_mul]
    exact hg₁eq
  have hgeq₂ : g₂ = k328r8p_ι F b c α hF hb B₂ * k328r8p_δ F b c α hF hb D₂ := by
    apply Units.ext
    rw [Units.val_mul]
    exact hg₂eq
  have hχι₁ : χ ⟨k328r8p_ι F b c α hF hb B₁, hι₁O⟩ = 1 :=
    k328r8p_chi_ι F hF b c α hb hα χ hχΩ B₁ hB₁
  have hχι₂ : χ ⟨k328r8p_ι F b c α hF hb B₂, hι₂O⟩ = 1 :=
    k328r8p_chi_ι F hF b c α hb hα χ hχΩ B₂ hB₂
  have hχδ₁ : χ ⟨k328r8p_δ F b c α hF hb D₁, hD₁O⟩ = 1 := by
    have hsub : (⟨g₁, hg₁O⟩ : k328r8p_O b c) =
        ⟨k328r8p_ι F b c α hF hb B₁, hι₁O⟩ * ⟨k328r8p_δ F b c α hF hb D₁, hD₁O⟩ := by
      apply Subtype.ext
      exact hgeq₁
    have h := hχΩ ⟨g₁, hg₁O⟩ hg₁Ω
    rw [hsub, map_mul, hχι₁, one_mul] at h
    exact h
  have hχδ₂ : χ ⟨k328r8p_δ F b c α hF hb D₂, hD₂O⟩ = 1 := by
    have hsub : (⟨g₂, hg₂O⟩ : k328r8p_O b c) =
        ⟨k328r8p_ι F b c α hF hb B₂, hι₂O⟩ * ⟨k328r8p_δ F b c α hF hb D₂, hD₂O⟩ := by
      apply Subtype.ext
      exact hgeq₂
    have h := hχΩ ⟨g₂, hg₂O⟩ hg₂Ω
    rw [hsub, map_mul, hχι₂, one_mul] at h
    exact h
  have hD₁diag := k328r8p_D_diag F hF b c α hb hα χ hχΩ hχr D₁ hD₁ hχδ₁
  have hD₂diag := k328r8p_D_diag F hF b c α hb hα χ hχΩ hχr D₂ hD₂ hχδ₂
  have hDcomm : D₁ * D₂ = D₂ * D₁ := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hD₁diag.1, hD₁diag.2.1, hD₂diag.1,
        hD₂diag.2.1]
    all_goals ring
  have hpair : ⁅(B₁, D₁), (B₂, D₂)⁆ = (⁅B₁, B₂⁆, (1 : GL (Fin 2) F)) := by
    apply Prod.ext <;> simp [commutatorElement_def, hDcomm]
  rw [hgeq₁, hgeq₂, ← hΦ, ← hΦ, ← map_commutatorElement, hpair, hΦ, map_one, mul_one]
  exact Subgroup.mem_map_of_mem _
    ((k328r8p_commutator_GU_eq F hF).symm ▸ Subgroup.commutator_mem_commutator hB₁ hB₂)

private theorem k328r8p_stdComp_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)]
    (hF : Fintype.card F = 8) (b c α : F) (hb : b ≠ 0) (hα : α ^ 2 + α = 1 + c / b ^ 2)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (z₀ : GL k328r8p_Ix F)
    (hz : (z₀ : Matrix k328r8p_Ix k328r8p_Ix F) = ofColumns F (k328r8p_zcol F b c α)) :
    stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ = k328r8p_Y F b c α hF hb :=
  le_antisymm (k328r8p_comm_le F hF b c α hb hα hbc z₀ hz)
    (k328r8p_Y_le_stdComp F b c α hF hb hα z₀ hz)

private theorem k328r8p_subgroupOf_eq {M : Type} [Group M] {H : Subgroup M} {z₀ : M}
    (hz₀ : z₀ ∈ H) :
    (stdComp H z₀).subgroupOf H =
      ⁅Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}, Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}⁆ := by
  have hC : (Subgroup.centralizer {(⟨z₀, hz₀⟩ : H)}).map H.subtype =
      H ⊓ Subgroup.centralizer {z₀} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    · rintro ⟨hyH, hyc⟩
      exact ⟨⟨y, hyH⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyc)), rfl⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, hC, Subgroup.map_subgroupOf_eq_of_le (stdComp_le H z₀), stdComp]

private theorem k328r8p_subnormal {M : Type} [Group M] (C : Subgroup M) :
    ((⁅C, C⁆ : Subgroup M).subgroupOf C).IsSubnormal := by
  have h : (⁅C, C⁆ : Subgroup M).subgroupOf C = _root_.commutator ↥C := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [h]
  exact Subgroup.Normal.isSubnormal inferInstance

private theorem k328r8p_model (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    CFSG.Open.IsQuasisimple ↥(k328r8p_SU F) ∧
      Nat.card (Subgroup.center ↥(k328r8p_SU F)) = 3 ∧
      LieModel (↥(k328r8p_SU F) ⧸ Subgroup.center ↥(k328r8p_SU F)) .PSU 3 2 3 := by
  have : Finite (QuadraticAlgebra F 1 1) :=
    Nat.finite_of_card_ne_zero (by rw [k328r8p_card_L F hF]; norm_num)
  have hcardL : Nat.card (QuadraticAlgebra F 1 1) = (2 ^ 3) ^ 2 := by
    rw [k328r8p_card_L F hF]; norm_num
  have hqsc := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := QuadraticAlgebra F 1 1) (p := 2) (f := 3) hcardL (n := 3) le_rfl (by norm_num)
  have hqsc' : CFSG.IsQuasisimple ↥(k328r8p_SU F) ∧
      Subgroup.center ↥(k328r8p_SU F) =
        (StatedScalars (Fin 3) (QuadraticAlgebra F 1 1)).subgroupOf (k328r8p_SU F) := by
    simpa only [k328r8p_SU] using hqsc
  have hqs : CFSG.Open.IsQuasisimple ↥(k328r8p_SU F) :=
    (fun h => ⟨h.1.1, h.2.1⟩ : CFSG.IsQuasisimple ↥(k328r8p_SU F) →
      CFSG.Open.IsQuasisimple ↥(k328r8p_SU F)) hqsc'.1
  have hcenter : Nat.card (Subgroup.center ↥(k328r8p_SU F)) = 3 := by
    rw [hqsc'.2]
    obtain ⟨-, -, hc⟩ := CFSG.LinearGroups.unitary_scalar_kernel (K := QuadraticAlgebra F 1 1)
      (p := 2) (f := 3) Nat.prime_two hcardL (n := 3) (by norm_num)
    rw [hc]; norm_num
  have hmodel : LieModel (↥(k328r8p_SU F) ⧸ Subgroup.center ↥(k328r8p_SU F)) .PSU 3 2 3 := by
    refine Or.inl ⟨by decide, ?_⟩
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩,
      QuadraticAlgebra F 1 1, inferInstance, inferInstance, hcardL, ?_⟩
    refine ⟨?_⟩
    exact QuotientGroup.congr (Subgroup.center ↥(k328r8p_SU F))
      ((StatedScalars (Fin 3) (QuadraticAlgebra F 1 1)).subgroupOf (k328r8p_SU F))
      (MulEquiv.refl _) (by simpa using hqsc'.2)
  exact ⟨hqs, hcenter, hmodel⟩

private theorem k328r8p_pos_of {M : Type} [Group M] [Finite M] {H : Subgroup M} {z₀ : M}
    (hz₀ : z₀ ∈ H) (hord : orderOf z₀ = 3) (hzX : z₀ ∈ stdComp H z₀)
    (hqs : CFSG.Open.IsQuasisimple ↥(stdComp H z₀))
    (hcen : Nat.card (Subgroup.center ↥(stdComp H z₀)) = 3)
    (hlie : LieModel (↥(stdComp H z₀) ⧸ Subgroup.center ↥(stdComp H z₀)) .PSU 3 2 3) :
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) ((stdComp H z₀).subgroupOf H) := by
  let eX : ↥((stdComp H z₀).subgroupOf H) ≃* ↥(stdComp H z₀) :=
    Subgroup.subgroupOfEquivOfLe (stdComp_le H z₀)
  refine ⟨?_, Subgroup.zpowers_le.2 hzX, ?_, ?_,
    isQuasisimple_of_mulEquiv' eX.symm hqs, ?_,
    Or.inr (LieModel.of_mulEquiv (QuotientGroup.congr (Subgroup.center ↥(stdComp H z₀))
      (Subgroup.center ↥((stdComp H z₀).subgroupOf H)) eX.symm
      (Subgroup.map_center_eq eX.symm)) hlie)⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hord
  · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, k328r8p_subgroupOf_eq hz₀]
    exact Subgroup.commutator_le_self _
  · rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, k328r8p_subgroupOf_eq hz₀]
    exact k328r8p_subnormal _
  · rw [← hcen]
    exact Nat.card_congr (Subgroup.centerCongr eX).toEquiv

theorem row8_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    PosLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  intro e f u v z₀ t₀ hz ht
  have he : e = fun i => bv F (Sum.inl i) := rfl
  have hf : f = fun i => bv F (Sum.inr (Sum.inl i)) := rfl
  have hu : u = bv F (Sum.inr (Sum.inr 0)) := rfl
  have hv : v = bv F (Sum.inr (Sum.inr 1)) := rfl
  have hz' : z₀ = ofColumns F (k328r8p_zcol F b c α) := by
    simp only [hz, he, hf, hu, hv]
    congr 1
    exact k328r8p_statement_zcol F b c α
  by_cases hb : b = 0
  · intro hzO
    exact absurd (k328r8p_Omega_le_O b c hzO)
      (k328r8p_not_mem_O_of_b_zero F hF b c α hb hbc hα z₀ hz')
  · intro hzO
    let : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
    have hstd : stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀ = k328r8p_Y F b c α hF hb :=
      k328r8p_stdComp_eq F hF b c α hb hα hbc z₀ hz'
    let eY : ↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) ≃* ↥(k328r8p_SU F) :=
      (MulEquiv.subgroupCongr hstd).trans
        (((k328r8p_SU F).equivMapOfInjective (k328r8p_ι F b c α hF hb)
          (k328r8p_ι_injective F b c α hF hb)).symm)
    obtain ⟨hqs, hcen, hlie⟩ := k328r8p_model F hF
    have hqs' : CFSG.Open.IsQuasisimple
        ↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) :=
      isQuasisimple_of_mulEquiv' eY.symm hqs
    have hcen' : Nat.card (Subgroup.center
        ↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀)) = 3 :=
      (Nat.card_congr (Subgroup.centerCongr eY).toEquiv).trans hcen
    have hlie' : LieModel (↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) ⧸
        Subgroup.center ↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀)) .PSU 3 2 3 :=
      LieModel.of_mulEquiv
        (QuotientGroup.congr
          (Subgroup.center ↥(stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀))
          (Subgroup.center ↥(k328r8p_SU F)) eY (Subgroup.map_center_eq eY)).symm hlie
    exact k328r8p_pos_of hzO
      (k328r8p_orderOf_z0 F hF b c α hb hα z₀ hz')
      (by rw [hstd]; exact k328r8p_z0_mem_Y F b c α hF hb hα z₀ hz')
      hqs' hcen' hlie'

theorem row8_card_stdComp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (α : F) (hα : α ^ 2 + α = 1 + c / b ^ 2) :
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    Nat.card (stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) = 16547328 := by
  intro e f u v z₀ hz
  have he : e = fun i => bv F (Sum.inl i) := rfl
  have hf : f = fun i => bv F (Sum.inr (Sum.inl i)) := rfl
  have hu : u = bv F (Sum.inr (Sum.inr 0)) := rfl
  have hv : v = bv F (Sum.inr (Sum.inr 1)) := rfl
  have hz' : z₀ = ofColumns F (k328r8p_zcol F b c α) := by
    simp only [hz, he, hf, hu, hv]
    congr 1
    exact k328r8p_statement_zcol F b c α
  have hb : b ≠ 0 := by
    rintro rfl
    have hchar : CharP F 2 := k328r8p_charP_two F hF
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    refine hbc s ?_
    rw [hs]
    ring_nf
    rw [h2, mul_zero]
  let : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r8p_fact F hF
  rw [k328r8p_stdComp_eq F hF b c α hb hα hbc z₀ hz']
  have hY : Nat.card ↥(k328r8p_Y F b c α hF hb) = Nat.card ↥(k328r8p_SU F) := by
    rw [k328r8p_Y]
    exact Subgroup.card_map_of_injective (k328r8p_ι_injective F b c α hF hb)
  rw [hY]
  have hSU : Nat.card ↥(k328r8p_SU F) = 16547328 := by
    have : Finite (QuadraticAlgebra F 1 1) :=
      Nat.finite_of_card_ne_zero (by rw [k328r8p_card_L F hF]; norm_num)
    obtain ⟨-, hcen, hlie⟩ := k328r8p_model F hF
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(k328r8p_SU F))
    rw [hcen] at hmul
    rw [hmul, CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (hlie.statedClassicalModel (by decide))]
  exact hSU

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
