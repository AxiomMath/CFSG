module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.LinearAlgebra.AnisotropicBinaryPlane
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.Blueprint (LieModel)
open QuadraticAlgebra
open scoped Matrix

private theorem k328r7p_charP_two (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : CharP F 2 := by
  have : Finite F := Finite.of_fintype F
  obtain ⟨p, hp, n, hp', hcard⟩ := FiniteField.card' (K := F)
  have : Fact p.Prime := ⟨hp'⟩
  have h1 : p ^ (n : ℕ) = 2 ^ 3 := by rw [← hcard, hF]; norm_num
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 3 := by rw [← h1]; exact dvd_pow_self p n.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 (hp'.dvd_of_dvd_pow hdvd)
  subst hp2; exact hp

private theorem k328r7p_aniso (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    ∀ x y : F, x ^ 2 + 1 * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  have : CharP F 2 := k328r7p_charP_two F hF
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

private theorem k328r7p_fact (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := by
  have : CharP F 2 := k328r7p_charP_two F hF
  refine ⟨fun r h => ?_⟩
  have h0 : r ^ 2 + 1 * r * 1 + 1 ^ 2 = 0 := by
    rw [h]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc (1 + 1 * r) + 1 * r * 1 + 1 ^ 2 = (2 : F) * (1 + r) := by ring
      _ = 0 := by rw [h2, zero_mul]
  exact one_ne_zero (k328r7p_aniso F hF r 1 h0).2

private theorem k328r7p_card_L (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : Nat.card (QuadraticAlgebra F 1 1) = 64 := by
  have : CharP F 2 := k328r7p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    CFSG.LinearAlgebra.anisotropic_binary_plane_norm_field (K := F) (ε := 1) (k328r7p_aniso F hF)
  have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  have := (hlast 3 (by norm_num) (by rw [hF8]; norm_num)).1
  simpa using this

private theorem k328r7p_star_pow (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z : QuadraticAlgebra F 1 1) : star z = z ^ 8 := by
  have : CharP F 2 := k328r7p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    CFSG.LinearAlgebra.anisotropic_binary_plane_norm_field (K := F) (ε := 1) (k328r7p_aniso F hF)
  have hF8 : Nat.card F = 8 := by rw [Nat.card_eq_fintype_card, hF]
  exact (hlast 3 (by norm_num) (by rw [hF8]; norm_num)).2 z

private theorem k328r7p_re_sum (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} (s : Finset ι) (f : ι → QuadraticAlgebra F 1 1) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, QuadraticAlgebra.re_add, ih]

private theorem k328r7p_im_sum (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} (s : Finset ι) (f : ι → QuadraticAlgebra F 1 1) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, QuadraticAlgebra.im_add, ih]

private theorem k328r7p_map_re_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    (A * B).map QuadraticAlgebra.re =
      A.map QuadraticAlgebra.re * B.map QuadraticAlgebra.re +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [k328r7p_re_sum]
  simp only [QuadraticAlgebra.re_mul]
  rw [Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; ring

private theorem k328r7p_map_im_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    (A * B).map QuadraticAlgebra.im =
      A.map QuadraticAlgebra.re * B.map QuadraticAlgebra.im +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.re +
      A.map QuadraticAlgebra.im * B.map QuadraticAlgebra.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [k328r7p_im_sum]
  simp only [QuadraticAlgebra.im_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; ring

private def k328r7p_rhoMat (F : Type) [Field F] [Fintype F] [DecidableEq F] :
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
    rw [k328r7p_map_re_mul, k328r7p_map_im_mul, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

private def k328r7p_rho (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    GL (Fin 3) (QuadraticAlgebra F 1 1) →* GL (Fin 3 ⊕ Fin 3) F :=
  Units.map (k328r7p_rhoMat F)

private theorem k328r7p_rho_apply (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    ((k328r7p_rho F A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
          QuadraticAlgebra.re)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re +
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im) :=
  rfl

private theorem k328r7p_rho_injective (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Function.Injective (k328r7p_rho F) := by
  intro A B h
  apply Units.ext
  have h' : k328r7p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) =
      k328r7p_rhoMat F (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :=
    congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
      (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) h
  have h1 : (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re =
      (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re :=
    (Matrix.fromBlocks_inj.mp h').1
  have h2 : (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im =
      (B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im :=
    (Matrix.fromBlocks_inj.mp h').2.1
  ext i j
  · simpa [Matrix.map_apply] using congrFun (congrFun h1 i) j
  · simpa [Matrix.map_apply] using congrFun (congrFun h2 i) j

private def k328r7p_ofBlocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) :=
  Matrix.of fun i j => (⟨P i j, Q i j⟩ : QuadraticAlgebra F 1 1)

private theorem k328r7p_ofBlocks_re (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    (k328r7p_ofBlocks F P Q).map QuadraticAlgebra.re = P := by
  ext i j; rfl

private theorem k328r7p_ofBlocks_im (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    (k328r7p_ofBlocks F P Q).map QuadraticAlgebra.im = Q := by
  ext i j; rfl

private theorem k328r7p_rhoMat_injective (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Function.Injective (k328r7p_rhoMat F) := by
  intro A B h
  have h1 : A.map QuadraticAlgebra.re = B.map QuadraticAlgebra.re :=
    (Matrix.fromBlocks_inj.mp h).1
  have h2 : A.map QuadraticAlgebra.im = B.map QuadraticAlgebra.im :=
    (Matrix.fromBlocks_inj.mp h).2.1
  ext i j
  · simpa [Matrix.map_apply] using congrFun (congrFun h1 i) j
  · simpa [Matrix.map_apply] using congrFun (congrFun h2 i) j

private theorem k328r7p_eq_rho_of_commute (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (h : g * Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 * g) :
    g = k328r7p_rhoMat F (k328r7p_ofBlocks F g.toBlocks₁₁ g.toBlocks₁₂) := by
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

private noncomputable def k328r7p_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : GL (Fin 3) (QuadraticAlgebra F 1 1) :=
  letI : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  Matrix.GeneralLinearGroup.scalar (Fin 3)
    (Units.mk0 (ω : QuadraticAlgebra F 1 1) (by
      intro h
      have h' : (1 : F) = 0 := by
        simpa using congrArg QuadraticAlgebra.im h
      exact one_ne_zero h'))

private theorem k328r7p_rho_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    ((k328r7p_rho F (k328r7p_omegaUnit F hF) : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 := by
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  rw [k328r7p_rho_apply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k328r7p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, h, QuadraticAlgebra.re_omega]
  · rw [k328r7p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.one_apply, h, QuadraticAlgebra.im_omega]
  · rw [k328r7p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.one_apply, h, QuadraticAlgebra.im_omega]
  · rw [k328r7p_omegaUnit, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.one_apply, h, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

private theorem k328r7p_centralizer_eq_range (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) :
    Subgroup.centralizer ({k328r7p_rho F (k328r7p_omegaUnit F hF)} :
      Set (GL (Fin 3 ⊕ Fin 3) F)) =
      (k328r7p_rho F).range := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    have hcomm : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 =
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 *
          (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
      have h1 := hg (k328r7p_rho F (k328r7p_omegaUnit F hF)) (Set.mem_singleton _)
      have h2 := congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
        (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) h1
      rw [Units.val_mul, Units.val_mul, k328r7p_rho_omegaUnit F hF] at h2
      exact h2.symm
    have hg' := k328r7p_eq_rho_of_commute F _ hcomm
    have hginv_mem : g⁻¹ ∈ Subgroup.centralizer
        ({k328r7p_rho F (k328r7p_omegaUnit F hF)} : Set (GL (Fin 3 ⊕ Fin 3) F)) :=
      (Subgroup.centralizer _).inv_mem hg
    rw [Subgroup.mem_centralizer_iff] at hginv_mem
    have hcomm_inv : ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 =
        Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 1 1 *
          ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
      have h1 := hginv_mem (k328r7p_rho F (k328r7p_omegaUnit F hF)) (Set.mem_singleton _)
      have h2 := congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
        (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) h1
      rw [Units.val_mul, Units.val_mul, k328r7p_rho_omegaUnit F hF] at h2
      exact h2.symm
    have hginv' := k328r7p_eq_rho_of_commute F _ hcomm_inv
    set A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) :=
      k328r7p_ofBlocks F (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁
        (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂ with hA
    set B : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1) :=
      k328r7p_ofBlocks F ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁
        ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂ with hB
    have hAB : A * B = 1 := by
      apply k328r7p_rhoMat_injective F
      rw [map_mul, map_one, hA, hB, ← hg', ← hginv']
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBA : B * A = 1 := by
      apply k328r7p_rhoMat_injective F
      rw [map_mul, map_one, hA, hB, ← hg', ← hginv']
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine MonoidHom.mem_range.mpr ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    change k328r7p_rhoMat F A = (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    rw [hA]
    exact hg'.symm
  · rintro g ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hcomm : k328r7p_omegaUnit F hF * A = A * k328r7p_omegaUnit F hF := by
      rw [k328r7p_omegaUnit]
      exact Matrix.GeneralLinearGroup.scalar_commute _ A
    rw [← map_mul, ← map_mul, hcomm]

private theorem k328r7p_sp_iff_unitary_blocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
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

private theorem k328r7p_ofBlocks_self (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r7p_ofBlocks F (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im) = A := by
  ext i j <;> simp [k328r7p_ofBlocks, Matrix.map_apply]

private theorem k328r7p_map_star_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    A.map star = k328r7p_ofBlocks F (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im)
      (A.map QuadraticAlgebra.im) := by
  have : CharP F 2 := k328r7p_charP_two F hF
  ext i j
  · simp [k328r7p_ofBlocks, Matrix.map_apply]
  · simp [k328r7p_ofBlocks, Matrix.map_apply, QuadraticAlgebra.im_star, CharTwo.neg_eq]

private theorem k328r7p_rhoMat_ofBlocks (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (P Q : Matrix (Fin 3) (Fin 3) F) :
    k328r7p_rhoMat F (k328r7p_ofBlocks F P Q) = Matrix.fromBlocks P Q Q (P + Q) := by
  change Matrix.fromBlocks ((k328r7p_ofBlocks F P Q).map QuadraticAlgebra.re)
      ((k328r7p_ofBlocks F P Q).map QuadraticAlgebra.im)
      ((k328r7p_ofBlocks F P Q).map QuadraticAlgebra.im)
      ((k328r7p_ofBlocks F P Q).map QuadraticAlgebra.re +
        (k328r7p_ofBlocks F P Q).map QuadraticAlgebra.im) =
    Matrix.fromBlocks P Q Q (P + Q)
  rw [k328r7p_ofBlocks_re, k328r7p_ofBlocks_im]

private theorem k328r7p_rhoMat_transpose (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r7p_rhoMat F Aᵀ = (k328r7p_rhoMat F A)ᵀ := by
  change Matrix.fromBlocks (Aᵀ.map QuadraticAlgebra.re) (Aᵀ.map QuadraticAlgebra.im)
      (Aᵀ.map QuadraticAlgebra.im) (Aᵀ.map QuadraticAlgebra.re + Aᵀ.map QuadraticAlgebra.im) =
    (Matrix.fromBlocks (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)
      (A.map QuadraticAlgebra.im) (A.map QuadraticAlgebra.re + A.map QuadraticAlgebra.im))ᵀ
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_add, Matrix.transpose_map]

private theorem k328r7p_mem_statedSp_iff (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    k328r7p_rho F A ∈ StatedSp 3 F ↔
      ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) = 1 := by
  have : CharP F 2 := k328r7p_charP_two F hF
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  simp only [CharTwo.neg_eq]
  rw [k328r7p_rho_apply]
  rw [k328r7p_sp_iff_unitary_blocks]
  have h1 : Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.re + (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re) =
      k328r7p_rhoMat F ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star) := by
    rw [k328r7p_map_star_eq F hF, k328r7p_rhoMat_ofBlocks]
    congr 1
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h2 : Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        QuadraticAlgebra.re)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im)
        ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.re +
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map QuadraticAlgebra.im) =
      k328r7p_rhoMat F (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)) := by
    rw [← k328r7p_rhoMat_ofBlocks, k328r7p_ofBlocks_self]
  have h3 : (k328r7p_rhoMat F ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map
        star))ᵀ =
      k328r7p_rhoMat F (((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)ᵀ) :=
    (k328r7p_rhoMat_transpose F
      ((A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star)).symm
  rw [h1, h2, h3, ← map_mul]
  constructor
  · intro h
    exact k328r7p_rhoMat_injective F (by rw [map_one]; exact h)
  · intro h
    rw [h, map_one]

private def k328r7p_GU (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Subgroup (GL (Fin 3) (QuadraticAlgebra F 1 1)) :=
  Subgroup.comap (k328r7p_rho F) (StatedSp 3 F)

private abbrev k328r7p_SU (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] : Subgroup (GL (Fin 3) (QuadraticAlgebra F 1 1)) :=
  StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1)

private theorem k328r7p_statedSU_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    k328r7p_SU F =
      k328r7p_GU F ⊓ (Matrix.GeneralLinearGroup.det :
        GL (Fin 3) (QuadraticAlgebra F 1 1) →* (QuadraticAlgebra F 1 1)ˣ).ker := by
  have : CharP F 2 := k328r7p_charP_two F hF
  obtain ⟨hset, -, -⟩ := CFSG.LinearGroups.unitary_scalar_kernel (K := QuadraticAlgebra F 1 1)
    (p := 2) (f := 3) Nat.prime_two (by rw [k328r7p_card_L F hF]; norm_num) (n := 3)
    (by norm_num)
  have hmem : ∀ A : GL (Fin 3) (QuadraticAlgebra F 1 1),
      A ∈ k328r7p_SU F ↔
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
    · show k328r7p_rho F A ∈ StatedSp 3 F
      exact (k328r7p_mem_statedSp_iff F hF A).mpr (by
        rw [show (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star =
            (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map (· ^ 8) from by
          ext i j
          · exact congrArg QuadraticAlgebra.re (k328r7p_star_pow F hF (A i j))
          · exact congrArg QuadraticAlgebra.im (k328r7p_star_pow F hF (A i j))]
        exact hA.2)
    · show (Matrix.GeneralLinearGroup.det :
          GL (Fin 3) (QuadraticAlgebra F 1 1) →* (QuadraticAlgebra F 1 1)ˣ) A = 1
      rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]
      exact hA.1
  · intro A hA
    rw [hmem]
    constructor
    · simpa [Matrix.GeneralLinearGroup.val_det_apply, Units.ext_iff] using hA.2
    · have hsp : k328r7p_rho F A ∈ StatedSp 3 F := hA.1
      rw [← (k328r7p_mem_statedSp_iff F hF A).mp hsp]
      have hstar : (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map star =
          (A : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1)).map (· ^ 8) := by
        ext i j
        · exact congrArg QuadraticAlgebra.re (k328r7p_star_pow F hF (A i j))
        · exact congrArg QuadraticAlgebra.im (k328r7p_star_pow F hF (A i j))
      rw [hstar]

private theorem k328r7p_commutator_GU_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    ⁅k328r7p_GU F, k328r7p_GU F⁆ = k328r7p_SU F := by
  have : CharP F 2 := k328r7p_charP_two F hF
  apply le_antisymm
  · rw [k328r7p_statedSU_eq F hF]
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (k328r7p_GU F).mul_mem ((k328r7p_GU F).mul_mem
        ((k328r7p_GU F).mul_mem ha hb) ((k328r7p_GU F).inv_mem ha))
        ((k328r7p_GU F).inv_mem hb)
    · rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      simp [mul_assoc]
  · have : Finite (QuadraticAlgebra F 1 1) :=
      Nat.finite_of_card_ne_zero (by rw [k328r7p_card_L F hF]; norm_num)
    have hperf : commutator (k328r7p_SU F) = ⊤ := by
      have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
          (F := QuadraticAlgebra F 1 1) (p := 2) (f := 3)
          (by rw [k328r7p_card_L F hF]; norm_num) (n := 3) le_rfl (by norm_num)).1
      exact ((fun h => ⟨h.1.1, h.2.1⟩ : CFSG.IsQuasisimple
          (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1)) →
        CFSG.Open.IsQuasisimple (StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1))) h).1
    have hSU : k328r7p_SU F ≤ k328r7p_GU F := by
      rw [k328r7p_statedSU_eq F hF]; exact inf_le_left
    rw [← commutator_self_of_perfect hperf]
    exact Subgroup.commutator_mono hSU hSU

private theorem k328r7p_stdComp_eq (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8)
    (z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1) :
    stdComp (StatedSp 3 F) z₀ =
      (k328r7p_SU F).map (k328r7p_rho F) := by
  have hz' : z₀ = k328r7p_rho F (k328r7p_omegaUnit F hF) := by
    apply Units.ext
    rw [hz, k328r7p_rho_omegaUnit F hF]
    simp [rhoL]
  rw [stdComp, hz', k328r7p_centralizer_eq_range F hF, inf_comm, ← Subgroup.map_comap_eq]
  rw [← Subgroup.map_commutator]
  congr 1
  exact k328r7p_commutator_GU_eq F hF

private abbrev k328r7p_H (F : Type) [Field F] : Subgroup (GL (Fin 3 ⊕ Fin 3) F) :=
  StatedSp 3 F

private abbrev k328r7p_C (F : Type) [Field F] (z₀ : GL (Fin 3 ⊕ Fin 3) F) :
    Subgroup (GL (Fin 3 ⊕ Fin 3) F) :=
  k328r7p_H F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 3 ⊕ Fin 3) F))

private theorem k328r7p_omega_pow_three (F : Type) [Field F] [CharP F 2] :
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

private theorem k328r7p_omega_ne_one (F : Type) [Field F] :
    (ω : QuadraticAlgebra F 1 1) ≠ 1 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_omega, QuadraticAlgebra.im_one] at him
  exact one_ne_zero (α := F) him

private theorem k328r7p_omega_ne_zero (F : Type) [Field F] :
    (ω : QuadraticAlgebra F 1 1) ≠ 0 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_omega, QuadraticAlgebra.im_zero] at him
  exact one_ne_zero (α := F) him

private theorem k328r7p_orderOf_omegaUnit (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : orderOf (k328r7p_omegaUnit F hF) = 3 := by
  have : CharP F 2 := k328r7p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  have h3 : (ω : QuadraticAlgebra F 1 1) ^ 3 = 1 := k328r7p_omega_pow_three F
  have hne : (ω : QuadraticAlgebra F 1 1) ≠ 1 := k328r7p_omega_ne_one F
  have h0 : (ω : QuadraticAlgebra F 1 1) ≠ 0 := k328r7p_omega_ne_zero F
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
  have hEq : k328r7p_omegaUnit F hF =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (ω : QuadraticAlgebra F 1 1) h0) := by
    rw [k328r7p_omegaUnit]
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
      (QuadraticAlgebra F 1 1)ˣ →* GL (Fin 3) (QuadraticAlgebra F 1 1)) := by
    intro c c' hcc'
    have := congrArg (fun g : GL (Fin 3) (QuadraticAlgebra F 1 1) =>
      (g : Matrix (Fin 3) (Fin 3) (QuadraticAlgebra F 1 1))) hcc'
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] at this
    exact Units.ext this
  rw [hEq]
  exact (orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin 3)) hinj _).trans hω

private theorem k328r7p_orderOf_rho (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : GL (Fin 3) (QuadraticAlgebra F 1 1)) :
    orderOf (k328r7p_rho F A) = orderOf A :=
  orderOf_injective (k328r7p_rho F) (k328r7p_rho_injective F) A

private theorem k328r7p_orderOf_z0 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1) :
    orderOf z₀ = 3 := by
  have hz' : z₀ = k328r7p_rho F (k328r7p_omegaUnit F hF) := by
    apply Units.ext
    rw [hz, k328r7p_rho_omegaUnit F hF]
    simp [rhoL]
  rw [hz', k328r7p_orderOf_rho, k328r7p_orderOf_omegaUnit F hF]

private theorem k328r7p_omegaUnit_mem_SU (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r)] (hF : Fintype.card F = 8) :
    k328r7p_omegaUnit F hF ∈ k328r7p_SU F := by
  have : CharP F 2 := k328r7p_charP_two F hF
  have hcard : Nat.card (QuadraticAlgebra F 1 1) = (2 ^ 3) ^ 2 := by
    rw [k328r7p_card_L F hF]; norm_num
  rw [show k328r7p_SU F = StatedSU 3 (2 ^ 3) (QuadraticAlgebra F 1 1) from rfl]
  rw [k328r7p_omegaUnit]
  rw [CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hcard (n := 3) (by norm_num)]
  refine ⟨?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact k328r7p_omega_pow_three F
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    rw [show (2 : ℕ) ^ 3 + 1 = 9 from by norm_num, show (9 : ℕ) = 3 * 3 from rfl, pow_mul,
      k328r7p_omega_pow_three F, one_pow]

private theorem k328r7p_centralizer_eq (F : Type) [Field F] (z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz₀ : z₀ ∈ k328r7p_H F) :
    Subgroup.centralizer (Subgroup.zpowers (⟨z₀, hz₀⟩ : ↥(k328r7p_H F)) :
        Set ↥(k328r7p_H F)) =
      (k328r7p_C F z₀).subgroupOf (k328r7p_H F) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact congrArg Subtype.val (hx ⟨z₀, hz₀⟩ (Subgroup.mem_zpowers _))
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (⟨z₀, hz₀⟩ : ↥(k328r7p_H F)) x := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx.2 z₀ (Set.mem_singleton z₀))
    exact (hc.zpow_left n).eq

private theorem k328r7p_subgroupOf_commutator (F : Type) [Field F]
    (z₀ : GL (Fin 3 ⊕ Fin 3) F) :
    (stdComp (k328r7p_H F) z₀).subgroupOf (k328r7p_H F) =
      ⁅(k328r7p_C F z₀).subgroupOf (k328r7p_H F),
        (k328r7p_C F z₀).subgroupOf (k328r7p_H F)⁆ := by
  have hmap : ((k328r7p_C F z₀).subgroupOf (k328r7p_H F)).map (k328r7p_H F).subtype =
      k328r7p_C F z₀ :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have h2 := Subgroup.map_commutator (f := (k328r7p_H F).subtype)
    (H₁ := (k328r7p_C F z₀).subgroupOf (k328r7p_H F))
    (H₂ := (k328r7p_C F z₀).subgroupOf (k328r7p_H F))
  rw [hmap] at h2
  rw [stdComp, ← h2]
  exact Subgroup.comap_map_eq_self_of_injective (k328r7p_H F).subtype_injective _

theorem row7_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    PosLeaf (StatedSp 3 F) z₀ := by
  have : CharP F 2 := k328r7p_charP_two F hF
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := k328r7p_fact F hF
  have : Finite (QuadraticAlgebra F 1 1) :=
    Nat.finite_of_card_ne_zero (by rw [k328r7p_card_L F hF]; norm_num)
  have _ht := ht
  intro hz₀
  have hz' : z₀ = k328r7p_rho F (k328r7p_omegaUnit F hF) := by
    apply Units.ext
    rw [hz, k328r7p_rho_omegaUnit F hF]
    simp [rhoL]
  have hstd : stdComp (StatedSp 3 F) z₀ = (k328r7p_SU F).map (k328r7p_rho F) :=
    k328r7p_stdComp_eq F hF z₀ hz
  have hz_mem : z₀ ∈ stdComp (StatedSp 3 F) z₀ := by
    rw [hstd, hz']
    exact Subgroup.mem_map_of_mem _ (k328r7p_omegaUnit_mem_SU F hF)
  have hcardL : Nat.card (QuadraticAlgebra F 1 1) = (2 ^ 3) ^ 2 := by
    rw [k328r7p_card_L F hF]; norm_num
  have hqsc := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := QuadraticAlgebra F 1 1) (p := 2) (f := 3) hcardL (n := 3) le_rfl (by norm_num)
  have hqsc' : CFSG.IsQuasisimple ↥(k328r7p_SU F) ∧
      Subgroup.center ↥(k328r7p_SU F) =
        (StatedScalars (Fin 3) (QuadraticAlgebra F 1 1)).subgroupOf (k328r7p_SU F) := by
    simpa only [k328r7p_SU] using hqsc
  have hqs : CFSG.Open.IsQuasisimple ↥(k328r7p_SU F) :=
    (fun h => ⟨h.1.1, h.2.1⟩ : CFSG.IsQuasisimple ↥(k328r7p_SU F) →
      CFSG.Open.IsQuasisimple ↥(k328r7p_SU F)) hqsc'.1
  have hcenter : Nat.card (Subgroup.center ↥(k328r7p_SU F)) = 3 := by
    rw [hqsc'.2]
    obtain ⟨-, -, hc⟩ := CFSG.LinearGroups.unitary_scalar_kernel (K := QuadraticAlgebra F 1 1)
      (p := 2) (f := 3) Nat.prime_two hcardL (n := 3) (by norm_num)
    rw [hc]; norm_num
  have hmodel : LieModel (↥(k328r7p_SU F) ⧸ Subgroup.center ↥(k328r7p_SU F)) .PSU 3 2 3 := by
    refine Or.inl ⟨by decide, ?_⟩
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩,
      QuadraticAlgebra F 1 1, inferInstance, inferInstance, hcardL, ?_⟩
    refine ⟨?_⟩
    exact QuotientGroup.congr (Subgroup.center ↥(k328r7p_SU F))
      ((StatedScalars (Fin 3) (QuadraticAlgebra F 1 1)).subgroupOf (k328r7p_SU F))
      (MulEquiv.refl _) (by simpa using hqsc'.2)
  let eX : ↥((stdComp (StatedSp 3 F) z₀).subgroupOf (StatedSp 3 F)) ≃* ↥(k328r7p_SU F) :=
    (Subgroup.subgroupOfEquivOfLe (stdComp_le (StatedSp 3 F) z₀)).trans
      ((MulEquiv.subgroupCongr hstd).trans
        (((k328r7p_SU F).equivMapOfInjective (k328r7p_rho F)
          (k328r7p_rho_injective F)).symm))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_mk, k328r7p_orderOf_z0 F hF z₀ hz]
  · intro y hy
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.zpow_mem _ hz_mem n
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_subgroupOf] at hx
    have hxC : (↑x : GL (Fin 3 ⊕ Fin 3) F) ∈ k328r7p_C F z₀ :=
      Subgroup.commutator_le_self (k328r7p_C F z₀) hx
    have hc : Commute (⟨z₀, hz₀⟩ : ↥(StatedSp 3 F)) x := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxC.2 z₀ (Set.mem_singleton z₀)
    exact (hc.zpow_left n).eq
  · rw [k328r7p_centralizer_eq F z₀ hz₀, k328r7p_subgroupOf_commutator F z₀]
    have h := (commutator_normal_in_sup ((k328r7p_C F z₀).subgroupOf (k328r7p_H F))
      ((k328r7p_C F z₀).subgroupOf (k328r7p_H F))).isSubnormal
    rwa [sup_idem] at h
  · exact isQuasisimple_of_mulEquiv' eX.symm hqs
  · exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).trans hcenter
  · exact Or.inr (LieModel.of_mulEquiv (QuotientGroup.congr (Subgroup.center _)
      (Subgroup.center ↥(k328r7p_SU F)) eX (Subgroup.map_center_eq eX)).symm hmodel)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

