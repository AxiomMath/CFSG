module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import CFSG.LinearAlgebra.AnisotropicBinaryPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Unitary CFSG.RankThree.SubgroupLists
open Matrix

private abbrev k328r7g_L (F : Type) [Field F] : Type := QuadraticAlgebra F 1 1

private def k328r7g_omega (F : Type) [Field F] : k328r7g_L F := QuadraticAlgebra.omega

private theorem k328r7g_aniso (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) : ∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r := by
  intro r hr
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have hr2 : r ^ 2 = 1 + r := by simpa using hr
  have hr3 : r ^ 3 = 1 := by
    calc r ^ 3 = r * r ^ 2 := by ring
      _ = r * (1 + r) := by rw [hr2]
      _ = r + r ^ 2 := by ring
      _ = r + (1 + r) := by rw [hr2]
      _ = 1 + (r + r) := by ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, one_pow] at hr2
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero (R := F)
    have : (1 : F) = 0 := by
      calc (1 : F) = 1 + 1 := hr2
        _ = 2 := by norm_num
        _ = 0 := h2
    exact one_ne_zero this
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr2
    simp at hr2
  let u : Fˣ := Units.mk0 r hr0
  have hu : (u : F) = r := rfl
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hr3, Units.val_one])
  have hu1 : u ≠ 1 := fun h => hr1 (by rw [← hu, h]; rfl)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card Fˣ := hord ▸ orderOf_dvd_natCard u
  have hcard : Nat.card Fˣ = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hF]
  rw [hcard] at hdvd
  norm_num at hdvd

private def k328r7g_phi (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (Fin 3 → k328r7g_L F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 → F) where
  toFun x := Sum.elim (fun i => (x i).re) (fun i => (x i).im)
  invFun v i := ⟨v (Sum.inl i), v (Sum.inr i)⟩
  left_inv x := by funext i; ext <;> rfl
  right_inv v := by funext s; cases s <;> rfl
  map_add' x y := by funext s; cases s <;> rfl
  map_smul' c x := by
    funext s
    cases s <;>
      · simp [Algebra.smul_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

private theorem k328r7g_phi_inl (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (x : Fin 3 → k328r7g_L F) (i : Fin 3) :
    k328r7g_phi F x (Sum.inl i) = (x i).re := rfl

private theorem k328r7g_phi_inr (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (x : Fin 3 → k328r7g_L F) (i : Fin 3) :
    k328r7g_phi F x (Sum.inr i) = (x i).im := rfl

private def k328r7g_rhoMat (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  rhoL F (A.map QuadraticAlgebra.re) (A.map QuadraticAlgebra.im)

private theorem k328r7g_rhoMat_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) (x : Fin 3 → k328r7g_L F) :
    k328r7g_rhoMat F A *ᵥ (k328r7g_phi F x) = k328r7g_phi F (A *ᵥ x) := by
  funext s
  cases s with
  | inl i =>
    show (k328r7g_rhoMat F A *ᵥ (k328r7g_phi F x)) (Sum.inl i) = ((A *ᵥ x) i).re
    unfold k328r7g_rhoMat rhoL
    rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Function.comp_apply, k328r7g_phi_inl, k328r7g_phi_inr]
    conv_rhs => rw [← QuadraticAlgebra.reₗ_apply, map_sum]
    simp only [QuadraticAlgebra.reₗ_apply, QuadraticAlgebra.re_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul]
  | inr i =>
    show (k328r7g_rhoMat F A *ᵥ (k328r7g_phi F x)) (Sum.inr i) = ((A *ᵥ x) i).im
    unfold k328r7g_rhoMat rhoL
    rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Function.comp_apply, k328r7g_phi_inl, k328r7g_phi_inr, Matrix.add_apply]
    conv_rhs => rw [← QuadraticAlgebra.imₗ_apply, map_sum]
    simp only [QuadraticAlgebra.imₗ_apply, QuadraticAlgebra.im_mul]
    have h1 : (∑ j, ((A i j).re + (A i j).im) * (x j).im)
        = ∑ j, ((A i j).re * (x j).im + (A i j).im * (x j).im) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1]
    have h2 : (∑ j, ((A i j).re * (x j).im + (A i j).im * (x j).re + 1 * (A i j).im * (x j).im))
        = ∑ j, ((A i j).re * (x j).im + (A i j).im * (x j).re + (A i j).im * (x j).im) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h2]
    simp only [Finset.sum_add_distrib]
    abel

private theorem k328r7g_hB_star (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    (x y : Fin 3 → k328r7g_L F) :
    spForm 3 F (k328r7g_phi F x) (k328r7g_phi F y) =
      (herm (starRingAut (R := k328r7g_L F)) x y
        + starRingAut (herm (starRingAut (R := k328r7g_L F)) x y)).re := by
  rw [spForm_apply]
  simp only [k328r7g_phi_inl, k328r7g_phi_inr]
  have htrace : (herm (starRingAut (R := k328r7g_L F)) x y
        + starRingAut (herm (starRingAut (R := k328r7g_L F)) x y)).re
      = QuadraticAlgebra.trace (herm (starRingAut (R := k328r7g_L F)) x y) := by
    rw [starRingAut_apply, ← QuadraticAlgebra.algebraMap_trace_eq_add_star]
    simp
  rw [htrace, QuadraticAlgebra.trace_def, herm_def]
  conv_rhs => rw [← QuadraticAlgebra.imₗ_apply, map_sum]
  simp only [QuadraticAlgebra.imₗ_apply, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star, starRingAut_apply]
  rw [Finset.sum_add_distrib]
  rw [CharTwo.two_eq_zero, zero_mul, zero_add, one_mul]
  simp only [CharTwo.neg_eq, sub_eq_add_neg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_mul]
  ring_nf
  rw [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem k328r7g_mat_ext_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [NonAssocSemiring R] {M N : Matrix ι ι R}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

private theorem k328r7g_rhoMat_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A B : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) :
    k328r7g_rhoMat F A * k328r7g_rhoMat F B = k328r7g_rhoMat F (A * B) := by
  apply k328r7g_mat_ext_mulVec
  intro v
  obtain ⟨x, rfl⟩ := (k328r7g_phi F).surjective v
  rw [← Matrix.mulVec_mulVec, k328r7g_rhoMat_mulVec, k328r7g_rhoMat_mulVec,
    k328r7g_rhoMat_mulVec, ← Matrix.mulVec_mulVec]

private theorem k328r7g_rhoMat_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7g_rhoMat F 1 = 1 := by
  apply k328r7g_mat_ext_mulVec
  intro v
  obtain ⟨x, rfl⟩ := (k328r7g_phi F).surjective v
  rw [k328r7g_rhoMat_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

private def k328r7g_J (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F) : Subgroup (GL (Fin 3 ⊕ Fin 3) F) :=
  StatedSp 3 F ⊓ Subgroup.centralizer {z₀} ⊔ StatedSp 3 F ⊓ Subgroup.centralizer {t₀} ⊔
    StatedSp 3 F ⊓ Subgroup.centralizer {z₀ * t₀} ⊔
      StatedSp 3 F ⊓ Subgroup.centralizer {z₀ * t₀ ^ 2}

private theorem k328r7g_J_le (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F) : k328r7g_J F z₀ t₀ ≤ StatedSp 3 F := by
  unfold k328r7g_J
  refine sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left

private def k328r7g_S (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (J : Subgroup (GL (Fin 3 ⊕ Fin 3) F)) : Set (Fin 3 ⊕ Fin 3 → F) :=
  {a | a ≠ 0 ∧ ∀ c, spTrans a c ∈ J}

private theorem k328r7g_S_stable (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {J : Subgroup (GL (Fin 3 ⊕ Fin 3) F)} (hJH : J ≤ StatedSp 3 F)
    {a : Fin 3 ⊕ Fin 3 → F} (ha : a ∈ k328r7g_S F J)
    {g : GL (Fin 3 ⊕ Fin 3) F} (hg : g ∈ J) : g • a ∈ k328r7g_S F J := by
  refine ⟨?_, ?_⟩
  · intro h
    apply ha.1
    have := congrArg (fun v => g⁻¹ • v) h
    simpa using this
  · intro c
    have hconj := conj_spTrans (hJH hg) a c
    change spTrans ((g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ a) c ∈ J
    rw [← hconj]
    exact J.mul_mem (J.mul_mem hg (ha.2 c)) (J.inv_mem hg)

private theorem k328r7g_S_of_fix (F : Type) [Field F] [Fintype F] [DecidableEq F]
    {J : Subgroup (GL (Fin 3 ⊕ Fin 3) F)} {s : GL (Fin 3 ⊕ Fin 3) F}
    (hsH : s ∈ StatedSp 3 F) (hC : StatedSp 3 F ⊓ Subgroup.centralizer {s} ≤ J)
    {a : Fin 3 ⊕ Fin 3 → F} (ha0 : a ≠ 0) (hsa : s • a = a) :
    a ∈ k328r7g_S F J := by
  refine ⟨ha0, fun c => hC ⟨spTrans_mem_statedSp a c, ?_⟩⟩
  change spTrans a c ∈ Subgroup.centralizer ({s} : Set (GL (Fin 3 ⊕ Fin 3) F))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hconj := conj_spTrans hsH a c
  have hsa' : (y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ a = a := hsa
  rw [hsa'] at hconj
  have := congrArg (fun z => z * y) hconj
  simpa [mul_assoc] using this

private theorem k328r7g_star_algebraMap (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] (γ : F) :
    star (algebraMap F (k328r7g_L F) γ) = algebraMap F (k328r7g_L F) γ := by
  ext <;> simp

private theorem k328r7g_herm_smul_right (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)]
    (x y : Fin 3 → k328r7g_L F) (γ : F) :
    herm (starRingAut (R := k328r7g_L F)) x (γ • y)
      = algebraMap F (k328r7g_L F) γ * herm (starRingAut (R := k328r7g_L F)) x y := by
  simp only [herm, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

private theorem k328r7g_herm_smul_left (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)]
    (x y : Fin 3 → k328r7g_L F) (γ : F) :
    herm (starRingAut (R := k328r7g_L F)) (γ • x) y
      = algebraMap F (k328r7g_L F) γ * herm (starRingAut (R := k328r7g_L F)) x y := by
  simp only [herm, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul,
    starRingAut_apply, k328r7g_star_algebraMap]
  apply Finset.sum_congr rfl; intro i _; ring

private theorem k328r7g_herm_smul_both (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)]
    (x : Fin 3 → k328r7g_L F) (γ : F) :
    herm (starRingAut (R := k328r7g_L F)) (γ • x) (γ • x)
      = algebraMap F (k328r7g_L F) γ * algebraMap F (k328r7g_L F) γ
        * herm (starRingAut (R := k328r7g_L F)) x x := by
  simp only [herm, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  simp only [map_mul, starRingAut_apply, k328r7g_star_algebraMap]
  ring

private theorem k328r7g_star_invol (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] :
    ∀ c : k328r7g_L F, starRingAut (starRingAut c) = c := by
  intro c
  rw [starRingAut_apply, starRingAut_apply]
  apply QuadraticAlgebra.ext
  · simp
  · simp

private theorem k328r7g_N_add_phi (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    (x y : Fin 3 → k328r7g_L F) (γ : F) :
    (herm (starRingAut (R := k328r7g_L F)) (x + γ • y) (x + γ • y)).re
      = (herm (starRingAut (R := k328r7g_L F)) x x).re
        + γ * spForm 3 F (k328r7g_phi F x) (k328r7g_phi F y)
        + γ ^ 2 * (herm (starRingAut (R := k328r7g_L F)) y y).re := by
  rw [herm_add_left, herm_add_right, herm_add_right]
  rw [k328r7g_herm_smul_right, k328r7g_herm_smul_left, k328r7g_herm_smul_both]
  have hconj : herm (starRingAut (R := k328r7g_L F)) y x
      = starRingAut (herm (starRingAut (R := k328r7g_L F)) x y) :=
    herm_conj (σ := starRingAut (R := k328r7g_L F)) (k328r7g_star_invol F) x y
  rw [hconj]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul,
    add_zero]
  have hcross : (herm (starRingAut (R := k328r7g_L F)) x y
        + starRingAut (herm (starRingAut (R := k328r7g_L F)) x y)).re
      = spForm 3 F (k328r7g_phi F x) (k328r7g_phi F y) := (k328r7g_hB_star F x y).symm
  have hcross' : (herm (starRingAut (R := k328r7g_L F)) x y).re
      + (starRingAut (herm (starRingAut (R := k328r7g_L F)) x y)).re
      = spForm 3 F (k328r7g_phi F x) (k328r7g_phi F y) := by
    simpa only [QuadraticAlgebra.re_add] using hcross
  linear_combination γ * hcross'

private theorem k328r7g_omega_sq (F : Type) [Field F] :
    k328r7g_omega F * k328r7g_omega F = 1 + k328r7g_omega F := by
  simpa [k328r7g_omega, one_smul, pow_two] using
    (QuadraticAlgebra.omega_pow_two_eq_add (R := F) (a := 1) (b := 1))

private theorem k328r7g_omega_cube (F : Type) [Field F] [CharP F 2] :
    k328r7g_omega F ^ 3 = 1 := by
  have : CharP (k328r7g_L F) 2 :=
    charP_of_injective_algebraMap (R := F) (A := k328r7g_L F) (p := 2)
      (fun x y h => by
        have := congrArg QuadraticAlgebra.re h
        simpa using this)
  have h2 := k328r7g_omega_sq F
  calc k328r7g_omega F ^ 3 = k328r7g_omega F * k328r7g_omega F ^ 2 := by ring
    _ = k328r7g_omega F * (1 + k328r7g_omega F) := by rw [pow_two, h2]
    _ = k328r7g_omega F + k328r7g_omega F * k328r7g_omega F := by ring
    _ = k328r7g_omega F + (1 + k328r7g_omega F) := by rw [h2]
    _ = 1 + k328r7g_omega F * 2 := by ring
    _ = 1 := by rw [CharTwo.two_eq_zero, mul_zero, add_zero]

private def k328r7g_D0 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) (k328r7g_L F) :=
  Matrix.diagonal ![1, k328r7g_omega F ^ 2, k328r7g_omega F]

private def k328r7g_D1 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) (k328r7g_L F) :=
  Matrix.diagonal ![k328r7g_omega F ^ 2, 1, k328r7g_omega F]

private def k328r7g_D2 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) (k328r7g_L F) :=
  Matrix.diagonal ![k328r7g_omega F, k328r7g_omega F ^ 2, 1]

private theorem k328r7g_D0_mulVec (F : Type) [Field F] (c : k328r7g_L F) :
    k328r7g_D0 F *ᵥ (Pi.single (0 : Fin 3) c) = Pi.single (0 : Fin 3) c := by
  funext i
  fin_cases i <;>
    simp [k328r7g_D0, Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem k328r7g_D1_mulVec (F : Type) [Field F] (c : k328r7g_L F) :
    k328r7g_D1 F *ᵥ (Pi.single (1 : Fin 3) c) = Pi.single (1 : Fin 3) c := by
  funext i
  fin_cases i <;>
    simp [k328r7g_D1, Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem k328r7g_D2_mulVec (F : Type) [Field F] (c : k328r7g_L F) :
    k328r7g_D2 F *ᵥ (Pi.single (2 : Fin 3) c) = Pi.single (2 : Fin 3) c := by
  funext i
  fin_cases i <;>
    simp [k328r7g_D2, Matrix.mulVec, dotProduct, Pi.single_apply]

private def k328r7g_zL (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) (k328r7g_L F) :=
  Matrix.scalar (Fin 3) (k328r7g_omega F)

private theorem k328r7g_zL_re (F : Type) [Field F] :
    (k328r7g_zL F).map QuadraticAlgebra.re = 0 := by
  ext i j
  by_cases h : i = j <;> simp [k328r7g_zL, k328r7g_omega, Matrix.scalar_apply,
    Matrix.map_apply, h]

private theorem k328r7g_zL_im (F : Type) [Field F] :
    (k328r7g_zL F).map QuadraticAlgebra.im = 1 := by
  ext i j
  by_cases h : i = j <;> simp [k328r7g_zL, k328r7g_omega, Matrix.scalar_apply,
    Matrix.map_apply, Matrix.one_apply, h]

private theorem k328r7g_D2_re (F : Type) [Field F] :
    (k328r7g_D2 F).map QuadraticAlgebra.re = Matrix.diagonal ![0, 1, 1] := by
  ext i j
  unfold k328r7g_D2
  fin_cases i <;> fin_cases j <;>
    simp [k328r7g_omega, pow_two, Matrix.map_apply, Fin.reduceFinMk, QuadraticAlgebra.re_one]

private theorem k328r7g_D2_im (F : Type) [Field F] :
    (k328r7g_D2 F).map QuadraticAlgebra.im = Matrix.diagonal ![1, 1, 0] := by
  ext i j
  unfold k328r7g_D2
  fin_cases i <;> fin_cases j <;>
    simp [k328r7g_omega, pow_two, Matrix.map_apply, Fin.reduceFinMk, QuadraticAlgebra.im_one]

private theorem k328r7g_rhoMat_zL (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7g_rhoMat F (k328r7g_zL F) = rhoL F 0 1 := by
  rw [k328r7g_rhoMat, k328r7g_zL_re, k328r7g_zL_im]

private theorem k328r7g_rhoMat_D2 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7g_rhoMat F (k328r7g_D2 F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]) := by
  rw [k328r7g_rhoMat, k328r7g_D2_re, k328r7g_D2_im]

private theorem k328r7g_zL_mul_D2 (F : Type) [Field F] [CharP F 2] :
    k328r7g_zL F * k328r7g_D2 F = k328r7g_D1 F := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    · apply QuadraticAlgebra.ext <;>
        simp [k328r7g_zL, k328r7g_D2, k328r7g_D1, k328r7g_omega, pow_two, Matrix.mul_apply,
          Matrix.diagonal_apply, CharTwo.add_self_eq_zero, QuadraticAlgebra.im_one,
          QuadraticAlgebra.re_one, Fin.reduceFinMk]

private theorem k328r7g_zL_mul_D2_mul_D2 (F : Type) [Field F] [CharP F 2] :
    k328r7g_zL F * k328r7g_D2 F * k328r7g_D2 F = k328r7g_D0 F := by
  rw [k328r7g_zL_mul_D2]
  funext i j
  fin_cases i <;> fin_cases j <;>
    · apply QuadraticAlgebra.ext <;>
        simp [k328r7g_D1, k328r7g_D2, k328r7g_D0, k328r7g_omega, pow_two, Matrix.mul_apply,
          Matrix.diagonal_apply, CharTwo.add_self_eq_zero, QuadraticAlgebra.im_one,
          QuadraticAlgebra.re_one, Fin.reduceFinMk]

private theorem k328r7g_star_omega (F : Type) [Field F] [CharP F 2] :
    star (k328r7g_omega F) = k328r7g_omega F ^ 2 := by
  apply QuadraticAlgebra.ext <;>
    simp [k328r7g_omega, pow_two, CharTwo.neg_eq]

private theorem k328r7g_zL_mulVec (F : Type) [Field F] (x : Fin 3 → k328r7g_L F) :
    k328r7g_zL F *ᵥ x = k328r7g_omega F • x := by
  funext i
  rw [k328r7g_zL, Matrix.scalar_apply, mulVec_diagonal]
  rfl

private theorem k328r7g_omega_sq_mul (F : Type) [Field F] [CharP F 2] :
    k328r7g_omega F ^ 2 * k328r7g_omega F = 1 := by
  rw [← pow_succ]
  exact k328r7g_omega_cube F

private theorem k328r7g_omega_pow6 (F : Type) [Field F] [CharP F 2] :
    k328r7g_omega F ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, k328r7g_omega_cube F, one_pow]

private theorem k328r7g_zL_herm (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    (x y : Fin 3 → k328r7g_L F) :
    herm (starRingAut (R := k328r7g_L F)) (k328r7g_zL F *ᵥ x) (k328r7g_zL F *ᵥ y)
      = herm (starRingAut (R := k328r7g_L F)) x y := by
  rw [k328r7g_zL_mulVec F x, k328r7g_zL_mulVec F y]
  rw [herm_smul_left, herm_smul_right, starRingAut_apply, k328r7g_star_omega,
    ← mul_assoc, k328r7g_omega_sq_mul, one_mul]

private theorem k328r7g_D2_mulVec_eq (F : Type) [Field F] (x : Fin 3 → k328r7g_L F) :
    k328r7g_D2 F *ᵥ x = fun i => ![k328r7g_omega F, k328r7g_omega F ^ 2, 1] i * x i := by
  funext i
  rw [k328r7g_D2, mulVec_diagonal]

private theorem k328r7g_D2_herm (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    (x y : Fin 3 → k328r7g_L F) :
    herm (starRingAut (R := k328r7g_L F)) (k328r7g_D2 F *ᵥ x) (k328r7g_D2 F *ᵥ y)
      = herm (starRingAut (R := k328r7g_L F)) x y := by
  simp only [k328r7g_D2_mulVec_eq F, herm]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;>
    · rw [map_mul, starRingAut_apply]
      simp
      try rw [k328r7g_star_omega]
      try rw [map_pow]
      try rw [starRingAut_apply]
      try rw [k328r7g_star_omega]
      try ring_nf
      try rw [k328r7g_omega_pow6]
      try rw [k328r7g_omega_cube]
      try ring

private theorem k328r7g_rhoMat_preserves (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {M : Matrix (Fin 3) (Fin 3) (k328r7g_L F)}
    (hM : ∀ x y, herm (starRingAut (R := k328r7g_L F)) (M *ᵥ x) (M *ᵥ y)
      = herm (starRingAut (R := k328r7g_L F)) x y) :
    ∀ u v, spForm 3 F (k328r7g_rhoMat F M *ᵥ u) (k328r7g_rhoMat F M *ᵥ v)
      = spForm 3 F u v := by
  intro u v
  obtain ⟨x, rfl⟩ := (k328r7g_phi F).surjective u
  obtain ⟨y, rfl⟩ := (k328r7g_phi F).surjective v
  rw [k328r7g_rhoMat_mulVec, k328r7g_rhoMat_mulVec,
    k328r7g_hB_star F (M *ᵥ x) (M *ᵥ y), k328r7g_hB_star F x y, hM]

private theorem k328r7g_phi_single (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (j : Fin 3) (c : k328r7g_L F) :
    k328r7g_phi F (Pi.single j c)
      = fun s => match s with
        | Sum.inl i => if i = j then c.re else 0
        | Sum.inr i => if i = j then c.im else 0 := by
  funext s
  cases s with
  | inl i =>
    by_cases h : i = j <;> simp [k328r7g_phi_inl, h]
  | inr i =>
    by_cases h : i = j <;> simp [k328r7g_phi_inr, h]

private def k328r7g_rhoGL (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : GL (Fin 3) (k328r7g_L F)) : GL (Fin 3 ⊕ Fin 3) F where
  val := k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
  inv := k328r7g_rhoMat F ((g⁻¹ : GL (Fin 3) (k328r7g_L F)) : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
  val_inv := by
    change k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        * k328r7g_rhoMat F (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) = 1
    have h : (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        * (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) = 1 := by
      simp
    calc k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
          * k328r7g_rhoMat F (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        = k328r7g_rhoMat F ((g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
            * (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))) :=
          k328r7g_rhoMat_mul F _ _
      _ = k328r7g_rhoMat F 1 := by rw [h]
      _ = 1 := k328r7g_rhoMat_one F
  inv_val := by
    change k328r7g_rhoMat F (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        * k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) = 1
    have h : (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        * (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) = 1 := by
      simp
    calc k328r7g_rhoMat F (↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
          * k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
        = k328r7g_rhoMat F ((↑g⁻¹ : Matrix (Fin 3) (Fin 3) (k328r7g_L F))
            * (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))) :=
          k328r7g_rhoMat_mul F _ _
      _ = k328r7g_rhoMat F 1 := by rw [h]
      _ = 1 := k328r7g_rhoMat_one F

private theorem k328r7g_rhoGL_apply (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : GL (Fin 3) (k328r7g_L F)) :
    ((k328r7g_rhoGL F g : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      k328r7g_rhoMat F (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F)) := rfl

private theorem k328r7g_rhoGL_mulVec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (g : GL (Fin 3) (k328r7g_L F)) (x : Fin 3 → k328r7g_L F) :
    ((k328r7g_rhoGL F g : GL (Fin 3 ⊕ Fin 3) F) : Matrix _ _ F) *ᵥ (k328r7g_phi F x) =
      k328r7g_phi F (g • x) := by
  rw [k328r7g_rhoGL_apply, k328r7g_rhoMat_mulVec]
  rfl

private theorem k328r7g_z_sp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {z₀ : GL (Fin 3 ⊕ Fin 3) F} (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1) :
    z₀ ∈ StatedSp 3 F := by
  rw [mem_statedSp_iff_preserves]
  intro u v
  rw [hz, ← k328r7g_rhoMat_zL]
  exact k328r7g_rhoMat_preserves F (k328r7g_zL_herm F) u v

private theorem k328r7g_t_sp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    t₀ ∈ StatedSp 3 F := by
  rw [mem_statedSp_iff_preserves]
  intro u v
  rw [ht, ← k328r7g_rhoMat_D2]
  exact k328r7g_rhoMat_preserves F (k328r7g_D2_herm F) u v

private theorem k328r7g_rhoGL_mem_J (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (_hzH : z₀ ∈ StatedSp 3 F)
    (g : GL (Fin 3) (k328r7g_L F))
    (hg : ∀ x y : Fin 3 → k328r7g_L F,
      herm (starRingAut (R := k328r7g_L F)) (g • x) (g • y)
      = herm (starRingAut (R := k328r7g_L F)) x y) :
    k328r7g_rhoGL F g ∈ k328r7g_J F z₀ t₀ := by
  refine Subgroup.mem_sup_left ?_
  refine Subgroup.mem_sup_left ?_
  refine Subgroup.mem_sup_left ?_
  refine ⟨?_, ?_⟩
  · change k328r7g_rhoGL F g ∈ StatedSp 3 F
    rw [mem_statedSp_iff_preserves]
    intro u v
    rw [k328r7g_rhoGL_apply]
    exact k328r7g_rhoMat_preserves F hg u v
  · change k328r7g_rhoGL F g ∈ Subgroup.centralizer ({z₀} : Set (GL (Fin 3 ⊕ Fin 3) F))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Units.ext
    change ((z₀ : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        * ((k328r7g_rhoGL F g : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
      = ((k328r7g_rhoGL F g : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        * ((z₀ : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    rw [k328r7g_rhoGL_apply, hz, ← k328r7g_rhoMat_zL, k328r7g_rhoMat_mul, k328r7g_rhoMat_mul]
    congr 1
    exact Matrix.scalar_comm (k328r7g_omega F) (fun r' => mul_comm _ _)
      (g : Matrix (Fin 3) (Fin 3) (k328r7g_L F))

private theorem k328r7g_line_fix (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]))
    (c : k328r7g_L F) :
    ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        *ᵥ k328r7g_phi F (Pi.single (0 : Fin 3) c)
      = k328r7g_phi F (Pi.single (0 : Fin 3) c)
    ∧ ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        *ᵥ k328r7g_phi F (Pi.single (1 : Fin 3) c)
      = k328r7g_phi F (Pi.single (1 : Fin 3) c)
    ∧ ((t₀ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
        *ᵥ k328r7g_phi F (Pi.single (2 : Fin 3) c)
      = k328r7g_phi F (Pi.single (2 : Fin 3) c) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmat : ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7g_rhoMat F (k328r7g_D0 F) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hz, ht, ← k328r7g_rhoMat_zL,
        ← k328r7g_rhoMat_D2, pow_two, k328r7g_rhoMat_mul, k328r7g_rhoMat_mul,
        ← mul_assoc, k328r7g_zL_mul_D2_mul_D2]
    rw [hmat, k328r7g_rhoMat_mulVec, k328r7g_D0_mulVec]
  · have hmat : ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7g_rhoMat F (k328r7g_D1 F) := by
      rw [Units.val_mul, hz, ht, ← k328r7g_rhoMat_zL, ← k328r7g_rhoMat_D2,
        k328r7g_rhoMat_mul, k328r7g_zL_mul_D2]
    rw [hmat, k328r7g_rhoMat_mulVec, k328r7g_D1_mulVec]
  · have hmat : ((t₀ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7g_rhoMat F (k328r7g_D2 F) := by
      rw [ht, ← k328r7g_rhoMat_D2]
    rw [hmat, k328r7g_rhoMat_mulVec, k328r7g_D2_mulVec]

private theorem k328r7g_aniso2 (F : Type) [Field F] [CharP F 2]
    (h : ∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r) :
    ∀ x y : F, x ^ 2 + 1 * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  by_cases hy : y = 0
  · subst hy
    simp only [mul_zero, add_zero] at hxy
    have hx2 : x * x = 0 := by simpa [pow_two] using hxy
    exact ⟨mul_self_eq_zero.mp hx2, rfl⟩
  · exfalso
    have hr : (x / y) ^ 2 = 1 + 1 * (x / y) := by
      field_simp
      have hx2 : x ^ 2 = -(x * y + y ^ 2) := by
        rw [eq_neg_iff_add_eq_zero]
        linear_combination hxy
      rw [hx2, CharTwo.neg_eq]
      ring
    exact h (x / y) hr

private theorem k328r7g_star_eq_unitary (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    [Fintype (k328r7g_L F)] [CharP (k328r7g_L F) 2]
    (hF : Fintype.card F = 8) :
    starRingAut (R := k328r7g_L F) = CFSG.LieType.BorelTits.unitaryInvolution (k328r7g_L F) 2 3 := by
  apply RingEquiv.ext
  intro z
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply (K := k328r7g_L F) (p := 2) (f := 3),
    starRingAut_apply]
  have h := (CFSG.LinearAlgebra.anisotropic_binary_plane_norm_field
    (K := F) (ε := (1 : F)) (k328r7g_aniso2 F Fact.out)).2.2.2.2.2.2.2.2.2.2.2.2
  exact (h 3 (by norm_num) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)).2 z

private theorem k328r7g_isUnitary_star (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    [Fintype (k328r7g_L F)] [CharP (k328r7g_L F) 2]
    (hF : Fintype.card F = 8) (hcardL : Nat.card (k328r7g_L F) = 64) :
    IsUnitaryInvolution (starRingAut (R := k328r7g_L F)) := by
  rw [k328r7g_star_eq_unitary F hF]
  exact isUnitaryInvolution_unitaryInvolution (K := k328r7g_L F) (p := 2) (f := 3) hcardL

private theorem k328r7g_exists_norm_ne_one (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    [Fintype (k328r7g_L F)] [CharP (k328r7g_L F) 2]
    (hF : Fintype.card F = 8) (hcardL : Nat.card (k328r7g_L F) = 64) :
    ∃ s : k328r7g_L F, s ≠ 0 ∧ starRingAut (R := k328r7g_L F) s * s ≠ 1 := by
  obtain ⟨s, hs0, hs1⟩ := exists_norm_ne_one (K := k328r7g_L F) (p := 2) (f := 3) hcardL (by norm_num)
  exact ⟨s, hs0, by rwa [← k328r7g_star_eq_unitary F hF] at hs1⟩

private theorem k328r7g_S_coord (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]))
    (j : Fin 3) (c : k328r7g_L F) (hc : c ≠ 0) :
    k328r7g_phi F (Pi.single j c) ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
  have hzH : z₀ ∈ StatedSp 3 F := k328r7g_z_sp F hz
  have htH : t₀ ∈ StatedSp 3 F := k328r7g_t_sp F ht
  have hphi0 : k328r7g_phi F (Pi.single j c) ≠ 0 := by
    intro h
    have h' : Pi.single j c = 0 := (k328r7g_phi F).injective (by rw [h, map_zero])
    exact hc (by simpa using congrFun h' j)
  have hfix := k328r7g_line_fix F hz ht c
  fin_cases j
  · refine k328r7g_S_of_fix F ((StatedSp 3 F).mul_mem hzH ((StatedSp 3 F).pow_mem htH 2)) ?_ hphi0 ?_
    · rw [k328r7g_J]; exact le_sup_right
    · exact hfix.1
  · refine k328r7g_S_of_fix F ((StatedSp 3 F).mul_mem hzH htH) ?_ hphi0 ?_
    · rw [k328r7g_J]; exact le_trans le_sup_right le_sup_left
    · exact hfix.2.1
  · refine k328r7g_S_of_fix F htH ?_ hphi0 ?_
    · rw [k328r7g_J]; exact le_trans (le_trans le_sup_right le_sup_left) le_sup_left
    · exact hfix.2.2

private noncomputable def k328r7g_N (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] :
    (Fin 3 ⊕ Fin 3 → F) → F :=
  fun a => (herm (starRingAut (R := k328r7g_L F)) ((k328r7g_phi F).symm a)
    ((k328r7g_phi F).symm a)).re

private theorem k328r7g_N_phi (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] (x : Fin 3 → k328r7g_L F) :
    k328r7g_N F (k328r7g_phi F x) = (herm (starRingAut (R := k328r7g_L F)) x x).re := by
  simp [k328r7g_N]

private theorem k328r7g_phi_single_one (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (j : Fin 3) :
    k328r7g_phi F (Pi.single j (1 : k328r7g_L F)) = Pi.single (Sum.inl j) 1 := by
  rw [k328r7g_phi_single]
  funext s
  cases s with
  | inl i => by_cases h : i = j <;> simp [h, QuadraticAlgebra.re_one]
  | inr i => by_cases h : i = j <;> simp [h, QuadraticAlgebra.im_one]

private theorem k328r7g_phi_single_omega (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (j : Fin 3) :
    k328r7g_phi F (Pi.single j (k328r7g_omega F)) = Pi.single (Sum.inr j) 1 := by
  rw [k328r7g_phi_single]
  funext s
  cases s with
  | inl i => by_cases h : i = j <;> simp [h, k328r7g_omega]
  | inr i => by_cases h : i = j <;> simp [h, k328r7g_omega]

private theorem k328r7g_N_single (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2] (s : Fin 3 ⊕ Fin 3) :
    k328r7g_N F (Pi.single s 1) = 1 := by
  rcases s with j | j
  · rw [← k328r7g_phi_single_one F j, k328r7g_N_phi]
    simp [herm_single_right, Pi.single_eq_same, map_one, QuadraticAlgebra.re_one]
  · rw [← k328r7g_phi_single_omega F j, k328r7g_N_phi]
    simp [herm_single_right, Pi.single_eq_same, starRingAut_apply, k328r7g_star_omega,
      k328r7g_omega_sq_mul, QuadraticAlgebra.re_one]

private theorem k328r7g_S_nonIso (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]))
    (hσ : IsUnitaryInvolution (starRingAut (R := k328r7g_L F)))
    (hs : ∃ s : k328r7g_L F, s ≠ 0 ∧ starRingAut (R := k328r7g_L F) s * s ≠ 1)
    {a : Fin 3 ⊕ Fin 3 → F} (hNa : k328r7g_N F a ≠ 0) :
    a ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
  obtain ⟨x, rfl⟩ := (k328r7g_phi F).surjective a
  have hxN : (herm (starRingAut (R := k328r7g_L F)) x x).re ≠ 0 := by
    rwa [k328r7g_N_phi] at hNa
  have hxN0 : herm (starRingAut (R := k328r7g_L F)) x x ≠ 0 := by
    intro h
    exact hxN (by rw [h]; rfl)
  obtain ⟨μ, hμ⟩ := hσ.norm_surj (herm (starRingAut (R := k328r7g_L F)) x x)
    (herm_self_fixed (starRingAut (R := k328r7g_L F)) hσ.invol x) hxN0
  have hμ0 : μ ≠ 0 := fun h => hxN0 (by rw [← hμ, h, mul_zero])
  set x' : Fin 3 → k328r7g_L F := μ⁻¹ • x with hx'def
  have hx' : herm (starRingAut (R := k328r7g_L F)) x' x' = 1 := by
    rw [hx'def, herm_smul_left, herm_smul_right, map_inv₀, ← mul_assoc]
    rw [show (starRingAut μ)⁻¹ * μ⁻¹ = (herm (starRingAut (R := k328r7g_L F)) x x)⁻¹ by
      rw [(mul_inv (starRingAut μ) μ).symm, hμ]]
    rw [inv_mul_cancel₀ hxN0]
  have hε : herm (starRingAut (R := k328r7g_L F)) (Pi.single (0 : Fin 3) (1 : k328r7g_L F))
      (Pi.single (0 : Fin 3) (1 : k328r7g_L F)) = 1 := by
    simp [herm, Pi.single_apply]
  obtain ⟨g, -, hg⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inr ⟨le_rfl, hs⟩) hε hx'
  have hmu_single : μ • (Pi.single (0 : Fin 3) (1 : k328r7g_L F)) = Pi.single (0 : Fin 3) μ := by
    funext i
    by_cases h : i = 0 <;> simp [Pi.smul_apply, h, smul_eq_mul]
  have hgx : (g : GL (Fin 3) (k328r7g_L F))
      • (μ • (Pi.single (0 : Fin 3) (1 : k328r7g_L F))) = x := by
    rw [smul_comm]
    change μ • (g • Pi.single (0 : Fin 3) (1 : k328r7g_L F)) = x
    rw [hg, hx'def]
    rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have haeq : k328r7g_phi F x =
      k328r7g_rhoGL F (g : GL (Fin 3) (k328r7g_L F)) • k328r7g_phi F (Pi.single (0 : Fin 3) μ) := by
    calc k328r7g_phi F x
        = k328r7g_phi F ((g : GL (Fin 3) (k328r7g_L F))
            • (μ • Pi.single (0 : Fin 3) (1 : k328r7g_L F))) := by rw [hgx]
      _ = k328r7g_rhoGL F (g : GL (Fin 3) (k328r7g_L F))
            • k328r7g_phi F (μ • Pi.single (0 : Fin 3) (1 : k328r7g_L F)) := by
          rw [← k328r7g_rhoGL_mulVec]
          rfl
      _ = k328r7g_rhoGL F (g : GL (Fin 3) (k328r7g_L F))
            • k328r7g_phi F (Pi.single (0 : Fin 3) μ) := by rw [hmu_single]
  rw [haeq]
  exact k328r7g_S_stable F (k328r7g_J_le F z₀ t₀)
    (k328r7g_S_coord F hz ht 0 μ hμ0)
    (k328r7g_rhoGL_mem_J F hz (k328r7g_z_sp F hz) g
      (fun x y => herm_smul_smul (starRingAut (R := k328r7g_L F)) g x y))

private theorem k328r7g_spForm_single_inr (F : Type) [Field F]
    (a : Fin 3 ⊕ Fin 3 → F) (i : Fin 3) :
    spForm 3 F a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
  rw [spForm_apply, Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro k _ hk; simp [hk]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem k328r7g_spForm_single_inl (F : Type) [Field F]
    (a : Fin 3 ⊕ Fin 3 → F) (i : Fin 3) :
    spForm 3 F a (Pi.single (Sum.inl i) 1) = -a (Sum.inr i) := by
  rw [spForm_apply, Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro k _ hk; simp [hk]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem k328r7g_omega_ne_zero (F : Type) [Field F] :
    k328r7g_omega F ≠ 0 := by
  intro h
  have h1 : (k328r7g_omega F).im = (0 : k328r7g_L F).im := congrArg QuadraticAlgebra.im h
  rw [QuadraticAlgebra.im_zero] at h1
  exact one_ne_zero h1

private theorem k328r7g_N_add (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2]
    (a b : Fin 3 ⊕ Fin 3 → F) (γ : F) :
    k328r7g_N F (a + γ • b)
      = k328r7g_N F a + γ * spForm 3 F a b + γ ^ 2 * k328r7g_N F b := by
  obtain ⟨x, rfl⟩ := (k328r7g_phi F).surjective a
  obtain ⟨y, rfl⟩ := (k328r7g_phi F).surjective b
  have hlin : k328r7g_phi F x + γ • k328r7g_phi F y = k328r7g_phi F (x + γ • y) := by
    rw [map_add, map_smul]
  rw [hlin, k328r7g_N_phi, k328r7g_N_add_phi, k328r7g_N_phi, k328r7g_N_phi]

private theorem k328r7g_exists_basis_nonorth (F : Type) [Field F]
    {a : Fin 3 ⊕ Fin 3 → F} (ha0 : a ≠ 0) :
    ∃ s : Fin 3 ⊕ Fin 3, spForm 3 F a (Pi.single s 1) ≠ 0 := by
  have hex : ∃ t, a t ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (funext h)
  obtain ⟨t, ht⟩ := hex
  rcases t with i | i
  · exact ⟨Sum.inr i, by rw [k328r7g_spForm_single_inr]; exact ht⟩
  · exact ⟨Sum.inl i, by rw [k328r7g_spForm_single_inl]; exact neg_ne_zero.mpr ht⟩

private theorem k328r7g_exists_d (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] (hF : Fintype.card F = 8) : ∃ d : F, d ≠ 0 ∧ 1 + d ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · have hthis := h x hx
      have h2 : x = (1 : F) := by
        have h3 : x = -(1 : F) := eq_neg_of_add_eq_zero_right hthis
        rwa [CharTwo.neg_eq] at h3
      simp [h2]
  have hle : (Finset.univ : Finset F).card ≤ ({0, 1} : Finset F).card :=
    Finset.card_le_card hsub
  rw [Finset.card_univ, hF] at hle
  have h2 : ({0, 1} : Finset F).card ≤ 2 := by
    calc ({0, 1} : Finset F).card ≤ ({1} : Finset F).card + 1 := Finset.card_insert_le 0 {1}
      _ ≤ 1 + 1 := by simp
      _ = 2 := by norm_num
  omega

private theorem k328r7g_S_iso (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2] (hF : Fintype.card F = 8)
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]))
    (hσ : IsUnitaryInvolution (starRingAut (R := k328r7g_L F)))
    (hs : ∃ s : k328r7g_L F, s ≠ 0 ∧ starRingAut (R := k328r7g_L F) s * s ≠ 1)
    {a : Fin 3 ⊕ Fin 3 → F} (ha0 : a ≠ 0) (hNa : k328r7g_N F a = 0) :
    a ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
  obtain ⟨s, hbs⟩ := k328r7g_exists_basis_nonorth F ha0
  set b : Fin 3 ⊕ Fin 3 → F := Pi.single s 1 with hbdef
  have hbS : b ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
    rcases s with j | j
    · rw [hbdef, ← k328r7g_phi_single_one F j]
      exact k328r7g_S_coord F hz ht j 1 one_ne_zero
    · rw [hbdef, ← k328r7g_phi_single_omega F j]
      exact k328r7g_S_coord F hz ht j (k328r7g_omega F) (k328r7g_omega_ne_zero F)
  obtain ⟨d, hd0, hd1⟩ := k328r7g_exists_d F hF
  set β : F := spForm 3 F a b with hβdef
  have hβ : β ≠ 0 := hbs
  have hNb : k328r7g_N F b = 1 := by
    rw [hbdef]; exact k328r7g_N_single F s
  have hNne : k328r7g_N F (a + (d * β) • b) ≠ 0 := by
    rw [k328r7g_N_add, hNa, hNb, zero_add, mul_one]
    have heq : d * β * spForm 3 F a b + (d * β) ^ 2 = d * β ^ 2 * (1 + d) := by
      rw [hβdef]; ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero hd0 (pow_ne_zero 2 hβ)) hd1
  have hsp : spTrans b d *ᵥ a = a + (d * β) • b := by
    rw [spTrans_mulVec, hβdef]
  have hSsp : spTrans b d *ᵥ a ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
    rw [hsp]
    exact k328r7g_S_nonIso F hz ht hσ hs hNne
  have hfix : (spTrans b d)⁻¹ • (spTrans b d *ᵥ a) = a := by
    rw [show spTrans b d *ᵥ a = spTrans b d • a from rfl, inv_smul_smul]
  rw [← hfix]
  exact k328r7g_S_stable F (k328r7g_J_le F z₀ t₀) hSsp
    ((k328r7g_J F z₀ t₀).inv_mem (hbS.2 d))

private theorem k328r7g_S_all (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r)] [CharP F 2] (hF : Fintype.card F = 8)
    {z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]))
    (hσ : IsUnitaryInvolution (starRingAut (R := k328r7g_L F)))
    (hs : ∃ s : k328r7g_L F, s ≠ 0 ∧ starRingAut (R := k328r7g_L F) s * s ≠ 1) :
    ∀ a : Fin 3 ⊕ Fin 3 → F, a ≠ 0 → a ∈ k328r7g_S F (k328r7g_J F z₀ t₀) := by
  intro a ha0
  by_cases hNa : k328r7g_N F a = 0
  · exact k328r7g_S_iso F hF hz ht hσ hs ha0 hNa
  · exact k328r7g_S_nonIso F hz ht hσ hs hNa

theorem row7_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    GenLeaf (StatedSp 3 F) z₀ t₀ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have hFact : Fact (∀ r : F, r ^ 2 ≠ (1 : F) + 1 * r) := ⟨k328r7g_aniso F hF⟩
  let : Field (k328r7g_L F) := inferInstance
  let : Fintype (k328r7g_L F) :=
    Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd (1 : F) 1).symm
  have : CharP (k328r7g_L F) 2 :=
    charP_of_injective_algebraMap (R := F) (A := k328r7g_L F) (p := 2)
      (fun x y h => by
        have := congrArg QuadraticAlgebra.re h
        simpa using this)
  have hcardL : Nat.card (k328r7g_L F) = 64 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (1 : F) 1), Nat.card_prod,
      Nat.card_eq_fintype_card, hF]
  have hσ : IsUnitaryInvolution (starRingAut (R := k328r7g_L F)) :=
    k328r7g_isUnitary_star F hF hcardL
  have hs : ∃ s : k328r7g_L F, s ≠ 0 ∧ starRingAut (R := k328r7g_L F) s * s ≠ 1 :=
    k328r7g_exists_norm_ne_one F hF hcardL
  rw [GenLeaf]
  apply le_antisymm
  · exact k328r7g_J_le F z₀ t₀
  · conv_lhs => rw [statedSp_eq_closure_spTrans]
    rw [Subgroup.closure_le]
    rintro g ⟨a, c, rfl⟩
    by_cases ha : a = 0
    · subst ha
      rw [spTrans_zero_vec]
      exact Subgroup.one_mem _
    · exact (k328r7g_S_all F hF hz ht hσ hs a ha).2 c

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
