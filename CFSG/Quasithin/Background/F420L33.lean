module

public import CFSG.Quasithin.Background.F420L2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear

public section

namespace CFSG.Quasithin.F420

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.QuasithinUnique.K1 CFSG.Assembly.LowTwoRank CFSG.ComponentClassification

variable {K : Type} [Field K]

section Three

variable [Finite K]

theorem charP_three_of_card_three (hK : Nat.card K = 3) : CharP K 3 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

theorem two_ne_zero_of_card_three (hK : Nat.card K = 3) : (2 : K) ≠ 0 := by
  have := charP_three_of_card_three hK
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h2
  omega

theorem eq_zero_or_one_or_neg_one_of_card_three (hK : Nat.card K = 3) (c : K) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 := two_ne_zero_of_card_three hK
  have h1 : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have h0 : (0 : K) ≠ -1 := by
    intro h
    exact one_ne_zero (by linear_combination h)
  have hc : ({0, 1, -1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_insert_of_notMem (by simp [h0]), Finset.card_pair h1, ←
      Nat.card_eq_fintype_card, hK]
  have h := Finset.eq_univ_of_card _ hc
  have hc' : c ∈ ({0, 1, -1} : Finset K) := h ▸ Finset.mem_univ c
  simpa using hc'

theorem scalars_three_eq_bot (hK : Nat.card K = 3) : scalars 3 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have h2 := two_ne_zero_of_card_three hK
  have hc1 : (c : K) = 1 := by
    have hc3 : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    rcases eq_zero_or_one_or_neg_one_of_card_three hK (c : K) with h | h | h
    · rw [h] at hc3
      norm_num at hc3
    · exact h
    · exfalso
      rw [h] at hc3
      apply h2
      linear_combination -hc3
  rw [Subgroup.mem_bot]
  ext i j
  rw [hA, hc1, map_one]
  rfl

theorem proj_injective_three (hK : Nat.card K = 3) : Function.Injective (proj 3 K) := by
  intro a b h
  rw [proj_eq_proj_iff, scalars_three_eq_bot hK, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

end Three

section Matrices

@[expose] def l33rM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 1, 0; 0, 0, -1]

@[expose] def l33rInvM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![-1, 1, 0; 1, 0, 0; 0, 0, -1]

@[expose] def l33sM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 1, -1, 0; 0, 0, -1]

@[expose] def l33zM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem l33rM_mul_rInvM : l33rM K * l33rInvM K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l33rM, l33rInvM, Matrix.mul_apply, Fin.sum_univ_three]

theorem l33sM_mul_sM : l33sM K * l33sM K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l33sM, Matrix.mul_apply, Fin.sum_univ_three]

theorem l33zM_mul_zM : l33zM K * l33zM K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l33zM, Matrix.mul_apply, Fin.sum_univ_three]

variable [CharP K 3]

theorem three_eq_zero_of_charP : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

theorem l33rM_pow_four : l33rM K * l33rM K * (l33rM K * l33rM K) = l33zM K := by
  have h3 : (3 : K) = 0 := three_eq_zero_of_charP
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l33rM, l33zM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination h3 | linear_combination 2 * h3

theorem l33sM_conj : l33sM K * l33rM K * l33sM K = l33rM K * l33rM K * l33rM K := by
  have h3 : (3 : K) = 0 := three_eq_zero_of_charP
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l33rM, l33sM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination -h3

end Matrices

theorem eq_diag_of_commute (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 3) (Fin 3) K)
    (hr : A * l33rM K = l33rM K * A) (hs : A * l33sM K = l33sM K * A) :
    A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 1 1 = A 0 0 := by
  have e := fun i j => congrFun (congrFun hr i) j
  have e02 := e 0 2
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e00 := e 0 0
  have e01 := e 0 1
  simp [l33rM, Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21 e00 e01
  have f01 := congrFun (congrFun hs 0) 1
  simp [l33sM, Matrix.mul_apply, Fin.sum_univ_three] at f01
  have hA01 : A 0 1 = 0 := by
    have : (2 : K) * A 0 1 = 0 := by linear_combination -f01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hA02 : A 0 2 = 0 := by linear_combination e12 - 2 * e02
  have hA20 : A 2 0 = 0 := by linear_combination -e21 + 2 * e20
  refine ⟨hA01, hA02, ?_, ?_, hA20, ?_, ?_⟩
  · rw [← e00, hA01]
  · linear_combination -e02 - hA02
  · linear_combination e20 - hA20
  · rw [← e01, hA01, add_zero]

section Elements

@[expose] def l33r : SpecialLinearGroup (Fin 3) K :=
  ⟨l33rM K, by simp [l33rM, Matrix.det_fin_three]⟩

@[expose] def l33rInv : SpecialLinearGroup (Fin 3) K :=
  ⟨l33rInvM K, by simp [l33rInvM, Matrix.det_fin_three]⟩

@[expose] def l33s : SpecialLinearGroup (Fin 3) K :=
  ⟨l33sM K, by simp [l33sM, Matrix.det_fin_three]⟩

@[expose] def l33z : SpecialLinearGroup (Fin 3) K :=
  ⟨l33zM K, by simp [l33zM, Matrix.det_fin_three]⟩

theorem l33r_inv : (l33r : SpecialLinearGroup (Fin 3) K)⁻¹ = l33rInv := by
  rw [inv_eq_of_mul_eq_one_right]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun l33rM_mul_rInvM i) j

theorem l33s_sq : (l33s : SpecialLinearGroup (Fin 3) K) ^ 2 = 1 := by
  rw [sq]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun l33sM_mul_sM i) j

theorem l33z_sq : (l33z : SpecialLinearGroup (Fin 3) K) ^ 2 = 1 := by
  rw [sq]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun l33zM_mul_zM i) j

variable [CharP K 3]

theorem l33r_pow_four : (l33r : SpecialLinearGroup (Fin 3) K) ^ 4 = l33z := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun l33rM_pow_four i) j

theorem l33r_pow_eight : (l33r : SpecialLinearGroup (Fin 3) K) ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, l33r_pow_four, l33z_sq]

theorem l33s_conj :
    (l33s : SpecialLinearGroup (Fin 3) K) * l33r * l33s⁻¹ = l33r ^ 3 := by
  have hs : (l33s : SpecialLinearGroup (Fin 3) K)⁻¹ = l33s := by
    rw [inv_eq_iff_mul_eq_one, ← sq, l33s_sq]
  rw [hs, pow_succ, sq]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun l33sM_conj i) j

end Elements

section Proj

variable [Finite K]

@[expose] noncomputable def l33Pr (_hK : Nat.card K = 3) : projectiveSL 3 K :=
  proj 3 K l33r

@[expose] noncomputable def l33Ps (_hK : Nat.card K = 3) : projectiveSL 3 K :=
  proj 3 K l33s

@[expose] noncomputable def l33Pz (_hK : Nat.card K = 3) : projectiveSL 3 K :=
  proj 3 K l33z

theorem commute_of_proj (hK : Nat.card K = 3) (g : SpecialLinearGroup (Fin 3) K)
    (hr : proj 3 K g * l33Pr hK = l33Pr hK * proj 3 K g)
    (hs : proj 3 K g * l33Ps hK = l33Ps hK * proj 3 K g) :
    (g : Matrix (Fin 3) (Fin 3) K) * l33rM K = l33rM K * g ∧
      (g : Matrix (Fin 3) (Fin 3) K) * l33sM K = l33sM K * g := by
  have := charP_three_of_card_three hK
  have hinj := proj_injective_three hK
  rw [l33Pr, ← map_mul, ← map_mul] at hr
  rw [l33Ps, ← map_mul, ← map_mul] at hs
  have hr' := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K))
    (hinj hr)
  have hs' := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K))
    (hinj hs)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hr' hs'
  exact ⟨hr', hs'⟩

theorem centralizer_T_l33 (hK : Nat.card K = 3) (x : projectiveSL 3 K)
    (hr : x * l33Pr hK = l33Pr hK * x) (hs : x * l33Ps hK = l33Ps hK * x) :
    x = 1 ∨ x = l33Pz hK := by
  have := charP_three_of_card_three hK
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  obtain ⟨hr', hs'⟩ := commute_of_proj hK g hr hs
  obtain ⟨h01, h02, h10, h12, h20, h21, h11⟩ :=
    eq_diag_of_commute (two_ne_zero_of_card_three hK) _ hr' hs'
  have hdet := g.2
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, h11] at hdet
  have ha : (g : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 2 = 1 := by
    rcases eq_zero_or_one_or_neg_one_of_card_three hK ((g : Matrix (Fin 3) (Fin 3) K) 0 0) with
      h | h | h
    · rw [h] at hdet
      simp at hdet
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hw : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have : (g : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 2 * (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      linear_combination hdet
    rw [ha, one_mul] at this
    exact this
  rcases eq_zero_or_one_or_neg_one_of_card_three hK ((g : Matrix (Fin 3) (Fin 3) K) 0 0) with
    h | h | h
  · rw [h] at ha
    norm_num at ha
  · left
    have : g = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, h11, h, hw]
    rw [this, map_one]
  · right
    have : g = l33z := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [l33z, l33zM, h01, h02, h10, h12, h20, h21, h11, h, hw]
    rw [this]
    rfl

theorem isPGroup_l33T (hK : Nat.card K = 3) :
    IsPGroup 2 (Subgroup.closure {l33Pr hK, l33Ps hK}) := by
  have := charP_three_of_card_three hK
  refine isPGroup_closure_pair (n := 3) (k := 3) ?_ ?_ ?_
  · rw [l33Pr, ← map_pow, show (2 ^ 3 : ℕ) = 8 from rfl, l33r_pow_eight, map_one]
  · rw [l33Ps, ← map_pow, l33s_sq, map_one]
  · rw [l33Pr, l33Ps, ← map_inv, ← map_mul, ← map_mul, l33s_conj, map_pow]

theorem smallCentralizerWitness_l33 (hK : Nat.card K = 3) :
    SmallCentralizerWitness (projectiveSL 3 K) :=
  ⟨Subgroup.closure {l33Pr hK, l33Ps hK}, l33Pz hK, isPGroup_l33T hK, fun x hx =>
    centralizer_T_l33 hK x (hx _ (Subgroup.subset_closure (Set.mem_insert _ _)))
      (hx _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))⟩

omit [Finite K] in
theorem conj_eq_of_eq_smul (A : GL (Fin 3) K) {c : K} {M : Matrix (Fin 3) (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = c • M) (hM : M * M = 1)
    (g : Matrix (Fin 3) (Fin 3) K) :
    (A : Matrix (Fin 3) (Fin 3) K) * g * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      M * g * M := by
  have h1 : (A : Matrix (Fin 3) (Fin 3) K) * g = (M * g * M) * (A : Matrix (Fin 3) (Fin 3) K) := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc (M * g), hM, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem inner_of_fix_T_l33 (hK : Nat.card K = 3) (β : MulAut (projectiveSL 3 K))
    (hr : β (l33Pr hK) = l33Pr hK) (hs : β (l33Ps hK) = l33Ps hK) :
    ∃ x : projectiveSL 3 K, ∀ y : projectiveSL 3 K, β y = x⁻¹ * y * x := by
  have := charP_three_of_card_three hK
  have hinj := proj_injective_three hK
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen β
  have hσ : fieldAut 3 K σ = 1 := by
    rw [ringEquiv_eq_refl_of_card_prime Nat.prime_three hK σ]
    exact map_one (fieldAut 3 K)
  rw [hσ, mul_one] at hβ
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hβ
    have hconj : ∀ g : SpecialLinearGroup (Fin 3) K,
        ((CatalogueBHigherLinearAction.slConjugation 3 K A g : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 3) (Fin 3) K) * g *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      fun g => coe_slConjugation A g
    have hfix : ∀ g : SpecialLinearGroup (Fin 3) K, β (proj 3 K g) = proj 3 K g →
        (A : Matrix (Fin 3) (Fin 3) K) * g = g * (A : Matrix (Fin 3) (Fin 3) K) := by
      intro g hg
      rw [hβ, conjAut_proj] at hg
      have h1 := congrArg (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K))
        (hinj hg)
      simp only [hconj] at h1
      calc (A : Matrix (Fin 3) (Fin 3) K) * g =
          ((A : Matrix (Fin 3) (Fin 3) K) * g *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * A := by
            rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) K), ← Units.val_mul,
              inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = g * (A : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
    have hAr := hfix l33r hr
    have hAs := hfix l33s hs
    obtain ⟨h01, h02, h10, h12, h20, h21, h11⟩ :=
      eq_diag_of_commute (two_ne_zero_of_card_three hK) _ hAr hAs
    have ha0 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
      intro h0
      have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by
        rw [Matrix.det_fin_three, h01, h02, h0]
        ring
      have hu := (A.isUnit.map (Matrix.detMonoidHom (n := Fin 3) (R := K)))
      simp only [Matrix.coe_detMonoidHom] at hu
      rw [hdet] at hu
      exact not_isUnit_zero hu
    set a := (A : Matrix (Fin 3) (Fin 3) K) 0 0
    set w := (A : Matrix (Fin 3) (Fin 3) K) 2 2
    have hw0 : w ≠ 0 := by
      intro h0
      have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 0 := by
        rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, show
          (A : Matrix (Fin 3) (Fin 3) K) 2 2 = w from rfl, h0]
        ring
      have hu := (A.isUnit.map (Matrix.detMonoidHom (n := Fin 3) (R := K)))
      simp only [Matrix.coe_detMonoidHom] at hu
      rw [hdet] at hu
      exact not_isUnit_zero hu
    have hc : w * a⁻¹ = 1 ∨ w * a⁻¹ = -1 := by
      rcases eq_zero_or_one_or_neg_one_of_card_three hK (w * a⁻¹) with h | h | h
      · exact absurd h (mul_ne_zero hw0 (inv_ne_zero ha0))
      · exact Or.inl h
      · exact Or.inr h
    rcases hc with hc | hc
    ·
      have hwa : w = a := by
        have := congrArg (· * a) hc
        simpa [mul_assoc, inv_mul_cancel₀ ha0] using this
      have hA : (A : Matrix (Fin 3) (Fin 3) K) = a • (1 : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h02, h10, h12, h20, h21, h11, a, ← hwa, w]
      refine ⟨1, fun y => ?_⟩
      obtain ⟨g, rfl⟩ := proj_surjective 3 K y
      rw [inv_one, one_mul, mul_one, hβ, conjAut_proj]
      congr 1
      ext i j
      rw [hconj, conj_eq_of_eq_smul A hA (Matrix.mul_one 1), Matrix.one_mul, Matrix.mul_one]
    ·
      have hwa : w = -a := by
        have := congrArg (· * a) hc
        simpa [mul_assoc, inv_mul_cancel₀ ha0] using this
      have hA : (A : Matrix (Fin 3) (Fin 3) K) = (-a) • l33zM K := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [l33zM, h01, h02, h10, h12, h20, h21, h11, a, hwa, w]
      have hzinv : (l33Pz hK)⁻¹ = l33Pz hK := by
        rw [inv_eq_iff_mul_eq_one, ← sq, l33Pz, ← map_pow, l33z_sq, map_one]
      refine ⟨l33Pz hK, fun y => ?_⟩
      obtain ⟨g, rfl⟩ := proj_surjective 3 K y
      rw [hzinv, hβ, conjAut_proj, l33Pz, ← map_mul, ← map_mul]
      congr 1
      ext i j
      rw [hconj, conj_eq_of_eq_smul A hA l33zM_mul_zM, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul]
      rfl
  ·
    exfalso
    rw [pow_one] at hβ
    rw [hβ, MulAut.mul_apply, l33Pr, dualAut_proj, conjAut_proj] at hr
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K))
      (hinj hr)
    simp only [coe_slConjugation] at h1
    have htr := congrArg Matrix.trace h1
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, l33r_inv] at htr
    change Matrix.trace (l33rInvM K)ᵀ = Matrix.trace (l33rM K) at htr
    rw [Matrix.trace_transpose] at htr
    simp [l33rInvM, l33rM, Matrix.trace, Fin.sum_univ_three] at htr
    have h3 : (3 : K) = 0 := three_eq_zero_of_charP
    exact one_ne_zero (by linear_combination htr + h3)

theorem noFourCentralizing_projectiveSL_three (hK : Nat.card K = 3) :
    NoFourCentralizing (projectiveSL 3 K) := by
  refine noFourCentralizing_of_inner (fun S hS α hα => ?_) (smallCentralizerWitness_l33 hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := (isPGroup_l33T hK).exists_le_sylow
  have hQ : CFSG.QuasithinUnique.IsSylowTwoOf (Q : Subgroup (projectiveSL 3 K)) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨Q.isPGroup', Q.not_dvd_index⟩
  refine sylowCentralizingAutInner_of_sylow _ hQ (fun β hβ => ?_) S
    (isSylowTwoOf_top_iff.mpr hS) α hα
  exact inner_of_fix_T_l33 hK β (hβ _ (hTQ (Subgroup.subset_closure (Set.mem_insert _ _))))
    (hβ _ (hTQ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))))

end Proj

noncomputable def statedSLEquivProjectiveSLThree :
    ↥(StatedSL 3 (ZMod 3)) ≃* projectiveSL 3 (ZMod 3) :=
  (specialLinearGroupEquivStatedSL 3 (ZMod 3)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (scalars_three_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).symm

theorem noFourCentralizing_of_l33 {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3)))) :
    NoFourCentralizing X := by
  rcases h with ⟨-, K, _, _, hK, ⟨e⟩⟩ | h
  · rw [pow_one] at hK
    exact NoFourCentralizing.of_mulEquiv (e.trans (statedProjEquivProjectiveSL 3 K))
      (noFourCentralizing_projectiveSL_three hK)
  · obtain ⟨e⟩ := h
    exact NoFourCentralizing.of_mulEquiv (e.trans statedSLEquivProjectiveSLThree)
      (noFourCentralizing_projectiveSL_three (by simp))

end CFSG.Quasithin.F420
