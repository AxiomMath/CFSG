module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Fixed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix Polynomial

namespace RecipeFieldLang

section Descent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {τ : K ≃+* K}

theorem iterate_smul {T : V →+ V} (hsmul : ∀ (a : K) (v : V), T (a • v) = τ a • T v) (i : ℕ)
    (a : K) (v : V) : T^[i] (a • v) = (τ ^ i) a • T^[i] v := by
  induction i generalizing a v with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hsmul, pow_succ', RingAut.mul_apply,
      Function.iterate_succ_apply']

theorem span_fixed_eq_top (T : V →+ V) (hsmul : ∀ (a : K) (v : V), T (a • v) = τ a • T v)
    {p : ℕ} (hp : 0 < p) (hTp : ∀ v, T^[p] v = v) {θ : K}
    (hθ : ∀ i, 0 < i → i < p → (τ ^ i) θ ≠ θ) :
    Submodule.span K {v | T v = v} = ⊤ := by
  classical
  set P : V → V := fun w => ∑ i ∈ Finset.range p, T^[i] w with hPdef
  have hPfix : ∀ w, T (P w) = P w := by
    intro w
    have e1 : T (P w) = ∑ i ∈ Finset.range p, T^[i + 1] w := by
      rw [hPdef, map_sum]
      exact Finset.sum_congr rfl fun i _ => (Function.iterate_succ_apply' T i w).symm
    have h1 := Finset.sum_range_succ (fun i => T^[i] w) p
    have h2 := Finset.sum_range_succ' (fun i => T^[i] w) p
    rw [h1, hTp, Function.iterate_zero_apply] at h2
    rw [e1]
    exact (add_right_cancel h2).symm
  have hPsmul : ∀ (a : K) (v : V), P (a • v) = ∑ i ∈ Finset.range p, (τ ^ i) a • T^[i] v :=
    fun a v => Finset.sum_congr rfl fun i _ => iterate_smul hsmul i a v
  set L : K[X] := ∏ i ∈ Finset.Ioo 0 p, (X - C ((τ ^ i) θ)) with hLdef
  have hLθ : L.eval θ ≠ 0 := by
    rw [hLdef, eval_prod, Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_Ioo] at hi
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact (hθ i hi.1 hi.2).symm
  have hLτ : ∀ i ∈ Finset.range p, i ≠ 0 → L.eval ((τ ^ i) θ) = 0 := by
    intro i hi hi0
    rw [hLdef, eval_prod]
    refine Finset.prod_eq_zero (i := i) ?_ ?_
    · rw [Finset.mem_Ioo]
      exact ⟨Nat.pos_of_ne_zero hi0, Finset.mem_range.mp hi⟩
    · rw [eval_sub, eval_X, eval_C, sub_self]
  refine eq_top_iff.mpr fun v _ => ?_
  have h1 : ∑ k ∈ Finset.range (L.natDegree + 1), L.coeff k • P (θ ^ k • v) =
      ∑ i ∈ Finset.range p, L.eval ((τ ^ i) θ) • T^[i] v := by
    simp only [hPsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, eval_eq_sum_range]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [map_pow]
  have h2 : ∑ i ∈ Finset.range p, L.eval ((τ ^ i) θ) • T^[i] v = L.eval θ • v := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      rw [hLτ i hi hi0, zero_smul]
    · intro h
      exact absurd (Finset.mem_range.mpr hp) h
  have key : v = (L.eval θ)⁻¹ •
      ∑ k ∈ Finset.range (L.natDegree + 1), L.coeff k • P (θ ^ k • v) := by
    rw [h1, h2, smul_smul, inv_mul_cancel₀ hLθ, one_smul]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hPfix _)))

end Descent

open Module in
theorem exists_fixed_basis_of_span {K : Type*} [Field K] {n : ℕ} (T : (Fin n → K) → (Fin n → K))
    (hspan : Submodule.span K {v | T v = v} = ⊤) :
    ∃ H : GL (Fin n) K, ∀ c : Fin n,
      T (fun r => (H : Matrix (Fin n) (Fin n) K) r c) =
        fun r => (H : Matrix (Fin n) (Fin n) K) r c := by
  classical
  set Fix : Set (Fin n → K) := {v | T v = v} with hFix
  obtain ⟨b, hbFix, hbspan, hbli⟩ := exists_linearIndependent K Fix
  rw [hspan] at hbspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin n → K)) := by
    rw [Subtype.range_coe, hbspan]
  let bas₀ := Basis.mk hbli hsp
  let _ := FiniteDimensional.fintypeBasisIndex bas₀
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bas₀, Module.finrank_fin_fun]
  let bas := bas₀.reindex (Fintype.equivFinOfCardEq hcard)
  have hbas : ∀ c, T (bas c) = bas c := fun c => by
    rw [Basis.reindex_apply, Basis.mk_apply]
    exact hbFix (Subtype.mem _)
  obtain ⟨Hm, hHm⟩ : ∃ Hm : Matrix (Fin n) (Fin n) K, Hm = Matrix.of fun r c => bas c r :=
    ⟨_, rfl⟩
  have hHunit : IsUnit Hm := by
    rw [← mulVec_surjective_iff_isUnit]
    intro u
    refine ⟨bas.repr u, ?_⟩
    conv_rhs => rw [← bas.sum_repr u]
    ext r
    simp only [hHm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  refine ⟨hHunit.unit, fun c => ?_⟩
  have hcol : (fun r => (hHunit.unit : Matrix (Fin n) (Fin n) K) r c) = bas c := by
    rw [IsUnit.unit_spec, hHm]
    rfl
  rw [hcol]
  exact hbas c

theorem exists_prod_range_pow_eq {K : Type} [Field K] [Finite K] {τ : K ≃+* K} {p : ℕ}
    (hτ : orderOf τ = p) (hp : 0 < p) {c : K} (hc : τ c = c) :
    ∃ b : K, ∏ i ∈ Finset.range p, (τ ^ i) b = c := by
  classical
  have hfin : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  let G : Subgroup (K ≃+* K) := Subgroup.zpowers τ
  have : Finite G := inferInstance
  have : Fintype G := Fintype.ofFinite G
  let F₀ := FixedPoints.subfield G K
  have hcF : c ∈ F₀ := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hfix : ∀ m : ℕ, (τ ^ m) c = c := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, RingAut.mul_apply, hc, ih]
    change (τ ^ k) c = c
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast]
      exact hfix m
    · rw [_root_.zpow_neg, zpow_natCast]
      conv_lhs => rw [← hfix m]
      exact (τ ^ m).symm_apply_apply c
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective F₀ K ⟨c, hcF⟩
  refine ⟨b, ?_⟩
  have h1 := Algebra.norm_eq_prod_automorphisms F₀ b
  rw [hb] at h1
  change c = _ at h1
  rw [h1]
  have hord : IsOfFinOrder τ := orderOf_pos_iff.mp (hτ ▸ hp)
  rw [← Fintype.prod_equiv (FixedPoints.toAlgAutMulEquiv G K).toEquiv (fun g => g • b) _
    (fun g => rfl)]
  rw [← Fintype.prod_equiv (finEquivZPowers hord) (fun i => (τ ^ (i : ℕ)) b) _ (fun i => rfl)]
  rw [Fin.prod_univ_eq_prod_range (fun i => (τ ^ i) b), hτ]

section Norm

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def normSeq (τ : K ≃+* K) (A : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | k + 1 => normSeq τ A k * GeneralLinearGroup.map ((τ ^ k : K ≃+* K) : K →+* K) A

theorem normSeq_zero (τ : K ≃+* K) (A : GL (Fin n) K) : normSeq τ A 0 = 1 := rfl

theorem normSeq_succ (τ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    normSeq τ A (k + 1) =
      normSeq τ A k * GeneralLinearGroup.map ((τ ^ k : K ≃+* K) : K →+* K) A := rfl

theorem pow_conjAut_mul_fieldAut (A : GL (Fin n) K) (τ : K ≃+* K) (k : ℕ) :
    (conjAut n K A * fieldAut n K τ) ^ k =
      conjAut n K (normSeq τ A k) * fieldAut n K (τ ^ k) := by
  induction k with
  | zero => rw [pow_zero, normSeq_zero, map_one, pow_zero, map_one, one_mul]
  | succ k ih => rw [pow_succ, ih, conjAut_mul_fieldAut_mul, ← normSeq_succ, ← pow_succ]

theorem map_map_pow (τ : K ≃+* K) (k : ℕ) (A : GL (Fin n) K) :
    GeneralLinearGroup.map (τ : K →+* K) (GeneralLinearGroup.map ((τ ^ k : K ≃+* K) : K →+* K) A) =
      GeneralLinearGroup.map ((τ ^ (k + 1) : K ≃+* K) : K →+* K) A := by
  ext i j
  simp [pow_succ', RingAut.mul_apply]

theorem normSeq_succ' (τ : K ≃+* K) (A : GL (Fin n) K) (k : ℕ) :
    normSeq τ A (k + 1) = A * GeneralLinearGroup.map (τ : K →+* K) (normSeq τ A k) := by
  induction k with
  | zero =>
    rw [normSeq_succ, normSeq_zero, one_mul, map_one, mul_one]
    ext i j
    simp
  | succ k ih =>
    conv_lhs => rw [normSeq_succ, ih]
    conv_rhs => rw [normSeq_succ, map_mul, map_map_pow]
    rw [mul_assoc]

theorem normSeq_scalar_mul (τ : K ≃+* K) (u : Kˣ) (A : GL (Fin n) K) (k : ℕ) :
    normSeq τ (GeneralLinearGroup.scalar (Fin n) u * A) k =
      GeneralLinearGroup.scalar (Fin n)
        (∏ i ∈ Finset.range k, Units.map ((τ ^ i : K ≃+* K) : K →* K) u) * normSeq τ A k := by
  induction k with
  | zero => rw [normSeq_zero, normSeq_zero, Finset.prod_range_zero, map_one, mul_one]
  | succ k ih =>
    rw [normSeq_succ, ih, normSeq_succ, map_mul, GeneralLinearGroup.map_scalar,
      Finset.prod_range_succ, map_mul]
    rw [mul_assoc, ← mul_assoc (normSeq τ A k), ← GeneralLinearGroup.scalar_commute]
    simp only [mul_assoc]
    rfl

end Norm

theorem lang_field_linear {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hpar : 3 ≤ n ∨ 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (A : GL (Fin n) K) (τ : K ≃+* K)
    (hτ1 : τ ≠ 1) (hα : (conjAut n K A * fieldAut n K τ) ^ p = 1) :
    orderOf (fieldAut n K τ) = p ∧ ∃ H : GL (Fin n) K,
      conjAut n K A * fieldAut n K τ = conjAut n K H * fieldAut n K τ * (conjAut n K H)⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rw [pow_conjAut_mul_fieldAut] at hα
  obtain ⟨hτp, c, hc⟩ := RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' hn hpar _ _ hα
  have hordτ : orderOf τ = p := orderOf_eq_prime hτp hτ1
  have hp0 : 0 < p := hp.pos
  have hf1 : fieldAut n K τ ≠ 1 := by
    intro h1
    exact hτ1 (RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' hn hpar 1 τ
      (by rw [map_one, one_mul, h1])).1
  refine ⟨orderOf_eq_prime (by rw [← map_pow, hτp, map_one]) hf1, ?_⟩
  have hNp1 : normSeq τ A (p + 1) = GeneralLinearGroup.scalar (Fin n) c * A := by
    rw [normSeq_succ, hτp, ← hc]
    congr 1
  have h3 : A * GeneralLinearGroup.map (τ : K →+* K) (GeneralLinearGroup.scalar (Fin n) c) =
      A * GeneralLinearGroup.scalar (Fin n) c := by
    conv_lhs => rw [hc, ← normSeq_succ', hNp1, GeneralLinearGroup.scalar_commute]
  rw [GeneralLinearGroup.map_scalar] at h3
  have h4 := congrArg (fun g : GL (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) (mul_left_cancel h3)
  have hcfix : τ (c : K) = c := by
    simpa [GeneralLinearGroup.coe_scalar] using h4
  obtain ⟨b, hb⟩ := exists_prod_range_pow_eq hordτ hp0 (c := ((c⁻¹ : Kˣ) : K))
    (by rw [Units.val_inv_eq_inv_val, map_inv₀, hcfix])
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hp0) (by rw [map_zero])] at hb
    exact (Units.ne_zero _) hb.symm
  set u := Units.mk0 b hb0 with hu
  set B := GeneralLinearGroup.scalar (Fin n) u * A with hB
  have hcB : conjAut n K B = conjAut n K A := by rw [hB, map_mul, conjAut_scalar, one_mul]
  have hprod : (∏ i ∈ Finset.range p, Units.map ((τ ^ i : K ≃+* K) : K →* K) u) = c⁻¹ := by
    ext
    rw [Units.coe_prod]
    simpa [hu] using hb
  have hNB : normSeq τ B p = 1 := by
    rw [hB, normSeq_scalar_mul, hprod, ← hc, ← map_mul, inv_mul_cancel, map_one]
  let T : (Fin n → K) →+ (Fin n → K) :=
    { toFun := fun v => (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => τ (v i)
      map_zero' := by
        show (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => τ ((0 : Fin n → K) i)) = 0
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add]
        rw [← mulVec_add]
        rfl }
  have hTapp : ∀ v, T v = (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => τ (v i) := fun _ => rfl
  have hsmul : ∀ (a : K) (v : Fin n → K), T (a • v) = τ a • T v := fun a v => by
    rw [hTapp, hTapp]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← mulVec_smul]
    rfl
  have hTk : ∀ (k : ℕ) (v : Fin n → K),
      T^[k] v = (normSeq τ B k : Matrix (Fin n) (Fin n) K) *ᵥ fun i => (τ ^ k) (v i) := by
    intro k
    induction k with
    | zero => intro v; simp [normSeq_zero]
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, normSeq_succ' τ B k, hTapp]
      have hσ : (fun i => τ (((normSeq τ B k : Matrix (Fin n) (Fin n) K) *ᵥ
          fun j => (τ ^ k) (v j)) i)) =
          ((normSeq τ B k : Matrix (Fin n) (Fin n) K).map τ) *ᵥ fun j => (τ ^ (k + 1)) (v j) := by
        funext i
        have h1 := RingHom.map_mulVec (τ : K →+* K) (normSeq τ B k : Matrix (Fin n) (Fin n) K)
          (fun j => (τ ^ k) (v j)) i
        simp only [RingEquiv.coe_toRingHom] at h1
        rw [h1]
        congr 1
        funext j
        rw [pow_succ', RingAut.mul_apply]
        rfl
      rw [hσ, mulVec_mulVec]
      rfl
  have hTp : ∀ v, T^[p] v = v := by
    intro v
    rw [hTk, hNB, hτp]
    simp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hθ : ∀ i, 0 < i → i < p → (τ ^ i) (g : K) ≠ g := by
    intro i hi0 hip heq
    have hfixu : ∀ x : Kˣ, (τ ^ i) (x : K) = x := by
      intro x
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, heq]
    have h1 : τ ^ i = 1 := by
      ext x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · exact hfixu (Units.mk0 x hx)
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hordτ] at hdvd
    exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)
  obtain ⟨H, hH⟩ := exists_fixed_basis_of_span T (span_fixed_eq_top T hsmul hp0 hTp hθ)
  have hBH : B * GeneralLinearGroup.map (τ : K →+* K) H = H := by
    ext r c
    have := congrFun (hH c) r
    rw [hTapp] at this
    simp only [mulVec, dotProduct] at this
    rw [← this]
    simp [Matrix.mul_apply]
  have hBeq : B = H * (GeneralLinearGroup.map (τ : K →+* K) H)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hBH
  refine ⟨H, ?_⟩
  have hfH : conjAut n K (GeneralLinearGroup.map (τ : K →+* K) H)⁻¹ * fieldAut n K τ =
      fieldAut n K τ * conjAut n K H⁻¹ := by
    rw [← map_inv, ← hfc τ H⁻¹]
    group
  rw [← hcB, hBeq, map_mul, mul_assoc, hfH, ← mul_assoc, map_inv]

theorem ggRawFieldConj_linear {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 2 ≤ d)
    (hpar : 3 ≤ d ∨ 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) :
    GGRawFieldConj p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  intro _ _ u hu f hf huf hp1
  set E := MulAut.congr (TypeA.recipeEquiv d K) with hE
  obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hu
  have hFle : Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) ≤
        (fieldAut d K).range.comap E.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨σ, hσ⟩ := RecipeFieldLinear.congr_field_eq hg
    exact ⟨σ, hσ.symm⟩
  obtain ⟨τ, hτ⟩ := hFle hf
  have hEuf : E (u * f) = conjAut d K A * fieldAut d K τ := by
    rw [map_mul, hA]
    congr 1
    exact hτ.symm
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply huf
    have e : E (u * f) = conjAut d K A := by rw [hEuf, map_one, mul_one]
    have hmem := NbrGraphLinear.symm_congr_conjAut_mem (K := K) A
    rwa [← e, MulEquiv.symm_apply_apply] at hmem
  have hαp : (conjAut d K A * fieldAut d K τ) ^ p = 1 := by
    rw [← hEuf, ← map_pow, hp1, map_one]
  obtain ⟨hord, H, hH⟩ := lang_field_linear hd hpar hp A τ hτ1 hαp
  refine ⟨E.symm (fieldAut d K τ), NbrGraphLinear.symm_congr_fieldAut_mem τ,
    E.symm (conjAut d K H), NbrGraphLinear.symm_congr_conjAut_mem H, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hord
  · apply E.injective
    rw [hEuf, hH, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end RecipeFieldLang

open RecipeFieldLang

theorem ggRawFieldConjOn_linear : GGRawFieldConjOn fun _ => GGLinearRecipeLabel := by
  intro p hp _ lab hlab hS Q₀ h
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · obtain ⟨hl1, hl2⟩ : 1 ≤ l ∧ (l = 1 → 2 ≤ n) := hlab.2
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawFieldConj_linear (by omega) (three_le_or_four_le_of_typeA hl1 hl2 hK) hp
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ?_) h
    exact ggRawFieldConj_linear (by omega) (Or.inl (by omega)) hp
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawFieldConj_linear le_rfl (Or.inr (four_le_card_of_sq hlab.1 hK)) hp

end CFSG.StandardType

end
