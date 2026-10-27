module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LieType.RootSystem.Form
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Extras
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Universal.SpecialLinearExtras
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.IntervalCases

public section


namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.Minuscule

open scoped commutatorElement

open Matrix

section FormAux

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem symmetrized_apply {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (i j : I) :
    symmetrized hA i j = symmetrizer hA i * (A i j : ℚ) := by
  have h1 : form hA (Pi.single i 1) (Pi.single j 1) = symmetrized hA i j := by
    rw [form_apply, single_dotProduct, one_mul, Matrix.mulVec]
    simp [Pi.single_apply]
  have h2 : form hA (Pi.single i 1) (Pi.single j 1) = symmetrizer hA i * (A i j : ℚ) := by
    rw [CFSG.LieType.RootSystem.form_single_left]
    congr 1
    simp [Pi.single_apply]
  rw [← h1, h2]

private theorem cartan_symm_of_conn {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hA)) : A.IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have hsl := hconn.1 i j hij
    have hm : (coxeterMatrix hA).M i j ≤ 3 := by rcases hsl with h | h <;> omega
    have hmem := hA.apply_mul_apply_mem_of_ne hij
    have hco : (coxeterMatrix hA).M i j = TauCeti.coxeterOrder (A i j * A j i) := by
      simpa only [coxeterMatrix] using
        TauCeti.coxeterMatrixOfCartanMatrix_apply A hA.apply_self
          (fun i j hij => hA.apply_mul_apply_mem_of_ne hij) i j
    have hprod : A i j * A j i = 0 ∨ A i j * A j i = 1 := by
      rw [hco] at hm
      exact (TauCeti.coxeterOrder_le_three_iff hmem).mp hm
    rcases cartan_pair_cases hA hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
    · exfalso; rw [h1, h2] at hprod; norm_num at hprod
    · exfalso; rw [h1, h2] at hprod; norm_num at hprod
    · exfalso; rw [h1, h2] at hprod; norm_num at hprod
    · exfalso; rw [h1, h2] at hprod; norm_num at hprod

private theorem symmetrizer_eq_of_conn {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hA)) (i j : I) :
    symmetrizer hA i = symmetrizer hA j := by
  have hedge : ∀ {a b : I}, (coxeterMatrix hA).M a b = 3 →
      symmetrizer hA a = symmetrizer hA b := by
    intro a b hab
    have hab_ne : a ≠ b := by
      rintro rfl
      rw [CoxeterMatrix.diagonal] at hab
      norm_num at hab
    have hco : (coxeterMatrix hA).M a b = TauCeti.coxeterOrder (A a b * A b a) := by
      simpa only [coxeterMatrix] using
        TauCeti.coxeterMatrixOfCartanMatrix_apply A hA.apply_self
          (fun i j hij => hA.apply_mul_apply_mem_of_ne hij) a b
    have hmem := hA.apply_mul_apply_mem_of_ne hab_ne
    have hle3 : TauCeti.coxeterOrder (A a b * A b a) ≤ 3 := by
      rw [← hco]; omega
    have hprod : A a b * A b a = 1 := by
      rcases (TauCeti.coxeterOrder_le_three_iff hmem).mp hle3 with h0 | h1
      · exfalso
        have h2eq : (coxeterMatrix hA).M a b = 2 := by
          rw [hco, h0, TauCeti.coxeterOrder_zero]
        omega
      · exact h1
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have := hA.apply_le_zero_of_ne hab_ne
      rw [h1] at this
      norm_num at this
    · have hs : symmetrized hA b a = symmetrized hA a b := by
        simpa using (posDef_symmetrized hA).isHermitian.apply a b
      rw [symmetrized_apply hA b a, symmetrized_apply hA a b, h2, h1] at hs
      have : symmetrizer hA b * (-1 : ℚ) = symmetrizer hA a * (-1 : ℚ) := by
        simpa using hs
      have : symmetrizer hA b = symmetrizer hA a := by linarith
      exact this.symm
  have hpath := hconn.2 i j
  induction hpath with
  | refl => rfl
  | tail hbc hstep ih => exact ih.trans (hedge hstep)

private noncomputable def ggQ (A : Matrix I I ℤ) : LinearMap.BilinForm ℤ (I → ℤ) :=
  Matrix.toBilin' A

private theorem ggQ_apply (A : Matrix I I ℤ) (x y : I → ℤ) :
    ggQ A x y = x ⬝ᵥ (A *ᵥ y) :=
  Matrix.toBilin'_apply' A x y

private theorem ggQ_sum (A : Matrix I I ℤ) (x y : I → ℤ) :
    ggQ A x y = ∑ i, ∑ j, x i * A i j * y j :=
  Matrix.toBilin'_apply A x y

private theorem ggQ_comm {A : Matrix I I ℤ} (hA : A.IsSymm) (x y : I → ℤ) :
    ggQ A x y = ggQ A y x := by
  rw [ggQ_apply, ggQ_apply]
  exact hA.dotProduct_mulVec_comm

private theorem ggQ_single_left (A : Matrix I I ℤ) (i : I) (y : I → ℤ) :
    ggQ A (Pi.single i 1) y = coroot A i y := by
  rw [ggQ_apply, single_dotProduct, one_mul, coroot_apply]
  rfl

private theorem ggQ_single_right {A : Matrix I I ℤ} (hA : A.IsSymm) (x : I → ℤ) (i : I) :
    ggQ A x (Pi.single i 1) = coroot A i x := by
  rw [ggQ_comm hA, ggQ_single_left]

private theorem ggQ_single_single {A : Matrix I I ℤ} {i : I} (h2 : A i i = 2) :
    ggQ A (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [ggQ_single_left, coroot_single, h2]

private theorem ggQ_reflection {A : Matrix I I ℤ} (hA : A.IsSymm) {i : I} (h2 : A i i = 2)
    (x y : I → ℤ) :
    ggQ A (reflection A i x) (reflection A i y) = ggQ A x y := by
  have hx : ggQ A x (Pi.single i 1) = coroot A i x := ggQ_single_right hA x i
  have hy : ggQ A (Pi.single i 1) y = coroot A i y := ggQ_single_left A i y
  have hee : ggQ A (Pi.single i 1) (Pi.single i 1) = 2 := ggQ_single_single h2
  rw [reflection_apply_coroot, reflection_apply_coroot]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hx, hy, hee]
  ring

private theorem ggQ_weylAction {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hsymm : A.IsSymm) (w : (coxeterMatrix hA).Group) (x y : I → ℤ) :
    ggQ A (weylAction hA w x) (weylAction hA w y) = ggQ A x y := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple,
      ggQ_reflection hsymm (hA.apply_self i), ih]

private theorem ggQ_cast (A : Matrix I I ℤ) (x y : I → ℤ) :
    ((ggQ A x y : ℤ) : ℚ) = ∑ i, ∑ j, (x i : ℚ) * (A i j : ℚ) * (y j : ℚ) := by
  rw [ggQ_sum]
  push_cast
  ring

private theorem form_eq_ggQ {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsymm : A.IsSymm)
    {d0 : ℚ} (hd : ∀ k, symmetrizer hA k = d0) (x y : I → ℤ) :
    form hA (toRat x) (toRat y) = d0 * (ggQ A x y : ℚ) := by
  have hpoint : ∀ l : I, (toRat y) l * form hA (toRat x) (Pi.single l 1) =
      d0 * ((y l : ℚ) * ∑ k, (A l k : ℚ) * (x k : ℚ)) := by
    intro l
    rw [form_single_right, hd l, toRat_apply]
    simp only [toRat_apply]
    ring
  have hsum : (∑ l : I, (y l : ℚ) * ∑ k : I, (A l k : ℚ) * (x k : ℚ)) =
      ∑ i : I, ∑ j : I, (x i : ℚ) * (A i j : ℚ) * (y j : ℚ) := by
    calc (∑ l : I, (y l : ℚ) * ∑ k : I, (A l k : ℚ) * (x k : ℚ))
        = ∑ l : I, ∑ k : I, (y l : ℚ) * ((A l k : ℚ) * (x k : ℚ)) := by
          apply Finset.sum_congr rfl
          intro l _
          exact Finset.mul_sum Finset.univ (fun k : I => (A l k : ℚ) * (x k : ℚ)) (y l : ℚ)
      _ = ∑ k : I, ∑ l : I, (y l : ℚ) * ((A l k : ℚ) * (x k : ℚ)) := by
          rw [Finset.sum_comm]
      _ = ∑ k : I, ∑ l : I, (x k : ℚ) * (A k l : ℚ) * (y l : ℚ) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [hsymm.apply k l]
          ring
  have hfactor : (∑ l : I, d0 * ((y l : ℚ) * ∑ k : I, (A l k : ℚ) * (x k : ℚ))) =
      d0 * ∑ l : I, ((y l : ℚ) * ∑ k : I, (A l k : ℚ) * (x k : ℚ)) :=
    (Finset.mul_sum Finset.univ
      (fun l : I => (y l : ℚ) * ∑ k : I, (A l k : ℚ) * (x k : ℚ)) d0).symm
  rw [form_eq_sum]
  rw [Finset.sum_congr rfl (fun l _ => hpoint l)]
  rw [hfactor]
  congr 1
  rw [ggQ_cast A x y]
  exact hsum

private theorem ggQ_pos {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsymm : A.IsSymm)
    {d0 : ℚ} (hd : ∀ k, symmetrizer hA k = d0) (hd0 : 0 < d0) (x : I → ℤ) (hx : x ≠ 0) :
    0 < ggQ A x x := by
  have hx' : toRat x ≠ 0 := by
    intro h
    exact hx (toRat_injective (by simpa using h))
  have hf := form_pos hA hx'
  rw [form_eq_ggQ hA hsymm hd x x] at hf
  have hq : (0 : ℚ) < (ggQ A x x : ℚ) := pos_of_mul_pos_right hf hd0.le
  exact_mod_cast hq

private theorem ggQ_nonneg {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hsymm : A.IsSymm)
    {d0 : ℚ} (hd : ∀ k, symmetrizer hA k = d0) (hd0 : 0 < d0) (x : I → ℤ) :
    0 ≤ ggQ A x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ggQ]
  · exact (ggQ_pos hA hsymm hd hd0 x hx).le

private theorem ggQ_self_eq_zero {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hsymm : A.IsSymm) {d0 : ℚ} (hd : ∀ k, symmetrizer hA k = d0) (hd0 : 0 < d0)
    {x : I → ℤ} (h : ggQ A x x = 0) : x = 0 := by
  by_contra hx
  have := ggQ_pos hA hsymm hd hd0 x hx
  omega

private theorem ggQ_self_add {A : Matrix I I ℤ} (hA : A.IsSymm) (x y : I → ℤ) :
    ggQ A (x + y) (x + y) = ggQ A x x + 2 * ggQ A x y + ggQ A y y := by
  simp only [map_add, LinearMap.add_apply]
  rw [ggQ_comm hA y x]
  ring

private theorem ggQ_self_sub {A : Matrix I I ℤ} (hA : A.IsSymm) (x y : I → ℤ) :
    ggQ A (x - y) (x - y) = ggQ A x x - 2 * ggQ A x y + ggQ A y y := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [ggQ_comm hA y x]
  ring

private theorem ggQ_bilin_gen {A : Matrix I I ℤ} (a b : ℤ) (x x' y y' : I → ℤ) :
    ggQ A (a • x - b • y) (a • x' - b • y') =
      (a * a) * ggQ A x x' - (a * b) * ggQ A x y' - (b * a) * ggQ A y x' +
        (b * b) * ggQ A y y' := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

private noncomputable def ggRefl {A : Matrix I I ℤ} (u : I → ℤ) : Module.End ℤ (I → ℤ) :=
  LinearMap.id - (ggQ A u).smulRight u

private theorem ggRefl_apply {A : Matrix I I ℤ} (hA : A.IsSymm) (u v : I → ℤ) :
    ggRefl (A := A) u v = v - ggQ A v u • u := by
  simp only [ggRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  rw [ggQ_comm hA]

private theorem ggRefl_neg {A : Matrix I I ℤ} (hsymm : A.IsSymm) (u : I → ℤ) :
    ggRefl (A := A) (-u) = ggRefl (A := A) u := by
  apply LinearMap.ext
  intro v
  rw [ggRefl_apply hsymm, ggRefl_apply hsymm, map_neg]
  simp only [neg_smul, neg_neg]
  module

private theorem ggRefl_sq {A : Matrix I I ℤ} (hA : A.IsSymm) {u : I → ℤ} (hu : ggQ A u u = 2) :
    ggRefl (A := A) u * ggRefl (A := A) u = 1 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.one_apply, ggRefl_apply hA, ggRefl_apply hA]
  have h1 : ggQ A (v - ggQ A v u • u) u = -ggQ A v u := by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu]
    ring
  rw [h1, neg_smul]
  module

private theorem ggRefl_comm_of_orthogonal {A : Matrix I I ℤ} (hA : A.IsSymm) {u u' : I → ℤ}
    (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2) (hc : ggQ A u u' = 0) :
    ggRefl (A := A) u * ggRefl (A := A) u' = ggRefl (A := A) u' * ggRefl (A := A) u := by
  have hc' : ggQ A u' u = 0 := (ggQ_comm hA u' u).trans hc
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, ggRefl_apply hA, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu, hu', hc, hc']
  module

private theorem ggRefl_braid {A : Matrix I I ℤ} (hA : A.IsSymm) {u u' : I → ℤ}
    (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2) {c : ℤ} (hc : ggQ A u u' = c)
    (hc2 : c * c = 1) :
    ggRefl (A := A) u * ggRefl (A := A) u' * ggRefl (A := A) u =
      ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u' := by
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hc2) with ⟨hc1, -⟩ | ⟨hcn1, -⟩
  · rw [hc1] at hc
    have hc' : ggQ A u' u = 1 := (ggQ_comm hA u' u).trans hc
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, ggRefl_apply hA, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu, hu', hc, hc']
    module
  · rw [hcn1] at hc
    have hc' : ggQ A u' u = -1 := (ggQ_comm hA u' u).trans hc
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, ggRefl_apply hA, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu, hu', hc, hc']
    module

private theorem ggRefl_pow_three_of_sq_one {A : Matrix I I ℤ} (hA : A.IsSymm) {u u' : I → ℤ}
    (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2) {c : ℤ} (hc : ggQ A u u' = c)
    (hc2 : c * c = 1) :
    (ggRefl (A := A) u * ggRefl (A := A) u') ^ 3 = 1 := by
  have hbraid := ggRefl_braid hA hu hu' hc hc2
  have hf := ggRefl_sq hA hu
  have hg := ggRefl_sq hA hu'
  calc (ggRefl (A := A) u * ggRefl (A := A) u') ^ 3
      = (ggRefl (A := A) u * ggRefl (A := A) u' * ggRefl (A := A) u) *
        (ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u') := by
        rw [pow_succ, pow_succ, pow_one]; group
    _ = (ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u') *
        (ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u') := by
        rw [hbraid]
    _ = 1 := by
        rw [show (ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u') *
              (ggRefl (A := A) u' * ggRefl (A := A) u * ggRefl (A := A) u') =
            ggRefl (A := A) u' * ggRefl (A := A) u *
              (ggRefl (A := A) u' * ggRefl (A := A) u') * ggRefl (A := A) u *
              ggRefl (A := A) u' by group, hg]
        rw [show ggRefl (A := A) u' * ggRefl (A := A) u * 1 * ggRefl (A := A) u *
              ggRefl (A := A) u' =
            ggRefl (A := A) u' * (ggRefl (A := A) u * ggRefl (A := A) u) *
              ggRefl (A := A) u' by group, hf]
        rw [show ggRefl (A := A) u' * 1 * ggRefl (A := A) u' =
            ggRefl (A := A) u' * ggRefl (A := A) u' by group, hg]

private theorem ggRefl_pow_three_of_not_commute {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hsymm : A.IsSymm) {d0 : ℚ}
    (hd : ∀ k, symmetrizer hA k = d0) (hd0 : 0 < d0) {u u' : I → ℤ}
    (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2)
    (hnc : ¬ Commute (ggRefl (A := A) u) (ggRefl (A := A) u')) :
    (ggRefl (A := A) u * ggRefl (A := A) u') ^ 3 = 1 := by
  generalize hcdef : ggQ A u u' = c
  have hcsq : c * c ≤ 4 := by
    have hnn := ggQ_nonneg hA hsymm hd hd0 (c • u - 2 • u')
    have hcp : ggQ A u' u = c := (ggQ_comm hsymm u' u).trans hcdef
    have hcalc : ggQ A (c • u - 2 • u') (c • u - 2 • u') = 8 - 2 * (c * c) := by
      rw [← natCast_zsmul u' 2]
      change ggQ A (c • u - (2 : ℤ) • u') (c • u - (2 : ℤ) • u') = 8 - 2 * (c * c)
      rw [ggQ_bilin_gen (A := A) c 2 u u u' u']
      rw [hu, hu', hcdef, hcp]
      ring
    rw [hcalc] at hnn
    omega
  have hlo : -2 ≤ c := by nlinarith [hcsq, sq_nonneg (c + 2)]
  have hhi : c ≤ 2 := by nlinarith [hcsq, sq_nonneg (c - 2)]
  interval_cases c
  ·
    exfalso
    apply hnc
    have hz : u + u' = 0 := by
      apply ggQ_self_eq_zero hA hsymm hd hd0
      rw [ggQ_self_add hsymm, hu, hu', hcdef]
      norm_num
    have huv : u' = -u := by
      rw [add_eq_zero_iff_eq_neg] at hz
      rw [hz]; simp
    rw [huv, ggRefl_neg hsymm]
  ·
    exact ggRefl_pow_three_of_sq_one hsymm hu hu' hcdef (by norm_num)
  ·
    exfalso
    apply hnc
    exact ggRefl_comm_of_orthogonal hsymm hu hu' hcdef
  ·
    exact ggRefl_pow_three_of_sq_one hsymm hu hu' hcdef (by norm_num)
  ·
    exfalso
    apply hnc
    have hz : u - u' = 0 := by
      apply ggQ_self_eq_zero hA hsymm hd hd0
      rw [ggQ_self_sub hsymm, hu, hu', hcdef]
      norm_num
    have huv : u = u' := sub_eq_zero.mp hz
    rw [huv]

private theorem weylAction_conj_eq_ggRefl {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hsymm : A.IsSymm) (w : (coxeterMatrix hA).Group) (i : I) :
    weylAction hA (w * (coxeterMatrix hA).simple i * w⁻¹) =
      ggRefl (A := A) (weylAction hA w (Pi.single i 1)) := by
  apply LinearMap.ext
  intro v
  rw [ggRefl_apply hsymm]
  have hsimple : weylAction hA ((coxeterMatrix hA).simple i) = reflection A i := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using weylAction_simple hA i
  rw [mul_assoc, weylAction_mul_apply, weylAction_mul_apply, hsimple,
    reflection_apply_coroot]
  rw [map_sub, map_smul, weylAction_apply_inv_apply]
  have hc : coroot A i (weylAction hA w⁻¹ v) =
      ggQ A v (weylAction hA w (Pi.single i 1)) := by
    rw [← ggQ_single_left A i (weylAction hA w⁻¹ v)]
    rw [← ggQ_weylAction hA hsymm w (Pi.single i 1) (weylAction hA w⁻¹ v)]
    rw [weylAction_apply_inv_apply, ggQ_comm hsymm]
  rw [hc]

private theorem ggRefl_eq_of_mul_eq_one {A : Matrix I I ℤ} (hsymm : A.IsSymm) {u u' : I → ℤ}
    {c : ℤ} (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2) (hc : ggQ A u u' = c)
    (hc2 : c * c = 1)
    (hcomm : ggRefl (A := A) u * ggRefl (A := A) u' =
      ggRefl (A := A) u' * ggRefl (A := A) u) :
    ggRefl (A := A) u = ggRefl (A := A) u' := by
  have hf := ggRefl_sq hsymm hu
  have hg := ggRefl_sq hsymm hu'
  have h3 := ggRefl_pow_three_of_sq_one hsymm hu hu' hc hc2
  have hsq : (ggRefl (A := A) u * ggRefl (A := A) u') ^ 2 = 1 := by
    rw [pow_two]
    calc (ggRefl (A := A) u * ggRefl (A := A) u') *
          (ggRefl (A := A) u * ggRefl (A := A) u')
        = ggRefl (A := A) u * (ggRefl (A := A) u' * ggRefl (A := A) u) *
            ggRefl (A := A) u' := by group
      _ = ggRefl (A := A) u * (ggRefl (A := A) u * ggRefl (A := A) u') *
            ggRefl (A := A) u' := by rw [← hcomm]
      _ = (ggRefl (A := A) u * ggRefl (A := A) u) *
            (ggRefl (A := A) u' * ggRefl (A := A) u') := by group
      _ = 1 := by rw [hf, hg, mul_one]
  have hfg : ggRefl (A := A) u * ggRefl (A := A) u' = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsq, one_mul] at h3
    exact h3
  calc ggRefl (A := A) u = ggRefl (A := A) u * 1 := (mul_one _).symm
    _ = ggRefl (A := A) u * (ggRefl (A := A) u' * ggRefl (A := A) u') := by rw [← hg]
    _ = (ggRefl (A := A) u * ggRefl (A := A) u') * ggRefl (A := A) u' := by group
    _ = ggRefl (A := A) u' := by rw [hfg, one_mul]

private theorem ggQ_eq_zero_of_commute {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    (hsymm : A.IsSymm) {d0 : ℚ} (hd : ∀ k, symmetrizer hA k = d0) (hd0 : 0 < d0)
    {u u' : I → ℤ} (hu : ggQ A u u = 2) (hu' : ggQ A u' u' = 2)
    (hne : ggRefl (A := A) u ≠ ggRefl (A := A) u')
    (hcomm : ggRefl (A := A) u * ggRefl (A := A) u' =
      ggRefl (A := A) u' * ggRefl (A := A) u) :
    ggQ A u u' = 0 := by
  generalize hcdef : ggQ A u u' = c
  have hcsq : c * c ≤ 4 := by
    have hnn := ggQ_nonneg hA hsymm hd hd0 (c • u - 2 • u')
    have hcp : ggQ A u' u = c := (ggQ_comm hsymm u' u).trans hcdef
    have hcalc : ggQ A (c • u - 2 • u') (c • u - 2 • u') = 8 - 2 * (c * c) := by
      rw [← natCast_zsmul u' 2]
      change ggQ A (c • u - (2 : ℤ) • u') (c • u - (2 : ℤ) • u') = 8 - 2 * (c * c)
      rw [ggQ_bilin_gen (A := A) c 2 u u u' u']
      rw [hu, hu', hcdef, hcp]
      ring
    rw [hcalc] at hnn
    omega
  have hlo : -2 ≤ c := by nlinarith [hcsq, sq_nonneg (c + 2)]
  have hhi : c ≤ 2 := by nlinarith [hcsq, sq_nonneg (c - 2)]
  interval_cases c
  · exfalso; apply hne
    have hz : u + u' = 0 := by
      apply ggQ_self_eq_zero hA hsymm hd hd0
      rw [ggQ_self_add hsymm, hu, hu', hcdef]
      norm_num
    have huv : u' = -u := by
      rw [add_eq_zero_iff_eq_neg] at hz
      rw [hz]; simp
    rw [huv, ggRefl_neg hsymm]
  · exact absurd (ggRefl_eq_of_mul_eq_one hsymm hu hu' hcdef (by norm_num) hcomm) hne
  · rfl
  · exact absurd (ggRefl_eq_of_mul_eq_one hsymm hu hu' hcdef (by norm_num) hcomm) hne
  · exfalso; apply hne
    have hz : u - u' = 0 := by
      apply ggQ_self_eq_zero hA hsymm hd hd0
      rw [ggQ_self_sub hsymm, hu, hu', hcdef]
      norm_num
    have huv : u = u' := sub_eq_zero.mp hz
    rw [huv]

private theorem ggQ_nsmul_left {A : Matrix I I ℤ} (n : ℕ) (x y : I → ℤ) :
    ggQ A (n • x) y = (n : ℤ) * ggQ A x y := by
  rw [← natCast_zsmul x n, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem ggQ_nsmul_right {A : Matrix I I ℤ} (n : ℕ) (x y : I → ℤ) :
    ggQ A x (n • y) = (n : ℤ) * ggQ A x y := by
  rw [← natCast_zsmul y n, map_smul, smul_eq_mul]

private theorem ggQ_nat_add_norm {A : Matrix I I ℤ} (hsymm : A.IsSymm) (a b : ℕ)
    (x y : I → ℤ) :
    ggQ A (a • x + b • y) (a • x + b • y) =
      (a : ℤ) * (a : ℤ) * ggQ A x x + 2 * (a : ℤ) * (b : ℤ) * ggQ A x y +
        (b : ℤ) * (b : ℤ) * ggQ A y y := by
  simp only [map_add, LinearMap.add_apply, ggQ_nsmul_left, ggQ_nsmul_right]
  rw [ggQ_comm hsymm y x]
  ring

private theorem linIndepPair_of_orthogonal {A : Matrix I I ℤ} (hsymm : A.IsSymm)
    {x y : I → ℤ} (hx : ggQ A x x = 2) (hy : ggQ A y y = 2) (hxy : ggQ A x y = 0) :
    LinIndepPair x y := by
  intro a b hab
  have hyne : y ≠ 0 := by
    rintro rfl
    simp [ggQ] at hy
  have hxa : ggQ A (a • x + b • y) x = 0 := by rw [hab]; simp [ggQ]
  have hval : ggQ A (a • x + b • y) x = a * ggQ A x x + b * ggQ A y x := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hval, hx, ggQ_comm hsymm, hxy] at hxa
  have ha : a = 0 := by omega
  have hb : b = 0 := by
    have h0 : b • y = 0 := by simpa [ha] using hab
    exact (smul_eq_zero.mp h0).resolve_right hyne
  exact ⟨ha, hb⟩

private theorem ggQ_norm_mem_roots {K : Type*} [Group K] (D : UniversalRootDatum K)
    (hconn : GGSimplyLacedConnected (coxeterMatrix D.isFiniteType))
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ggQ D.cartan γ γ = 2 ∨ ggQ D.cartan γ γ = 8 := by
  have hsymm : D.cartan.IsSymm := cartan_symm_of_conn D.isFiniteType hconn
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, _, rfl⟩
  · left
    rw [ggQ_weylAction D.isFiniteType hsymm, ggQ_single_single (D.isFiniteType.apply_self i)]
  · right
    rw [ggQ_nsmul_left, ggQ_nsmul_right, ggQ_weylAction D.isFiniteType hsymm,
      ggQ_single_single (D.isFiniteType.apply_self i)]
    norm_num

private theorem openCone_empty_of_orthogonal {K : Type*} [Group K] (D : UniversalRootDatum K)
    (hconn : GGSimplyLacedConnected (coxeterMatrix D.isFiniteType)) {x y : Fin D.rank → ℤ}
    (hx : ggQ D.cartan x x = 2) (hy : ggQ D.cartan y y = 2) (hxy : ggQ D.cartan x y = 0) :
    openCone D.roots x y = ∅ := by
  have hsymm : D.cartan.IsSymm := cartan_symm_of_conn D.isFiniteType hconn
  ext ε
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hεroot, a, b, ha, hb, rfl⟩
  have hnorm := ggQ_norm_mem_roots D hconn hεroot
  have hcalc : ggQ D.cartan (a • x + b • y) (a • x + b • y) =
      2 * ((a : ℤ) * (a : ℤ)) + 2 * ((b : ℤ) * (b : ℤ)) := by
    rw [ggQ_nat_add_norm hsymm a b x y, hx, hy, hxy]
    ring
  rw [hcalc] at hnorm
  have ha' : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have ha2 : a ≤ 2 := by
    have h : (a : ℤ) ≤ 2 := by
      rcases hnorm with h2 | h8
      · nlinarith [h2, ha', hb', sq_nonneg ((a : ℤ) - 2), sq_nonneg ((b : ℤ) - 1)]
      · nlinarith [h8, ha', hb', sq_nonneg ((a : ℤ) - 2), sq_nonneg ((b : ℤ) - 1)]
    exact_mod_cast h
  have hb2 : b ≤ 2 := by
    have h : (b : ℤ) ≤ 2 := by
      rcases hnorm with h2 | h8
      · nlinarith [h2, ha', hb', sq_nonneg ((b : ℤ) - 2), sq_nonneg ((a : ℤ) - 1)]
      · nlinarith [h8, ha', hb', sq_nonneg ((b : ℤ) - 2), sq_nonneg ((a : ℤ) - 1)]
    exact_mod_cast h
  rcases hnorm with h2 | h8
  · interval_cases a <;> interval_cases b <;> norm_num at h2
  · interval_cases a <;> interval_cases b <;> norm_num at h8

private theorem rootGroup_commute_of_orthogonal {K : Type*} [Group K] (D : UniversalRootDatum K)
    (hconn : GGSimplyLacedConnected (coxeterMatrix D.isFiniteType))
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H)
    {x y : Fin D.rank → ℤ} (hx : ggQ D.cartan x x = 2) (hy : ggQ D.cartan y y = 2)
    (hxy : ggQ D.cartan x y = 0) (hxroot : x ∈ D.roots) (hyroot : y ∈ D.roots) :
    ∀ a ∈ D.rootGroup x, ∀ b ∈ D.rootGroup y, a * b = b * a := by
  have hsymm : D.cartan.IsSymm := cartan_symm_of_conn D.isFiniteType hconn
  have hlin : LinIndepPair x y := linIndepPair_of_orthogonal hsymm hx hy hxy
  have hcone : openCone D.roots x y = ∅ := openCone_empty_of_orthogonal D hconn hx hy hxy
  intro a ha b hb
  have hmem := hext.commutator_mem x hxroot y hyroot hlin a ha b hb
  have hbot : ⁅a, b⁆ = 1 := by simpa [hcone] using hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hbot

end FormAux

section RootPairs

theorem ggWeyl_refl_order3 {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hconn : GGSimplyLacedConnected (coxeterMatrix hA))
    (w w' : (coxeterMatrix hA).Group) (i j : I)
    (hncomm : ¬ Commute (w * (coxeterMatrix hA).simple i * w⁻¹)
      (w' * (coxeterMatrix hA).simple j * w'⁻¹)) :
    ((w * (coxeterMatrix hA).simple i * w⁻¹) * (w' * (coxeterMatrix hA).simple j * w'⁻¹)) ^ 3 =
      1 := by
  classical
  have hsymm : A.IsSymm := cartan_symm_of_conn hA hconn
  set d0 : ℚ := symmetrizer hA i with hd0def
  have hd : ∀ k, symmetrizer hA k = d0 := fun k => symmetrizer_eq_of_conn hA hconn k i
  have hd0 : 0 < d0 := by rw [hd0def]; exact symmetrizer_pos hA i
  have hu : ggQ A (weylAction hA w (Pi.single i 1)) (weylAction hA w (Pi.single i 1)) = 2 := by
    rw [ggQ_weylAction hA hsymm, ggQ_single_single (hA.apply_self i)]
  have hu' : ggQ A (weylAction hA w' (Pi.single j 1)) (weylAction hA w' (Pi.single j 1)) = 2 := by
    rw [ggQ_weylAction hA hsymm, ggQ_single_single (hA.apply_self j)]
  have h1 : weylAction hA (w * (coxeterMatrix hA).simple i * w⁻¹) =
      ggRefl (A := A) (weylAction hA w (Pi.single i 1)) :=
    weylAction_conj_eq_ggRefl hA hsymm w i
  have h2 : weylAction hA (w' * (coxeterMatrix hA).simple j * w'⁻¹) =
      ggRefl (A := A) (weylAction hA w' (Pi.single j 1)) :=
    weylAction_conj_eq_ggRefl hA hsymm w' j
  have hnc : ¬ Commute (ggRefl (A := A) (weylAction hA w (Pi.single i 1)))
      (ggRefl (A := A) (weylAction hA w' (Pi.single j 1))) := by
    intro hc
    apply hncomm
    apply weylAction_injective hA
    conv_lhs => rw [map_mul]
    conv_rhs => rw [map_mul]
    rw [h1, h2]
    exact hc
  have h3 := ggRefl_pow_three_of_not_commute hA hsymm hd hd0 hu hu' hnc
  apply weylAction_injective hA
  rw [map_pow, map_one]
  conv_lhs => rw [map_mul]
  rw [h1, h2, h3]

end RootPairs

section TagLevi

theorem ggTag_levi_comm {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n)
    (w w' : (coxeterMatrix (ggU t n f).D.isFiniteType).Group) (i j : Fin (ggU t n f).D.rank)
    (hne : w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹ ≠
      w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹)
    (hcomm : Commute (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)
      (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹)) :
    ∀ a ∈ ggRootLevi (ggU t n f).D (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)),
    ∀ b ∈ ggRootLevi (ggU t n f).D (weylAction (ggU t n f).D.isFiniteType w' (Pi.single j 1)),
      a * b = b * a := by
  classical
  have hweyl := ggTag_weylMatrix ht hadm
  have hconn : GGSimplyLacedConnected (coxeterMatrix (ggU t n f).D.isFiniteType) :=
    ggSimplyLacedConnected_of_weyl hweyl.1 hweyl.2
  have hsymm : (ggU t n f).D.cartan.IsSymm :=
    cartan_symm_of_conn (ggU t n f).D.isFiniteType hconn
  set u : Fin (ggU t n f).D.rank → ℤ :=
    weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1) with hu_def
  set u' : Fin (ggU t n f).D.rank → ℤ :=
    weylAction (ggU t n f).D.isFiniteType w' (Pi.single j 1) with hu'_def
  have hu : ggQ (ggU t n f).D.cartan u u = 2 := by
    rw [hu_def, ggQ_weylAction (ggU t n f).D.isFiniteType hsymm,
      ggQ_single_single ((ggU t n f).D.isFiniteType.apply_self i)]
  have hu' : ggQ (ggU t n f).D.cartan u' u' = 2 := by
    rw [hu'_def, ggQ_weylAction (ggU t n f).D.isFiniteType hsymm,
      ggQ_single_single ((ggU t n f).D.isFiniteType.apply_self j)]
  set d0 : ℚ := symmetrizer (ggU t n f).D.isFiniteType i with hd0def
  have hd : ∀ k, symmetrizer (ggU t n f).D.isFiniteType k = d0 :=
    fun k => symmetrizer_eq_of_conn (ggU t n f).D.isFiniteType hconn k i
  have hd0 : 0 < d0 := by
    rw [hd0def]; exact symmetrizer_pos (ggU t n f).D.isFiniteType i
  have h1 : weylAction (ggU t n f).D.isFiniteType
      (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) =
      ggRefl (A := (ggU t n f).D.cartan) u := by
    simpa only [hu_def] using
      weylAction_conj_eq_ggRefl (ggU t n f).D.isFiniteType hsymm w i
  have h2 : weylAction (ggU t n f).D.isFiniteType
      (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹) =
      ggRefl (A := (ggU t n f).D.cartan) u' := by
    simpa only [hu'_def] using
      weylAction_conj_eq_ggRefl (ggU t n f).D.isFiniteType hsymm w' j
  have hnl : ggRefl (A := (ggU t n f).D.cartan) u ≠
      ggRefl (A := (ggU t n f).D.cartan) u' := by
    intro heq
    apply hne
    apply weylAction_injective (ggU t n f).D.isFiniteType
    rw [h1, h2, heq]
  have hcomml : ggRefl (A := (ggU t n f).D.cartan) u *
      ggRefl (A := (ggU t n f).D.cartan) u' =
      ggRefl (A := (ggU t n f).D.cartan) u' *
      ggRefl (A := (ggU t n f).D.cartan) u := by
    have hc0 : w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹ *
        (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹) =
        (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹) *
        (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) := hcomm
    have hc := congrArg (weylAction (ggU t n f).D.isFiniteType) hc0
    conv_lhs at hc => rw [map_mul]
    conv_rhs at hc => rw [map_mul]
    rw [h1, h2] at hc
    exact hc
  have hc : ggQ (ggU t n f).D.cartan u u' = 0 :=
    ggQ_eq_zero_of_commute (ggU t n f).D.isFiniteType hsymm hd hd0 hu hu' hnl hcomml
  have hstein : ∃ (n' : Fin (ggU t n f).D.rank → (ggU t n f).K)
      (H' : Fin (ggU t n f).D.rank → Subgroup (ggU t n f).K),
      SteinbergExtras (ggU t n f).D n' H' := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at h3; omega⟩
      exact ⟨SpecialLinear.weylRep m (GaloisField 2 f),
        SpecialLinear.torus m (GaloisField 2 f),
        SpecialLinear.steinbergExtras m (GaloisField 2 f)⟩
    · have hn : 3 ≤ n := by simpa only [bnRank] using h3
      have hU : ggU .POmegaPlus n f =
          ⟨spinGroup (quadPlus n (GaloisField 2 f)), plusDatum n (GaloisField 2 f) hn⟩ := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [hU]
      exact ⟨weylD (GaloisField 2 f) hn, fun k => (torusD (GaloisField 2 f) hn k).range,
        plusDatum_steinbergExtras hn⟩
    · exact ⟨e6Data_valid.nm (GaloisField 2 f), e6Data_valid.torus (GaloisField 2 f),
        e6Datum_steinbergExtras (k := GaloisField 2 f)⟩
    · exact ⟨e7Data_valid.nm (GaloisField 2 f), e7Data_valid.torus (GaloisField 2 f),
        e7Datum_steinbergExtras (k := GaloisField 2 f)⟩
    · exact ⟨CFSG.LieType.Chevalley.weylElement .E8 (GaloisField 2 f),
        CFSG.LieType.Steinberg.Adjoint.torus (τ := .E8) (GaloisField 2 f),
        CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras (K := GaloisField 2 f)⟩
  obtain ⟨n', H', hext⟩ := hstein
  have hu_root : u ∈ (ggU t n f).D.roots := by rw [hu_def]; exact Or.inl ⟨w, i, rfl⟩
  have hu'_root : u' ∈ (ggU t n f).D.roots := by rw [hu'_def]; exact Or.inl ⟨w', j, rfl⟩
  have hnu_root : -u ∈ (ggU t n f).D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (ggU t n f).D.isFiniteType hu_root
  have hnu'_root : -u' ∈ (ggU t n f).D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (ggU t n f).D.isFiniteType hu'_root
  have hnu : ggQ (ggU t n f).D.cartan (-u) (-u) = 2 := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hu
  have hnu' : ggQ (ggU t n f).D.cartan (-u') (-u') = 2 := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hu'
  have hcnu' : ggQ (ggU t n f).D.cartan (-u) u' = 0 := by
    simp only [map_neg, LinearMap.neg_apply, hc, neg_zero]
  have hcun' : ggQ (ggU t n f).D.cartan u (-u') = 0 := by
    simp only [map_neg, hc, neg_zero]
  have hcnun' : ggQ (ggU t n f).D.cartan (-u) (-u') = 0 := by
    simp only [map_neg, LinearMap.neg_apply, hc, neg_zero]
  have hcomm_uu' := rootGroup_commute_of_orthogonal (ggU t n f).D hconn hext
    hu hu' hc hu_root hu'_root
  have hcomm_nu' := rootGroup_commute_of_orthogonal (ggU t n f).D hconn hext
    hnu hu' hcnu' hnu_root hu'_root
  have hcomm_un' := rootGroup_commute_of_orthogonal (ggU t n f).D hconn hext
    hu hnu' hcun' hu_root hnu'_root
  have hcomm_nun' := rootGroup_commute_of_orthogonal (ggU t n f).D hconn hext
    hnu hnu' hcnun' hnu_root hnu'_root
  have mk_le : ∀ {x y : Fin (ggU t n f).D.rank → ℤ},
      (∀ a ∈ (ggU t n f).D.rootGroup x, ∀ b ∈ (ggU t n f).D.rootGroup y, a * b = b * a) →
      (ggU t n f).D.rootGroup x ≤
        Subgroup.centralizer ((ggU t n f).D.rootGroup y : Set (ggU t n f).K) := by
    intro x y hxy a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hxy a ha b hb).symm
  have le_uu' := mk_le hcomm_uu'
  have le_nu' := mk_le hcomm_nu'
  have le_un' := mk_le hcomm_un'
  have le_nn' := mk_le hcomm_nun'
  have hL : ggRootLevi (ggU t n f).D u ≤
      Subgroup.centralizer (ggRootLevi (ggU t n f).D u' : Set (ggU t n f).K) := by
    rw [ggRootLevi, ggRootLevi]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]; exact le_uu'
      · rw [Subgroup.le_centralizer_iff]; exact le_un'
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]; exact le_nu'
      · rw [Subgroup.le_centralizer_iff]; exact le_nn'
  intro a ha b hb
  have hmem : a ∈ Subgroup.centralizer (ggRootLevi (ggU t n f).D u' : Set (ggU t n f).K) :=
    hL ha
  exact ((Subgroup.mem_centralizer_iff.mp hmem) b hb).symm

end TagLevi

end CFSG.StandardType
