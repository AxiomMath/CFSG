module

public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.KernelDirect.C5101

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_Lg : Fintype.card Lg = 1440 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_filter_BL : (Finset.univ.filter fun l : Lg => l ∈ BL).card = 144 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem repPt_spec : ∀ x : Lg,
    (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * x ∈ BL).card = 1 := by
  decide +kernel

@[expose] def mat4 {F : Type} : F × F × F × F ≃ Matrix (Fin 2) (Fin 2) F where
  toFun p := !![p.1, p.2.1; p.2.2.1, p.2.2.2]
  invFun A := (A 0 0, A 0 1, A 1 0, A 1 1)
  left_inv _ := rfl
  right_inv A := (Matrix.eta_fin_two A).symm

theorem sum_SL2 {F : Type} [CommRing F] [Fintype F] [DecidableEq F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F → ℤ) :
    ∑ M : Matrix.SpecialLinearGroup (Fin 2) F, g M =
      ∑ a : F, ∑ b : F, ∑ c : F, ∑ d : F,
        if h : a * d - b * c = 1 then g ⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩
        else 0 := by
  let f : Matrix (Fin 2) (Fin 2) F → ℤ := fun A => if h : A.det = 1 then g ⟨A, h⟩ else 0
  have h1 : ∑ M : Matrix.SpecialLinearGroup (Fin 2) F, g M =
      ∑ M : Matrix.SpecialLinearGroup (Fin 2) F, f M.1 :=
    Finset.sum_congr rfl fun M _ => by simp only [f, dif_pos M.2]; rfl
  have h2 : ∑ M : Matrix.SpecialLinearGroup (Fin 2) F, f M.1 =
      ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) F => A.det = 1), f A :=
    (Finset.sum_subtype _ (fun A => by simp) f).symm
  have h3 : ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) F => A.det = 1), f A =
      ∑ A, f A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : A.det = 1
    · rw [if_pos h]
    · rw [if_neg h]; simp only [f, dif_neg h]
  have h4 : ∑ A, f A = ∑ p : F × F × F × F, f (mat4 p) :=
    (Fintype.sum_equiv mat4 (fun p => f (mat4 p)) f (fun _ => rfl)).symm
  rw [h1, h2, h3, h4, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  show (if h : (!![a, b; c, d]).det = 1 then g ⟨!![a, b; c, d], h⟩ else 0) = _
  by_cases h : a * d - b * c = 1
  · rw [dif_pos h, dif_pos ((Matrix.det_fin_two_of a b c d).trans h)]
  · rw [dif_neg h, dif_neg (fun h' => h ((Matrix.det_fin_two_of a b c d).symm.trans h'))]

theorem sum_Lg (f : Lg → ℤ) :
    ∑ l : Lg, f l = ∑ M : SL2, f ⟨M, 1⟩ + ∑ M : SL2, f ⟨M, Multiplicative.ofAdd 1⟩ := by
  rw [Fintype.sum_equiv SemidirectProduct.equivProd f
    (fun p => f (SemidirectProduct.equivProd.symm p)) (fun _ => rfl), Fintype.sum_prod_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun M _ => ?_
  have hu : (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, Multiplicative.ofAdd 1} := by
    decide
  rw [hu, Finset.sum_pair (by decide)]
  rfl

@[expose] def sumP (a : F9) (ε : Multiplicative (ZMod 2)) : ℤ :=
  ∑ b : F9, ∑ c : F9, ∑ d : F9,
    if h : a * d - b * c = 1 then
      aTabFast ⟨⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩, ε⟩ ^ 2
    else 0

@[expose] def vals_one (a : F9) : ℤ := [56, 65, 65, 137, 65, 65, 137, 65, 65].getD (3 * a.re.val + a.im.val) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_00_one : sumP ⟨0, 0⟩ (1) = vals_one ⟨0, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_01_one : sumP ⟨0, 1⟩ (1) = vals_one ⟨0, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_02_one : sumP ⟨0, 2⟩ (1) = vals_one ⟨0, 2⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_10_one : sumP ⟨1, 0⟩ (1) = vals_one ⟨1, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_11_one : sumP ⟨1, 1⟩ (1) = vals_one ⟨1, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_12_one : sumP ⟨1, 2⟩ (1) = vals_one ⟨1, 2⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_20_one : sumP ⟨2, 0⟩ (1) = vals_one ⟨2, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_21_one : sumP ⟨2, 1⟩ (1) = vals_one ⟨2, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_22_one : sumP ⟨2, 2⟩ (1) = vals_one ⟨2, 2⟩ := by decide +kernel

theorem sumP_one (a : F9) : sumP a (1) = vals_one a := by
  rcases a with ⟨r, i⟩
  fin_cases r <;> fin_cases i
  exacts [sumP_00_one, sumP_01_one, sumP_02_one, sumP_10_one, sumP_11_one, sumP_12_one, sumP_20_one, sumP_21_one, sumP_22_one]

@[expose] def vals_neg (a : F9) : ℤ := [72, 81, 81, 81, 81, 81, 81, 81, 81].getD (3 * a.re.val + a.im.val) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_00_neg : sumP ⟨0, 0⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨0, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_01_neg : sumP ⟨0, 1⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨0, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_02_neg : sumP ⟨0, 2⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨0, 2⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_10_neg : sumP ⟨1, 0⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨1, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_11_neg : sumP ⟨1, 1⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨1, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_12_neg : sumP ⟨1, 2⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨1, 2⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_20_neg : sumP ⟨2, 0⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨2, 0⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_21_neg : sumP ⟨2, 1⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨2, 1⟩ := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sumP_22_neg : sumP ⟨2, 2⟩ (Multiplicative.ofAdd 1) = vals_neg ⟨2, 2⟩ := by decide +kernel

theorem sumP_neg (a : F9) : sumP a (Multiplicative.ofAdd 1) = vals_neg a := by
  rcases a with ⟨r, i⟩
  fin_cases r <;> fin_cases i
  exacts [sumP_00_neg, sumP_01_neg, sumP_02_neg, sumP_10_neg, sumP_11_neg, sumP_12_neg, sumP_20_neg, sumP_21_neg, sumP_22_neg]

set_option maxRecDepth 100000 in
theorem vals_sum : ∑ a : F9, vals_one a + ∑ a : F9, vals_neg a = 1440 := by decide +kernel

theorem sum_sq_aTabFast : ∑ l : Lg, aTabFast l ^ 2 = 1440 := by
  calc ∑ l : Lg, aTabFast l ^ 2 = ∑ a : F9, sumP a 1 + ∑ a : F9, sumP a (Multiplicative.ofAdd 1) := by
        rw [sum_Lg, sum_SL2, sum_SL2]
        rfl
    _ = ∑ a : F9, vals_one a + ∑ a : F9, vals_neg a := by
        rw [Finset.sum_congr rfl (fun a _ => sumP_one a), Finset.sum_congr rfl (fun a _ => sumP_neg a)]
    _ = 1440 := vals_sum


end CertificateChecks.KernelDirect.C5101
