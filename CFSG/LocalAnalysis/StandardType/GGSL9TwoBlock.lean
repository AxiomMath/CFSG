module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

private theorem ggSL9_exp_neg_mul_eq (e : ZMod 3) :
    2 ^ e.val * 2 ^ (-e).val = 1 ∨ 2 ^ e.val * 2 ^ (-e).val = 8 := by
  fin_cases e <;> decide

private theorem ggSL9_pow_exp_mul (x : GaloisField 2 3) (e : ZMod 3) :
    (x ^ 2 ^ e.val) ^ 2 ^ (-e).val = x := by
  rw [← pow_mul]
  rcases ggSL9_exp_neg_mul_eq e with h | h
  · rw [h, pow_one]
  · rw [h, ggSL9_pow_eight]

private theorem ggSL9_exp_neg_mul_eq' (e : ZMod 3) :
    2 ^ (-e).val * 2 ^ e.val = 1 ∨ 2 ^ (-e).val * 2 ^ e.val = 8 := by
  fin_cases e <;> decide

private theorem ggSL9_pow_exp_mul' (x : GaloisField 2 3) (e : ZMod 3) :
    (x ^ 2 ^ (-e).val) ^ 2 ^ e.val = x := by
  rw [← pow_mul]
  rcases ggSL9_exp_neg_mul_eq' e with h | h
  · rw [h, pow_one]
  · rw [h, ggSL9_pow_eight]

private theorem ggSL9_add_self_cancel (x y : GaloisField 2 3) : x + (y + x) = y := by
  rw [add_comm y x, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem ggSL9_zmod_two_pow_val (e : ZMod 3) :
    ((2 : ZMod 7) ^ e.val).val = 2 ^ e.val := by
  fin_cases e <;> decide

private theorem ggSL9_zmod_two_pow_val_neg (e : ZMod 3) :
    ((2 : ZMod 7) ^ (-e).val).val = 2 ^ (-e).val := by
  fin_cases e <;> decide

private theorem ggSL9Zeta_pow_eq_mod (m : ℕ) :
    ggSL9Zeta ^ m = ggSL9Zeta ^ (m % 7) := by
  conv_lhs => rw [← pow_mod_orderOf]
  rw [orderOf_ggSL9Zeta]

private theorem ggSL9Zeta_pow_val_mul_neg (e : ZMod 3) (x : ZMod 7) :
    ggSL9Zeta ^ (((2 : ZMod 7) ^ (-e).val) * x).val =
      (ggSL9Zeta ^ x.val) ^ 2 ^ (-e).val := by
  rw [← pow_mul, ZMod.val_mul, ggSL9_zmod_two_pow_val_neg]
  conv_rhs => rw [ggSL9Zeta_pow_eq_mod]
  congr 1
  exact congrArg (fun n : ℕ => n % 7) (Nat.mul_comm _ _)

private theorem ggSL9Zeta_pow_val_mul_pos (e : ZMod 3) (x : ZMod 7) :
    ggSL9Zeta ^ (((2 : ZMod 7) ^ e.val) * x).val =
      (ggSL9Zeta ^ x.val) ^ 2 ^ e.val := by
  rw [← pow_mul, ZMod.val_mul, ggSL9_zmod_two_pow_val]
  conv_rhs => rw [ggSL9Zeta_pow_eq_mod]
  congr 1
  exact congrArg (fun n : ℕ => n % 7) (Nat.mul_comm _ _)

private theorem ggSL9Zeta_field_pow_val_mul_neg (e : ZMod 3) (x : ZMod 7) :
    ((ggSL9Zeta ^ (((2 : ZMod 7) ^ (-e).val) * x).val : (GaloisField 2 3)ˣ) :
        GaloisField 2 3) =
      (((ggSL9Zeta ^ x.val : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ 2 ^ (-e).val := by
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg (fun u : (GaloisField 2 3)ˣ => (u : GaloisField 2 3))
    (ggSL9Zeta_pow_val_mul_neg e x)

private theorem ggSL9Zeta_field_pow_val_mul_pos (e : ZMod 3) (x : ZMod 7) :
    ((ggSL9Zeta ^ (((2 : ZMod 7) ^ e.val) * x).val : (GaloisField 2 3)ˣ) :
        GaloisField 2 3) =
      (((ggSL9Zeta ^ x.val : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ 2 ^ e.val := by
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg (fun u : (GaloisField 2 3)ˣ => (u : GaloisField 2 3))
    (ggSL9Zeta_pow_val_mul_pos e x)

private theorem ggSL9TorusCoord_apply' (f : Multiplicative (Fin 3 → ZMod 7)) (v : GGSL9V)
    (i : Fin 3) : ggSL9TorusCoord f v i = ((ggSL9Zeta ^ (toAdd f i).val :
      (GaloisField 2 3)ˣ) : GaloisField 2 3) * v i := by
  conv_lhs => rw [show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm]
  rw [ggSL9TorusCoord_apply]

private theorem ggSL9Fun_apply_j {i j : Fin 3} (hij : i ≠ j) (n : ℕ) (μ : GaloisField 2 3)
    (v : GGSL9V) : ggSL9Fun i j n μ v j = v j + μ * v i ^ 2 ^ n := by
  simp only [ggSL9Fun, Pi.add_apply, Pi.single_eq_same]

private theorem ggSL9Fun_apply_of_ne {i j : Fin 3} (n : ℕ) (μ : GaloisField 2 3) (v : GGSL9V)
    {l : Fin 3} (hlj : l ≠ j) : ggSL9Fun i j n μ v l = v l := by
  simp only [ggSL9Fun, Pi.add_apply, Pi.single_eq_of_ne hlj, add_zero]

@[expose] noncomputable def ggSL9W (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  ggSL9Root i j hij e.val 1 * ggSL9Root j i hij.symm (-e).val 1 * ggSL9Root i j hij e.val 1

theorem ggSL9W_mem_J {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    ggSL9W i j hij e ∈ ggSL9J i j e := by
  unfold ggSL9W ggSL9J
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure (Or.inl ⟨hij, 1, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨hij.symm, 1, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨hij, 1, rfl⟩)

theorem ggSL9W_apply {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) (v : GGSL9V) (l : Fin 3) :
    ggSL9W i j hij e v l =
      if l = i then v j ^ 2 ^ (-e).val else if l = j then v i ^ 2 ^ e.val else v l := by
  rw [ggSL9W, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggSL9Root_apply, ggSL9Root_apply, ggSL9Root_apply]
  by_cases hli : l = i
  · rw [hli]
    rw [ggSL9Fun_apply_of_ne e.val 1 _ hij,
      ggSL9Fun_apply_j hij.symm (-e).val 1 _,
      ggSL9Fun_apply_of_ne e.val 1 _ hij,
      ggSL9Fun_apply_j hij e.val 1 _,
      if_pos rfl, one_mul, add_pow_char_pow, one_mul, ggSL9_pow_exp_mul]
    exact ggSL9_add_self_cancel (v i) (v j ^ 2 ^ (-e).val)
  · rw [if_neg hli]
    by_cases hlj : l = j
    · rw [hlj]
      have houter : (v i + (v j + v i ^ 2 ^ e.val) ^ 2 ^ (-e).val) ^ 2 ^ e.val =
          v i ^ 2 ^ e.val + ((v j + v i ^ 2 ^ e.val) ^ 2 ^ (-e).val) ^ 2 ^ e.val := by
        rw [add_pow_char_pow]
      rw [ggSL9Fun_apply_j hij e.val 1 _,
        ggSL9Fun_apply_of_ne (-e).val 1 _ hij.symm,
        ggSL9Fun_apply_j hij.symm (-e).val 1 _,
        ggSL9Fun_apply_of_ne e.val 1 _ hij,
        ggSL9Fun_apply_j hij e.val 1 _,
        if_pos rfl]
      simp only [one_mul]
      rw [houter, ggSL9_pow_exp_mul']
      exact ggSL9_add_self_cancel (v j + v i ^ 2 ^ e.val) (v i ^ 2 ^ e.val)
    · rw [ggSL9Fun_apply_of_ne e.val 1 _ hlj,
        ggSL9Fun_apply_of_ne (-e).val 1 _ hli,
        ggSL9Fun_apply_of_ne e.val 1 _ hlj,
        if_neg hlj]

theorem ggSL9W_mul_self {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    ggSL9W i j hij e * ggSL9W i j hij e = 1 := by
  apply LinearEquiv.ext
  intro v
  funext l
  rw [LinearEquiv.mul_apply]
  simp only [ggSL9W_apply]
  by_cases hli : l = i
  · rw [if_pos hli]
    rw [if_neg (Ne.symm hij)]
    rw [if_pos trivial]
    rw [hli]
    exact ggSL9_pow_exp_mul _ e
  · rw [if_neg hli]
    by_cases hlj : l = j
    · rw [if_pos hlj]
      rw [if_pos trivial]
      rw [hlj]
      exact ggSL9_pow_exp_mul' _ e
    · rw [if_neg hlj]
      rw [if_neg hli, if_neg hlj]
      rfl

@[expose] def ggSL9WCoordFun (i j : Fin 3) (e : ZMod 3) (f : Fin 3 → ZMod 7) : Fin 3 → ZMod 7 :=
  fun l => if l = i then 2 ^ (-e).val * f j else if l = j then 2 ^ e.val * f i else f l

private theorem ggSL9_two_pow_neg_mul (e : ZMod 3) :
    (2 : ZMod 7) ^ (-e).val * 2 ^ e.val = 1 := by
  fin_cases e <;> decide

theorem ggSL9WCoordFun_invol {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) (f : Fin 3 → ZMod 7) :
    ggSL9WCoordFun i j e (ggSL9WCoordFun i j e f) = f := by
  have h1 := ggSL9_two_pow_neg_mul e
  have h2 : (2 : ZMod 7) ^ e.val * 2 ^ (-e).val = 1 := by rw [mul_comm]; exact h1
  have hi : ∀ g : Fin 3 → ZMod 7, ggSL9WCoordFun i j e g i = 2 ^ (-e).val * g j :=
    fun g => if_pos (rfl : i = i)
  have hj : ∀ g : Fin 3 → ZMod 7, ggSL9WCoordFun i j e g j = 2 ^ e.val * g i :=
    fun g => (if_neg hij.symm).trans (if_pos (rfl : j = j))
  have hl : ∀ (g : Fin 3 → ZMod 7) (l : Fin 3), l ≠ i → l ≠ j → ggSL9WCoordFun i j e g l = g l :=
    fun g l hli hlj => (if_neg hli).trans (if_neg hlj)
  funext l
  by_cases hli : l = i
  · rw [hli, hi, hj, ← mul_assoc, h1, one_mul]
  · by_cases hlj : l = j
    · rw [hlj, hj, hi, ← mul_assoc, h2, one_mul]
    · rw [hl _ l hli hlj]
      exact hl f l hli hlj

private theorem ggSL9WCoordFun_apply_i {i j : Fin 3} (e : ZMod 3) (f : Fin 3 → ZMod 7) :
    ggSL9WCoordFun i j e f i = 2 ^ (-e).val * f j := by
  unfold ggSL9WCoordFun
  rw [if_pos rfl]

private theorem ggSL9WCoordFun_apply_j {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (f : Fin 3 → ZMod 7) : ggSL9WCoordFun i j e f j = 2 ^ e.val * f i := by
  unfold ggSL9WCoordFun
  rw [if_neg hij.symm, if_pos rfl]

private theorem ggSL9WCoordFun_apply_of_ne {i j : Fin 3} (e : ZMod 3) (f : Fin 3 → ZMod 7)
    {l : Fin 3} (hli : l ≠ i) (hlj : l ≠ j) : ggSL9WCoordFun i j e f l = f l := by
  unfold ggSL9WCoordFun
  rw [if_neg hli, if_neg hlj]

@[expose] def ggSL9WCoord (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    MulAut (Multiplicative (Fin 3 → ZMod 7)) where
  toFun f := ofAdd (ggSL9WCoordFun i j e (toAdd f))
  invFun f := ofAdd (ggSL9WCoordFun i j e (toAdd f))
  left_inv f := by
    simp only [toAdd_ofAdd, ggSL9WCoordFun_invol hij, ofAdd_toAdd]
  right_inv f := by
    simp only [toAdd_ofAdd, ggSL9WCoordFun_invol hij, ofAdd_toAdd]
  map_mul' f g := by
    simp only [toAdd_mul, ← ofAdd_add]
    congr 1
    funext l
    simp only [ggSL9WCoordFun, Pi.add_apply]
    split_ifs <;> ring

theorem ggSL9WCoord_apply {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) (f : Fin 3 → ZMod 7) :
    ggSL9WCoord i j hij e (ofAdd f) = ofAdd (ggSL9WCoordFun i j e f) :=
  rfl

private theorem ggSL9WCoord_apply' {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (f : Multiplicative (Fin 3 → ZMod 7)) :
    ggSL9WCoord i j hij e f = ofAdd (ggSL9WCoordFun i j e (toAdd f)) := rfl

theorem ggSL9W_conj_torusCoord {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (f : Multiplicative (Fin 3 → ZMod 7)) :
    ggSL9W i j hij e * ggSL9TorusCoord f * (ggSL9W i j hij e)⁻¹ =
      ggSL9TorusCoord (ggSL9WCoord i j hij e f) := by
  have hw : ggSL9W i j hij e * ggSL9W i j hij e = 1 := ggSL9W_mul_self hij e
  have hwinv : (ggSL9W i j hij e)⁻¹ = ggSL9W i j hij e := inv_eq_of_mul_eq_one_right hw
  rw [hwinv]
  apply LinearEquiv.ext
  intro v
  funext l
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [ggSL9W_apply]
  by_cases hli : l = i
  · rw [if_pos hli]
    rw [ggSL9TorusCoord_apply']
    simp only [ggSL9W_apply]
    rw [if_neg (Ne.symm hij)]
    rw [if_pos trivial]
    rw [ggSL9WCoord_apply' hij e f]
    rw [ggSL9TorusCoord_apply']
    rw [toAdd_ofAdd]
    rw [hli]
    rw [ggSL9WCoordFun_apply_i]
    rw [mul_pow, ggSL9_pow_exp_mul, ← ggSL9Zeta_field_pow_val_mul_neg]
  · rw [if_neg hli]
    by_cases hlj : l = j
    · rw [if_pos hlj]
      rw [ggSL9TorusCoord_apply']
      simp only [ggSL9W_apply]
      rw [if_pos trivial]
      rw [ggSL9WCoord_apply' hij e f]
      rw [ggSL9TorusCoord_apply']
      rw [toAdd_ofAdd]
      rw [hlj]
      rw [ggSL9WCoordFun_apply_j hij e (toAdd f)]
      rw [mul_pow, ggSL9_pow_exp_mul', ← ggSL9Zeta_field_pow_val_mul_pos]
    · rw [if_neg hlj]
      rw [ggSL9TorusCoord_apply']
      simp only [ggSL9W_apply]
      rw [if_neg hli, if_neg hlj]
      rw [ggSL9WCoord_apply' hij e f]
      rw [ggSL9TorusCoord_apply']
      rw [toAdd_ofAdd]
      rw [ggSL9WCoordFun_apply_of_ne e (toAdd f) hli hlj]

theorem ggSL9WCoord_mul_self {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    ggSL9WCoord i j hij e * ggSL9WCoord i j hij e = 1 := by
  apply MulEquiv.ext
  intro f
  rw [MulAut.mul_apply, MulAut.one_apply,
    show f = ofAdd (toAdd f) from (ofAdd_toAdd f).symm,
    ggSL9WCoord_apply, ggSL9WCoord_apply]
  exact congrArg ofAdd (ggSL9WCoordFun_invol hij e (toAdd f))

private noncomputable def ggSL9WCoordFixEquiv (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    {f : Fin 3 → ZMod 7 // ggSL9WCoordFun i j e f = f} ≃ ({l : Fin 3 // l ≠ j} → ZMod 7) where
  toFun f := fun l => f.1 l.1
  invFun g := ⟨fun l => if h : l = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨l, h⟩, by
    funext l
    by_cases hli : l = i
    · rw [hli, ggSL9WCoordFun_apply_i]
      show 2 ^ (-e).val * (if h : j = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨j, h⟩) =
        (if h : i = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨i, h⟩)
      rw [dif_pos rfl, dif_neg hij, ← mul_assoc, ggSL9_two_pow_neg_mul, one_mul]
    · by_cases hlj : l = j
      · rw [hlj, ggSL9WCoordFun_apply_j hij e]
        show 2 ^ e.val * (if h : i = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨i, h⟩) =
          (if h : j = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨j, h⟩)
        rw [dif_neg hij, dif_pos rfl]
      · rw [ggSL9WCoordFun_apply_of_ne e _ hli hlj]⟩
  left_inv f := by
    apply Subtype.ext
    funext l
    show (if h : l = j then 2 ^ e.val * f.1 i else f.1 l) = f.1 l
    by_cases hlj : l = j
    · rw [dif_pos hlj, hlj]
      have h := congrFun f.2 j
      rw [ggSL9WCoordFun_apply_j hij e] at h
      exact h
    · rw [dif_neg hlj]
  right_inv g := by
    funext x
    show (if h : x.1 = j then 2 ^ e.val * g ⟨i, hij⟩ else g ⟨x.1, h⟩) = g x
    rw [dif_neg x.2]

private noncomputable def ggSL9MultiplicativeFixEquiv (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    {f : Multiplicative (Fin 3 → ZMod 7) // ggSL9WCoord i j hij e f = f} ≃
      {g : Fin 3 → ZMod 7 // ggSL9WCoordFun i j e g = g} where
  toFun f := ⟨toAdd f.1, by
    have h : toAdd (ggSL9WCoord i j hij e f.1) = toAdd f.1 := congrArg toAdd f.2
    rw [ggSL9WCoord_apply', toAdd_ofAdd] at h
    exact h⟩
  invFun g := ⟨ofAdd g.1, by
    rw [ggSL9WCoord_apply', toAdd_ofAdd, g.2]⟩
  left_inv f := by
    apply Subtype.ext
    exact ofAdd_toAdd f.1
  right_inv g := by
    apply Subtype.ext
    exact toAdd_ofAdd g.1

theorem card_fix_ggSL9WCoord {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    Nat.card {f : Multiplicative (Fin 3 → ZMod 7) // ggSL9WCoord i j hij e f = f} = 7 ^ 2 := by
  rw [Nat.card_congr (ggSL9MultiplicativeFixEquiv i j hij e),
    Nat.card_congr (ggSL9WCoordFixEquiv i j hij e), Nat.card_fun,
    Nat.card_eq_fintype_card (α := ZMod 7), ZMod.card]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun l : Fin 3 => l = j),
    Fintype.card_subtype_eq, Fintype.card_fin]

theorem ggSL9WCoord_inj {i j i' j' : Fin 3} (hij : i < j) (hij' : i' < j') {e e' : ZMod 3}
    (h : ggSL9WCoord i j hij.ne e = ggSL9WCoord i' j' hij'.ne e') :
    i = i' ∧ j = j' ∧ e = e' := by
  have h1 : ggSL9WCoordFun i j e (Pi.single i (1 : ZMod 7)) =
      ggSL9WCoordFun i' j' e' (Pi.single i (1 : ZMod 7)) := by
    have hc := congrArg (fun φ : MulAut (Multiplicative (Fin 3 → ZMod 7)) =>
      φ (ofAdd (Pi.single i (1 : ZMod 7)))) h
    rw [ggSL9WCoord_apply, ggSL9WCoord_apply] at hc
    exact ofAdd.injective hc
  have h2 : ggSL9WCoordFun i j e (Pi.single j (1 : ZMod 7)) =
      ggSL9WCoordFun i' j' e' (Pi.single j (1 : ZMod 7)) := by
    have hc := congrArg (fun φ : MulAut (Multiplicative (Fin 3 → ZMod 7)) =>
      φ (ofAdd (Pi.single j (1 : ZMod 7)))) h
    rw [ggSL9WCoord_apply, ggSL9WCoord_apply] at hc
    exact ofAdd.injective hc
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;> fin_cases e <;> fin_cases e'
  all_goals
    first
      | exact absurd hij (by decide)
      | exact absurd hij' (by decide)
      | (refine ⟨rfl, rfl, rfl⟩)
      | (exact absurd h1 (by decide))
      | (exact absurd h2 (by decide))

@[expose] noncomputable def ggSL9BlockFun (i j : Fin 3) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) : GGSL9V :=
  fun l => if l = i then M 0 0 * v i + M 0 1 * v j ^ 2 ^ (-e).val
    else if l = j then (M 1 0 * v i + M 1 1 * v j ^ 2 ^ (-e).val) ^ 2 ^ e.val else v l

private theorem ggSL9BlockFun_apply_i {i j : Fin 3} (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) :
    ggSL9BlockFun i j e M v i = M 0 0 * v i + M 0 1 * v j ^ 2 ^ (-e).val := by
  unfold ggSL9BlockFun
  rw [if_pos rfl]

private theorem ggSL9BlockFun_apply_j {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) :
    ggSL9BlockFun i j e M v j =
      (M 1 0 * v i + M 1 1 * v j ^ 2 ^ (-e).val) ^ 2 ^ e.val := by
  unfold ggSL9BlockFun
  rw [if_neg (Ne.symm hij), if_pos rfl]

private theorem ggSL9BlockFun_apply_of_ne {i j : Fin 3} (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) {l : Fin 3}
    (hli : l ≠ i) (hlj : l ≠ j) : ggSL9BlockFun i j e M v l = v l := by
  unfold ggSL9BlockFun
  rw [if_neg hli, if_neg hlj]

private theorem ggSL9_zero_pow_two (n : ℕ) : (0 : GaloisField 2 3) ^ 2 ^ n = 0 :=
  zero_pow (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))

private theorem ggSL9BlockFun_single_i_apply_i {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single i (1 : GaloisField 2 3)) i = M 0 0 := by
  rw [ggSL9BlockFun_apply_i e M (Pi.single i 1),
    Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, ggSL9_zero_pow_two, mul_one, mul_zero,
    add_zero]

private theorem ggSL9BlockFun_single_i_apply_j {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single i (1 : GaloisField 2 3)) j = M 1 0 ^ 2 ^ e.val := by
  rw [ggSL9BlockFun_apply_j hij e M (Pi.single i 1),
    Pi.single_eq_of_ne hij.symm, Pi.single_eq_same, ggSL9_zero_pow_two, mul_one, mul_zero,
    add_zero]

private theorem ggSL9BlockFun_single_j_apply_i {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single j (1 : GaloisField 2 3)) i = M 0 1 := by
  rw [ggSL9BlockFun_apply_i e M (Pi.single j 1),
    Pi.single_eq_of_ne hij, Pi.single_eq_same, one_pow, mul_one, mul_zero, zero_add]

private theorem ggSL9BlockFun_single_j_apply_j {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single j (1 : GaloisField 2 3)) j = M 1 1 ^ 2 ^ e.val := by
  rw [ggSL9BlockFun_apply_j hij e M (Pi.single j 1),
    Pi.single_eq_of_ne hij, Pi.single_eq_same, one_pow, mul_one, mul_zero, zero_add]

theorem ggSL9BlockFun_add (i j : Fin 3) (e : ZMod 3) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
    (v w : GGSL9V) :
    ggSL9BlockFun i j e M (v + w) = ggSL9BlockFun i j e M v + ggSL9BlockFun i j e M w := by
  funext l
  by_cases hli : l = i
  · rw [hli, ggSL9BlockFun_apply_i e M (v + w)]
    change M 0 0 * (v i + w i) + M 0 1 * ((v j + w j) ^ 2 ^ (-e).val) =
      ggSL9BlockFun i j e M v i + ggSL9BlockFun i j e M w i
    rw [ggSL9BlockFun_apply_i e M v, ggSL9BlockFun_apply_i e M w,
      add_pow_char_pow, mul_add, mul_add]
    abel
  · by_cases hlj : l = j
    · have hij : i ≠ j := fun h => hli (hlj.trans h.symm)
      rw [hlj, ggSL9BlockFun_apply_j hij e M (v + w)]
      change (M 1 0 * (v i + w i) + M 1 1 * ((v j + w j) ^ 2 ^ (-e).val)) ^ 2 ^ e.val =
        ggSL9BlockFun i j e M v j + ggSL9BlockFun i j e M w j
      rw [ggSL9BlockFun_apply_j hij e M v, ggSL9BlockFun_apply_j hij e M w]
      have hinner : (v j + w j) ^ 2 ^ (-e).val =
          v j ^ 2 ^ (-e).val + w j ^ 2 ^ (-e).val := by
        rw [add_pow_char_pow]
      have hbase : M 1 0 * (v i + w i) + M 1 1 * ((v j + w j) ^ 2 ^ (-e).val) =
          (M 1 0 * v i + M 1 1 * v j ^ 2 ^ (-e).val) +
            (M 1 0 * w i + M 1 1 * w j ^ 2 ^ (-e).val) := by
        rw [hinner, mul_add, mul_add]
        abel
      rw [hbase, add_pow_char_pow]
    · rw [ggSL9BlockFun_apply_of_ne e M (v + w) hli hlj]
      change v l + w l = ggSL9BlockFun i j e M v l + ggSL9BlockFun i j e M w l
      rw [ggSL9BlockFun_apply_of_ne e M v hli hlj,
        ggSL9BlockFun_apply_of_ne e M w hli hlj]

theorem ggSL9BlockFun_mul {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) :
    ggSL9BlockFun i j e (M * N) v = ggSL9BlockFun i j e M (ggSL9BlockFun i j e N v) := by
  funext l
  by_cases hli : l = i
  · rw [hli]
    rw [ggSL9BlockFun_apply_i e (M * N) v,
      ggSL9BlockFun_apply_i e M (ggSL9BlockFun i j e N v),
      ggSL9BlockFun_apply_i e N v, ggSL9BlockFun_apply_j hij e N v,
      ggSL9_pow_exp_mul, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two]
    ring
  · by_cases hlj : l = j
    · rw [hlj]
      rw [ggSL9BlockFun_apply_j hij e (M * N) v,
        ggSL9BlockFun_apply_j hij e M (ggSL9BlockFun i j e N v),
        ggSL9BlockFun_apply_i e N v, ggSL9BlockFun_apply_j hij e N v,
        ggSL9_pow_exp_mul, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two]
      congr 1
      ring
    · rw [ggSL9BlockFun_apply_of_ne e (M * N) v hli hlj,
        ggSL9BlockFun_apply_of_ne e M (ggSL9BlockFun i j e N v) hli hlj,
        ggSL9BlockFun_apply_of_ne e N v hli hlj]

theorem ggSL9BlockFun_one (i j : Fin 3) (e : ZMod 3) (v : GGSL9V) :
    ggSL9BlockFun i j e 1 v = v := by
  funext l
  by_cases hli : l = i
  · rw [hli, ggSL9BlockFun_apply_i e 1 v]
    simp [Matrix.one_apply]
  · by_cases hlj : l = j
    · have hij : i ≠ j := fun h => hli (hlj.trans h.symm)
      rw [hlj, ggSL9BlockFun_apply_j hij e 1 v]
      simp [Matrix.one_apply]
      exact ggSL9_pow_exp_mul' (v j) e
    · rw [ggSL9BlockFun_apply_of_ne e 1 v hli hlj]

@[expose] noncomputable def ggSL9BlockEquiv (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3)
    (M : GL (Fin 2) (GaloisField 2 3)) : GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  { AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk' (ggSL9BlockFun i j e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)))
        (ggSL9BlockFun_add i j e _)) with
    invFun := ggSL9BlockFun i j e
      ((M⁻¹ : GL (Fin 2) (GaloisField 2 3)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
    left_inv := fun v => by
      change ggSL9BlockFun i j e _ (ggSL9BlockFun i j e _ v) = v
      rw [← ggSL9BlockFun_mul hij, Units.inv_mul, ggSL9BlockFun_one]
    right_inv := fun v => by
      change ggSL9BlockFun i j e _ (ggSL9BlockFun i j e _ v) = v
      rw [← ggSL9BlockFun_mul hij, Units.mul_inv, ggSL9BlockFun_one] }

@[expose] noncomputable def ggSL9BlockGL (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    GL (Fin 2) (GaloisField 2 3) →* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  MonoidHom.mk' (ggSL9BlockEquiv i j hij e) fun M N => LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply]
    change ggSL9BlockFun i j e ((M * N : GL (Fin 2) (GaloisField 2 3)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) v = ggSL9BlockFun i j e _ (ggSL9BlockFun i j e _ v)
    rw [Units.val_mul, ggSL9BlockFun_mul hij]

theorem ggSL9BlockGL_apply {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (M : GL (Fin 2) (GaloisField 2 3)) (v : GGSL9V) :
    ggSL9BlockGL i j hij e M v =
      ggSL9BlockFun i j e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) v :=
  rfl

private theorem ggSL9BlockGL_transvection_01 {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (c : GaloisField 2 3) :
    ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)) =
      ggSL9Root j i hij.symm (-e).val c := by
  have h00 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 0 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h01 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 1 = c := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h10 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h11 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 1 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  apply LinearEquiv.ext
  intro v
  funext l
  rw [ggSL9BlockGL_apply, ggSL9Root_apply]
  by_cases hli : l = i
  · rw [hli, ggSL9BlockFun_apply_i e _ v, ggSL9Fun_apply_j hij.symm (-e).val c v,
      h00, h01, one_mul]
  · by_cases hlj : l = j
    · rw [hlj, ggSL9BlockFun_apply_j hij e _ v, ggSL9Fun_apply_self hij.symm (-e).val c v,
        h10, h11, zero_mul, one_mul, zero_add, ggSL9_pow_exp_mul']
    · rw [ggSL9BlockFun_apply_of_ne e _ v hli hlj,
        ggSL9Fun_apply_of_ne (-e).val c v hli]

private theorem ggSL9BlockGL_transvection_10 {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)
    (c : GaloisField 2 3) :
    ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)) =
      ggSL9Root i j hij e.val (c ^ 2 ^ e.val) := by
  have h00 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 0 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h01 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 1 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h10 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 0 = c := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h11 : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) c) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 1 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  apply LinearEquiv.ext
  intro v
  funext l
  rw [ggSL9BlockGL_apply, ggSL9Root_apply]
  by_cases hli : l = i
  · rw [hli, ggSL9BlockFun_apply_i e _ v, ggSL9Fun_apply_self hij e.val (c ^ 2 ^ e.val) v,
      h00, h01, one_mul, zero_mul, add_zero]
  · by_cases hlj : l = j
    · rw [hlj, ggSL9BlockFun_apply_j hij e _ v, ggSL9Fun_apply_j hij e.val (c ^ 2 ^ e.val) v,
        h10, h11, one_mul, add_pow_char_pow, mul_pow, ggSL9_pow_exp_mul']
      ring
    · rw [ggSL9BlockFun_apply_of_ne e _ v hli hlj,
        ggSL9Fun_apply_of_ne e.val (c ^ 2 ^ e.val) v hlj]

theorem ggSL9BlockGL_injective {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    Function.Injective (ggSL9BlockGL i j hij e) := by
  intro M N h
  have h1 := congrArg (fun g : GGSL9V ≃ₗ[ZMod 2] GGSL9V =>
    g (Pi.single i (1 : GaloisField 2 3))) h
  rw [ggSL9BlockGL_apply, ggSL9BlockGL_apply] at h1
  have h00 : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 0 =
      (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 0 := by
    have hi := congrFun h1 i
    rwa [ggSL9BlockFun_single_i_apply_i hij e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)),
      ggSL9BlockFun_single_i_apply_i hij e (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))] at hi
  have h10 : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 0 =
      (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 0 := by
    have hj := congrFun h1 j
    rw [ggSL9BlockFun_single_i_apply_j hij e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)),
      ggSL9BlockFun_single_i_apply_j hij e (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))] at hj
    have hj' := congrArg (fun x : GaloisField 2 3 => x ^ 2 ^ (-e).val) hj
    rwa [ggSL9_pow_exp_mul, ggSL9_pow_exp_mul] at hj'
  have h2 := congrArg (fun g : GGSL9V ≃ₗ[ZMod 2] GGSL9V =>
    g (Pi.single j (1 : GaloisField 2 3))) h
  rw [ggSL9BlockGL_apply, ggSL9BlockGL_apply] at h2
  have h01 : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 1 =
      (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 1 := by
    have hi := congrFun h2 i
    rwa [ggSL9BlockFun_single_j_apply_i hij e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)),
      ggSL9BlockFun_single_j_apply_i hij e (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))] at hi
  have h11 : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 1 =
      (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 1 1 := by
    have hj := congrFun h2 j
    rw [ggSL9BlockFun_single_j_apply_j hij e (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)),
      ggSL9BlockFun_single_j_apply_j hij e (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))] at hj
    have hj' := congrArg (fun x : GaloisField 2 3 => x ^ 2 ^ (-e).val) hj
    rwa [ggSL9_pow_exp_mul, ggSL9_pow_exp_mul] at hj'
  apply Units.ext
  apply Matrix.ext
  intro a b
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

theorem range_ggSL9BlockGL_comp_toGL {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    ((ggSL9BlockGL i j hij e).comp Matrix.SpecialLinearGroup.toGL).range = ggSL9J i j e := by
  let Φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) →*
      (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
    (ggSL9BlockGL i j hij e).comp Matrix.SpecialLinearGroup.toGL
  change Φ.range = ggSL9J i j e
  have htop : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) (GaloisField 2 3) →
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hgen : Φ '' (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) (GaloisField 2 3) →
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))) =
      ggSL9RootSet i j e.val ∪ ggSL9RootSet j i (-e).val := by
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      rcases t with ⟨a, b, hab, c⟩
      fin_cases a <;> fin_cases b
      · exact absurd hab (by decide)
      · right
        refine ⟨hij.symm, c, ?_⟩
        rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
        exact ggSL9BlockGL_transvection_01 hij e c
      · left
        refine ⟨hij, c ^ 2 ^ e.val, ?_⟩
        rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
        exact ggSL9BlockGL_transvection_10 hij e c
      · exact absurd hab (by decide)
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨h, μ, rfl⟩ := hx
        refine ⟨Matrix.TransvectionStruct.toSpecialLinearGroup
            ⟨1, 0, (by decide : (1 : Fin 2) ≠ 0), μ ^ 2 ^ (-e).val⟩, ⟨_, rfl⟩, ?_⟩
        rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
        change ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide)
            (μ ^ 2 ^ (-e).val))) = ggSL9Root i j hij e.val μ
        rw [ggSL9BlockGL_transvection_10 hij e (μ ^ 2 ^ (-e).val), ggSL9_pow_exp_mul']
      · obtain ⟨h, μ, rfl⟩ := hx
        refine ⟨Matrix.TransvectionStruct.toSpecialLinearGroup
            ⟨0, 1, (by decide : (0 : Fin 2) ≠ 1), μ⟩, ⟨_, rfl⟩, ?_⟩
        rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
        change ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) μ)) =
          ggSL9Root j i hij.symm (-e).val μ
        exact ggSL9BlockGL_transvection_01 hij e μ
  calc Φ.range =
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3))).map Φ :=
        MonoidHom.range_eq_map Φ
    _ = (Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
          Matrix.TransvectionStruct (Fin 2) (GaloisField 2 3) →
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)))).map Φ := by rw [htop]
    _ = Subgroup.closure (Φ '' (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
          Matrix.TransvectionStruct (Fin 2) (GaloisField 2 3) →
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)))) :=
        MonoidHom.map_closure Φ _
    _ = Subgroup.closure (ggSL9RootSet i j e.val ∪ ggSL9RootSet j i (-e).val) := by rw [hgen]
    _ = ggSL9J i j e := rfl

private noncomputable def ggSL9JEquivSL2 {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    ↥(ggSL9J i j e) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
  ((MonoidHom.ofInjective (f := (ggSL9BlockGL i j hij e).comp Matrix.SpecialLinearGroup.toGL)
      ((ggSL9BlockGL_injective hij e).comp
        Matrix.SpecialLinearGroup.toGL_injective)).trans
    (MulEquiv.subgroupCongr (range_ggSL9BlockGL_comp_toGL hij e))).symm

theorem isQuasisimple_ggSL9J {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    CFSG.Assembly.IsQuasisimple (ggSL9J i j e) := by
  refine CFSG.Assembly.IsQuasisimple.of_mulEquiv (ggSL9JEquivSL2 hij e) ?_
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
      (GaloisField 2 3) (by norm_num)
      (Or.inr (by rw [GaloisField.card 2 3 (by norm_num)]; norm_num))
      (Or.inr (by rw [GaloisField.card 2 3 (by norm_num)]; norm_num)))

theorem seven_dvd_card_ggSL9J {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    7 ∣ Nat.card (ggSL9J i j e) := by
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) = 504 := by
    letI := Fintype.ofFinite (GaloisField 2 3)
    have hq : Fintype.card (GaloisField 2 3) = 8 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
      norm_num
    rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
    norm_num
  have hcard : Nat.card (ggSL9J i j e) = 504 := by
    rw [Nat.card_congr (ggSL9JEquivSL2 hij e).toEquiv, hSL]
  rw [hcard]
  norm_num

end CFSG.StandardType

end
