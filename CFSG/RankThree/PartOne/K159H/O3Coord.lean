module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.K159H.O3Basic
public import CFSG.RankThree.PartOne.KFR4.B3Comb

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.PartOne.KFR4

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] (p : ℕ)

@[expose] def zpowE (ζ : Kˣ) (x : ZMod p) : Kˣ := ζ ^ x.val

variable {p} {ζ : Kˣ}

theorem zpowE_zero : zpowE p ζ 0 = 1 := by simp [zpowE]

theorem zpowE_add [NeZero p] (hζ : ζ ^ p = 1) (x y : ZMod p) : zpowE p ζ (x + y) = zpowE p ζ x * zpowE p ζ y := by
  unfold zpowE
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) p, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem zpowE_neg [NeZero p] (hζ : ζ ^ p = 1) (x : ZMod p) : zpowE p ζ (-x) = (zpowE p ζ x)⁻¹ := by
  have := zpowE_add hζ x (-x)
  rw [add_neg_cancel, zpowE_zero] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem zpowE_inj (hζ : IsPrimitiveRoot ζ p) [NeZero p] {x y : ZMod p} (h : zpowE p ζ x = zpowE p ζ y) : x = y := by
  have := hζ.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h
  exact ZMod.val_injective p this

theorem zpowE_eq_one_iff (hζ : IsPrimitiveRoot ζ p) [NeZero p] {x : ZMod p} : zpowE p ζ x = 1 ↔ x = 0 := by
  constructor
  · intro h
    exact zpowE_inj hζ (h.trans zpowE_zero.symm)
  · rintro rfl
    exact zpowE_zero

variable (ζ)

@[expose] def dOf (v : Vec p) : Fin 3 → Kˣ := fun k => zpowE p ζ (v k)

variable {ζ}

theorem wt_dOf_inl (v : Vec p) (k : Fin 3) : wt (dOf ζ v) (Sum.inl k) = zpowE p ζ (v k) := rfl

theorem wt_dOf_inr [NeZero p] (hζ : ζ ^ p = 1) (v : Vec p) (k : Fin 3) :
    wt (dOf ζ v) (Sum.inr k) = zpowE p ζ (-v k) := by
  rw [zpowE_neg hζ]
  rfl

theorem dOf_add [NeZero p] (hζ : ζ ^ p = 1) (v w : Vec p) : dOf ζ (v + w) = dOf ζ v * dOf ζ w := by
  funext k
  exact zpowE_add hζ (v k) (w k)

theorem dOf_zero : dOf ζ (0 : Vec p) = 1 := by
  funext k
  exact zpowE_zero

@[expose] def dHom [NeZero p] (hζ : ζ ^ p = 1) : Multiplicative (Vec p) →* (Fin 3 → Kˣ) where
  toFun v := dOf ζ (Multiplicative.toAdd v)
  map_one' := dOf_zero
  map_mul' _ _ := dOf_add hζ _ _

theorem dHom_injective [NeZero p] (hζ : IsPrimitiveRoot ζ p) : Function.Injective (dHom hζ.pow_eq_one) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext k
  exact zpowE_inj hζ (congrFun h k)

theorem torH_injective (r : ℕ) : Function.Injective (torH K A r) := by
  intro d d' h
  funext k
  have := congrArg (fun e : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) =>
    (e (hypVec K A (Sum.inl k))).1 (Sum.inl k)) h
  simp only [torH_hypVec, Prod.smul_fst, Pi.smul_apply, hypVec_fst, smul_eq_mul, ite_true, mul_one] at this
  exact Units.ext this

end CFSG.RankThree.PartOne.K159H
