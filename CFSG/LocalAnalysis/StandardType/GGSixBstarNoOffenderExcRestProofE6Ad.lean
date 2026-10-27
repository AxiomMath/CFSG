module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace NoOffRest

open TableBExc.E6Three

section Faithful

variable {τ : Tag} {p : ℕ}

theorem adAct_add (w : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    adAct τ p w (x + y) = adAct τ p w x + adAct τ p w y := by
  funext i
  simp only [adAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem adAct_sub (w : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    adAct τ p w (x - y) = adAct τ p w x - adAct τ p w y := by
  funext i
  simp only [adAct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem eq_one_of_adAct [Fact p.Prime] (hp2 : p ≠ 2) {w : WeylGroup τ}
    (hw : ∀ x, adAct τ p w x = x) : w = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hij : ∀ i j : Fin τ.rank,
      (((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j : ℤ) : ZMod p) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (hw (Pi.single j 1)) i
    simpa only [adAct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using h
  refine inv_eq_one.mp (NoOffExc.eq_one_of_torusAct hp2 fun x => ?_)
  funext k
  rw [TableBExc.torusAct, weyl_smul_eq_sum]
  simp only [TableBExc.redMod, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, hij, mul_ite, mul_one, mul_zero]
  simp [TableBExc.liftMod]

theorem adPerm_injective [Fact p.Prime] (hp2 : p ≠ 2) : Function.Injective (adPerm τ p) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact eq_one_of_adAct hp2 fun x => by rw [← adPerm_apply, hw]; rfl

end Faithful

section Ad

local instance noOffRestFactThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem actNoOffender_adPerm_E6 :
    ActNoOffender (adPerm .E6 3) 3 := by
  refine actNoOffender_of_sylow Nat.prime_three (S := modelHomE6.range) ?_
    fun A hAS hA hA1 => ?_
  · rw [NoOffExc.index_eq_of_card card_range_modelHomE6 NoOffExc.card_weyl_E6
      (show 81 * 640 = 51840 by norm_num) (by norm_num)]
    norm_num
  · have h := noOffender_E6ad A hAS hA hA1
    rw [Nat.card_eq_fintype_card (α := Fin Tag.E6.rank → ZMod 3), Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    exact h

end Ad

section Hyp

@[expose] def kE6 : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def kDotP (p : ℕ) (x : Fin Tag.E6.rank → ZMod p) : ZMod p :=
  ∑ i, ((kE6 i : ℤ) : ZMod p) * x i

variable {p : ℕ}

theorem kDotP_add (x y : Fin Tag.E6.rank → ZMod p) : kDotP p (x + y) = kDotP p x + kDotP p y := by
  simp only [kDotP, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem kDotP_sub (x y : Fin Tag.E6.rank → ZMod p) : kDotP p (x - y) = kDotP p x - kDotP p y := by
  simp only [kDotP, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem kDotP_neg (x : Fin Tag.E6.rank → ZMod p) : kDotP p (-x) = -kDotP p x := by
  simp only [kDotP, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem kDotP_smul (c : ZMod p) (x : Fin Tag.E6.rank → ZMod p) :
    kDotP p (c • x) = c * kDotP p x := by
  simp only [kDotP, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem kDotP_zero : kDotP p 0 = 0 := by
  simp [kDotP]

theorem kDotP_adRefl {i : Fin Tag.E6.rank}
    (hi : kDotP p (fun j => ((Tag.E6.cartan i j : ℤ) : ZMod p)) = 0)
    (x : Fin Tag.E6.rank → ZMod p) : kDotP p (adRefl .E6 p i x) = kDotP p x := by
  rw [adRefl, kDotP_sub, kDotP_smul, hi, mul_zero, sub_zero]

theorem kDot_cartan : ∀ i : Fin Tag.E6.rank,
    kDotP 3 (fun j => ((Tag.E6.cartan i j : ℤ) : ZMod 3)) = 0 := by
  decide +kernel

theorem kDot_adWord (ω : List (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ZMod 3) :
    kDotP 3 (adWord .E6 3 ω x) = kDotP 3 x := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change kDotP 3 (adRefl .E6 3 i (adWord .E6 3 ω x)) = kDotP 3 x
    exact (kDotP_adRefl (kDot_cartan i) _).trans ih

theorem kDot_adAct (w : WeylGroup .E6) (x : Fin Tag.E6.rank → ZMod 3) :
    kDotP 3 (adAct .E6 3 w x) = kDotP 3 x := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective w
  rw [← adWord_eq_adAct]
  exact kDot_adWord ω x

variable (p) in
@[expose] def hypSub : AddSubgroup (Fin Tag.E6.rank → ZMod p) where
  carrier := {x | kDotP p x = 0}
  add_mem' {x y} hx hy := by
    change kDotP p (x + y) = 0
    rw [kDotP_add, show kDotP p x = 0 from hx, show kDotP p y = 0 from hy, add_zero]
  zero_mem' := kDotP_zero
  neg_mem' {x} hx := by
    change kDotP p (-x) = 0
    rw [kDotP_neg, show kDotP p x = 0 from hx, neg_zero]

instance hypSubAddCommGroup (p : ℕ) : AddCommGroup (hypSub p) :=
  AddSubgroup.toAddCommGroup (hypSub p)

abbrev hypE6 : AddSubgroup (Fin Tag.E6.rank → ZMod 3) := hypSub 3

theorem mem_hypE6 {x : Fin Tag.E6.rank → ZMod 3} : x ∈ hypE6 ↔ kDotP 3 x = 0 :=
  Iff.rfl

theorem adAct_mem_hypE6 (w : WeylGroup .E6) {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) :
    adAct .E6 3 w x ∈ hypE6 :=
  mem_hypE6.mpr ((kDot_adAct w x).trans (mem_hypE6.mp hx))

@[expose] noncomputable def hypPerm : WeylGroup .E6 →* Equiv.Perm hypE6 where
  toFun w :=
    { toFun := fun x => ⟨adAct .E6 3 w x, adAct_mem_hypE6 w x.2⟩
      invFun := fun x => ⟨adAct .E6 3 w⁻¹ x, adAct_mem_hypE6 w⁻¹ x.2⟩
      left_inv x := Subtype.ext (by
        show adAct .E6 3 w⁻¹ (adAct .E6 3 w x) = x
        rw [← adAct_mul, inv_mul_cancel, adAct_one])
      right_inv x := Subtype.ext (by
        show adAct .E6 3 w (adAct .E6 3 w⁻¹ x) = x
        rw [← adAct_mul, mul_inv_cancel, adAct_one]) }
  map_one' := Equiv.ext fun x => Subtype.ext (adAct_one _)
  map_mul' w w' := Equiv.ext fun x => Subtype.ext (adAct_mul w w' _)

theorem coe_hypPerm_apply (w : WeylGroup .E6) (x : hypE6) :
    ((hypPerm w x : hypE6) : Fin Tag.E6.rank → ZMod 3) = adAct .E6 3 w x :=
  rfl

theorem card_hypE6 : Nat.card hypE6 = 3 ^ 5 := by
  change Nat.card {x : Fin Tag.E6.rank → ZMod 3 // kDotP 3 x = 0} = 3 ^ 5
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end Hyp

end NoOffRest

end CFSG.StandardType
