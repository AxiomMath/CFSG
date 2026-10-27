module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Module.ZMod

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.RepresentationTheory.Maschke

namespace CFSG
end CFSG
open CFSG
/-!
# Linear algebra of finite right near-fields

This file contains the characteristic, prime-field module, and right-multiplication
action used by both Peterfalvi Appendix II and Huppert--Blackburn XI.2.5.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixII

universe u

public theorem rightNearField_nsmul_one_mul {F : Type u} [RightNearField F]
    (n : ℕ) (x : F) : (n • (1 : F)) * x = n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, RightNearField.right_distrib, ih, one_mul, succ_nsmul]

public theorem rightNearField_nsmul_one_mul_nsmul_one {F : Type u} [RightNearField F]
    (m n : ℕ) : (m • (1 : F)) * (n • (1 : F)) = (m * n) • (1 : F) := by
  rw [rightNearField_nsmul_one_mul]
  simpa [Nat.mul_comm] using (mul_nsmul (1 : F) n m).symm

public theorem rightNearField_addOrderOf_one_prime {F : Type u} [RightNearField F] [Finite F] :
    Nat.Prime (addOrderOf (1 : F)) := by
  let p := addOrderOf (1 : F)
  change Nat.Prime p
  have hp_pos : 0 < p := addOrderOf_pos 1
  have hp_ne_one : p ≠ 1 := by
    intro hp
    have : (1 : F) = 0 := AddMonoid.addOrderOf_eq_one_iff.mp hp
    exact one_ne_zero this
  rw [Nat.prime_def_lt]
  constructor
  · omega
  intro m hm_lt hm_dvd
  rcases hm_dvd with ⟨n, hpn⟩
  by_contra hm_ne_one
  have hm_pos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp at hpn
    omega
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hpn
    omega
  have hprod_zero :
      (m • (1 : F)) * (n • (1 : F)) = 0 := by
    rw [rightNearField_nsmul_one_mul_nsmul_one, ← hpn]
    exact (addOrderOf_dvd_iff_nsmul_eq_zero.mp (dvd_refl p))
  rcases mul_eq_zero.mp hprod_zero with hm_zero | hn_zero
  · have hp_dvd_m : p ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hm_zero
    exact (Nat.not_le_of_lt hm_lt) (Nat.le_of_dvd hm_pos hp_dvd_m)
  · have hp_dvd_n : p ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn_zero
    have hn_lt : n < m * n := by
      have hm_two : 2 ≤ m := by omega
      nlinarith
    have hn_lt_p : n < p := by rw [hpn]; exact hn_lt
    exact (Nat.not_le_of_lt hn_lt_p) (Nat.le_of_dvd hn_pos hp_dvd_n)

/-- The additive characteristic annihilates every element, not only one. -/
public theorem rightNearField_addOrderOf_one_nsmul_eq_zero
    {F : Type u} [RightNearField F] (x : F) :
    addOrderOf (1 : F) • x = 0 := by
  rw [← rightNearField_nsmul_one_mul]
  rw [addOrderOf_dvd_iff_nsmul_eq_zero.mp
    (dvd_refl (addOrderOf (1 : F)))]
  exact zero_mul x

/-- The canonical vector-space structure on the additive group over its prime
field. -/
@[expose, reducible] public noncomputable def rightNearFieldZModModule
    (F : Type u) [RightNearField F] :
    Module (ZMod (addOrderOf (1 : F))) F :=
  AddCommGroup.zmodModule (n := addOrderOf (1 : F))
    rightNearField_addOrderOf_one_nsmul_eq_zero

/-- The finite additive group has prime-power cardinality, with prime equal
to the near-field characteristic. -/
public theorem rightNearField_natCard_eq_addOrderOf_one_pow
    {F : Type u} [RightNearField F] [Finite F] :
    ∃ n : ℕ, Nat.card F = addOrderOf (1 : F) ^ n := by
  let p := addOrderOf (1 : F)
  have hp : Nat.Prime p := rightNearField_addOrderOf_one_prime
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Module (ZMod p) F := rightNearFieldZModModule F
  letI : Fintype F := Fintype.ofFinite F
  have hcard := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
  refine ⟨Module.finrank (ZMod p) F, ?_⟩
  change Nat.card F = p ^ Module.finrank (ZMod p) F

  simpa [Nat.card_eq_fintype_card] using hcard

/-- The additive group of a finite right near-field, in multiplicative notation, is elementary abelian of its additive characteristic. -/
public theorem rightNearFieldMultiplicativeIsElementaryAbelian
    {F : Type u} [RightNearField F] :
    IsElementaryAbelian (addOrderOf (1 : F)) (Multiplicative F) :=
  { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
    exponent_dvd_p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      change addOrderOf (1 : F) • Multiplicative.toAdd x = 0
      exact rightNearField_addOrderOf_one_nsmul_eq_zero
        (F := F) (Multiplicative.toAdd x) }

/-- Right multiplication, regarded as an additive endomorphism. -/
@[expose] public noncomputable def rightNearFieldRightMulAddHom
    {F : Type u} [RightNearField F] (a : F) : F →+ F where
  toFun x := x * a
  map_zero' := zero_mul a
  map_add' x y := RightNearField.right_distrib x y a

/-- Right multiplication by a unit, as an additive automorphism. -/
@[expose] public noncomputable def rightNearFieldRightMulAddEquiv
    {F : Type u} [RightNearField F] (a : Fˣ) : F ≃+ F :=
  AddEquiv.ofBijective (rightNearFieldRightMulAddHom (a : F))
    (Units.mulRight_bijective a)

/-- The faithful action of the opposite unit group by right multiplication.
The opposite multiplication records the reversal in composition of right
translations. -/
@[expose] public noncomputable def rightNearFieldRightMulAction
    {F : Type u} [RightNearField F] :
    (Fˣ)ᵐᵒᵖ →* Multiplicative (F ≃+ F) where
  toFun a := Multiplicative.ofAdd (rightNearFieldRightMulAddEquiv a.unop)
  map_one' := by
    ext x
    change x * (1 : F) = x
    simp
  map_mul' a b := by
    ext x
    change x * ((b.unop * a.unop : Fˣ) : F) =
      (x * (b.unop : F)) * (a.unop : F)
    rw [Units.val_mul, mul_assoc]
/-- Evaluation of the opposite-unit right-multiplication action. -/
@[simp]
public theorem rightNearFieldRightMulAction_apply
    {F : Type u} [RightNearField F] (a : (Fˣ)ᵐᵒᵖ) (x : F) :
    (rightNearFieldRightMulAction a).toAdd x = x * (a.unop : F) := by
  rfl

/-- The prime-field representation of the opposite unit group by right
multiplication. -/
@[expose] public noncomputable def rightNearFieldRightMulRepresentation
    {F : Type u} [RightNearField F] [Finite F]
    [Module (ZMod (addOrderOf (1 : F))) F] :
    Representation (ZMod (addOrderOf (1 : F))) (Fˣ)ᵐᵒᵖ F := by
  let L : (F →+ F) ≃+ (F →ₗ[ZMod (addOrderOf (1 : F))] F) :=
    AddMonoidHom.toZModLinearMapEquiv _
  exact
    { toFun := fun a => L (rightNearFieldRightMulAddHom (a.unop : F))
      map_one' := by
        ext x
        change x * (1 : F) = x
        simp
      map_mul' := by
        intro a b
        ext x
        change x * ((b.unop * a.unop : Fˣ) : F) =
          (x * (b.unop : F)) * (a.unop : F)
        rw [Units.val_mul, mul_assoc] }

@[simp]
public theorem rightNearFieldRightMulRepresentation_apply
    {F : Type u} [RightNearField F] [Finite F]
    [Module (ZMod (addOrderOf (1 : F))) F]
    (a : (Fˣ)ᵐᵒᵖ) (x : F) :
    rightNearFieldRightMulRepresentation a x = x * (a.unop : F) := by
  rfl

/-- Restriction of the opposite-unit right-multiplication representation to a
subgroup, stated directly to avoid elaboration diamonds for endomorphism
composition. -/
@[expose] public noncomputable def rightNearFieldRightMulSubgroupRepresentation
    {F : Type u} [RightNearField F] [Finite F]
    [Module (ZMod (addOrderOf (1 : F))) F]
    (A : Subgroup (Fˣ)ᵐᵒᵖ) :
    Representation (ZMod (addOrderOf (1 : F))) A F := by
  let L : (F →+ F) ≃+ (F →ₗ[ZMod (addOrderOf (1 : F))] F) :=
    AddMonoidHom.toZModLinearMapEquiv _
  exact
    { toFun := fun a => L (rightNearFieldRightMulAddHom (a.1.unop : F))
      map_one' := by
        ext x
        change x * (1 : F) = x
        simp
      map_mul' := by
        intro a b
        ext x
        change x * ((b.1.unop * a.1.unop : Fˣ) : F) =
          (x * (b.1.unop : F)) * (a.1.unop : F)
        rw [Units.val_mul, mul_assoc] }

@[simp]
public theorem rightNearFieldRightMulSubgroupRepresentation_apply
    {F : Type u} [RightNearField F] [Finite F]
    [Module (ZMod (addOrderOf (1 : F))) F]
    (A : Subgroup (Fˣ)ᵐᵒᵖ) (a : A) (x : F) :
    rightNearFieldRightMulSubgroupRepresentation A a x =
      x * (a.1.unop : F) := by
  rfl

/-- A commutative subgroup of the unit group acts additively by right multiplication. -/
@[expose, reducible] public noncomputable def rightNearFieldUnitsMulDistribMulAction
    {F : Type u} [RightNearField F] (A : Subgroup Fˣ) [IsMulCommutative A] :
    MulDistribMulAction A (Multiplicative F) where
  smul a x := Multiplicative.ofAdd (Multiplicative.toAdd x * ((a : A) : Fˣ))
  one_smul x := by
    change Multiplicative.toAdd x * (1 : F) = Multiplicative.toAdd x
    simp
  mul_smul a b x := by
    change Multiplicative.toAdd x * (((a * b : A) : Fˣ) : F) =
      (Multiplicative.toAdd x * ((b : A) : Fˣ)) * ((a : A) : Fˣ)
    rw [Subgroup.coe_mul, Units.val_mul]
    have habU : (a : Fˣ) * (b : Fˣ) = (b : Fˣ) * (a : Fˣ) :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm a b)
    have habF : ((a : Fˣ) : F) * (b : Fˣ) =
        ((b : Fˣ) : F) * (a : Fˣ) := congrArg Units.val habU
    rw [habF, mul_assoc]
  smul_mul a x y := by
    change (Multiplicative.toAdd x + Multiplicative.toAdd y) * ((a : A) : Fˣ) =
      Multiplicative.toAdd x * ((a : A) : Fˣ) +
        Multiplicative.toAdd y * ((a : A) : Fˣ)
    exact RightNearField.right_distrib _ _ _
  smul_one a := by
    change (0 : F) * ((a : A) : Fˣ) = 0
    exact zero_mul _

end PFAppendixII
end CFSG.BenderSuzuki
