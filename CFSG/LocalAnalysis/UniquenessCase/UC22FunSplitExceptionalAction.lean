module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSimplyLacedGeometry
public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegreeEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarSts
public import TauCeti.Data.ZMod.IntUnitsPower
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.ExceptionalAction

open Subgroup Matrix Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.AS81.Sec2
open CFSG.StandardType.TableBExcTwo
open scoped MatrixGroups

abbrev V3 := Fin 3 → ZMod 2

local instance : AddCommGroup V3 := Pi.addCommGroup
local instance : Module (ZMod 2) V3 := Pi.module _ _ _

@[expose] def e7Label : Fin 7 → V3 :=
  ![![1, 0, 0], ![1, 0, 1], ![1, 1, 1], ![0, 0, 1],
    ![0, 1, 1], ![1, 1, 0], ![0, 1, 0]]

@[expose] def e8Label : Fin 8 → V3 :=
  ![![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1],
    ![0, 0, 1], ![0, 1, 1], ![1, 1, 0], ![0, 1, 0]]

theorem e7Label_ne_zero : ∀ i, e7Label i ≠ 0 := by decide +kernel

theorem e7Label_bijective : Function.Bijective
    (fun i : Fin 7 => (⟨e7Label i, e7Label_ne_zero i⟩ : {v : V3 // v ≠ 0})) := by
  decide +kernel

theorem e8Label_bijective : Function.Bijective e8Label := by decide +kernel

def e7LabelEquiv : Fin 7 ≃ {v : V3 // v ≠ 0} :=
  Equiv.ofBijective _ e7Label_bijective

def e8LabelEquiv : Fin 8 ≃ V3 := Equiv.ofBijective _ e8Label_bijective

@[expose] def e7Sign (v : V3) : Fin 7 → ZMod 2 :=
  ![v 0, 0, 0, v 1, 0, v 2, 0]

@[expose] def e8Sign (a : ZMod 2) (v : V3) : Fin 8 → ZMod 2 :=
  ![v 0, 0, 0, v 1, 0, v 2, 0, a + v 1]

theorem e7Sign_add (v w : V3) : e7Sign (v + w) = e7Sign v + e7Sign w := by
  ext i; fin_cases i <;> rfl

theorem e7Sign_zero : e7Sign 0 = 0 := by ext i; fin_cases i <;> rfl

theorem e7Sign_injective : Function.Injective e7Sign := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 3
  · exact congrFun h 5

theorem e8Sign_add (a b : ZMod 2) (v w : V3) :
    e8Sign (a + b) (v + w) = e8Sign a v + e8Sign b w := by
  ext i; fin_cases i <;> try rfl
  change a + b + (v 1 + w 1) = (a + v 1) + (b + w 1)
  abel

theorem e8Sign_zero : e8Sign 0 0 = 0 := by ext i; fin_cases i <;> rfl

theorem e8Sign_injective : Function.Injective (fun av : ZMod 2 × V3 => e8Sign av.1 av.2) := by
  intro av bw h
  have hv : av.2 = bw.2 := by
    funext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 3
    · exact congrFun h 5
  have ha : av.1 = bw.1 := by
    have h7 := congrFun h 7
    change av.1 + av.2 1 = bw.1 + bw.2 1 at h7
    rw [hv] at h7
    exact add_right_cancel h7
  exact Prod.ext ha hv

theorem e7Frame_coroot_sign : ∀ (k : Fin 7) (i : Fin 7),
    (iform (frameE7Root k) (Pi.single i 1) : ZMod 2) = e7Sign (e7Label k) i := by
  decide +kernel

theorem e8Frame_coroot_sign : ∀ (k : Fin 8) (i : Fin 8),
    (iform (frameE8Root k) (Pi.single i 1) : ZMod 2) = e8Sign 1 (e8Label k) i := by
  decide +kernel

theorem e7Frame_norm : ∀ k : Fin 7, iform (frameE7Root k) (frameE7Root k) = 2 := by
  decide +kernel

theorem e8Frame_norm : ∀ k : Fin 8, iform (frameE8Root k) (frameE8Root k) = 2 := by
  decide +kernel

def binaryUnit (F : Type) [Field F] : Multiplicative (ZMod 2) →* Fˣ :=
  (CFSG.LieType.Chevalley.intUnitsMap F).comp
    (AddEquiv.toMultiplicative TauCeti.additiveIntUnitsAddEquiv.symm).toMonoidHom

theorem binaryUnit_apply {F : Type} [Field F] (a : ZMod 2) :
    binaryUnit F (.ofAdd a) = if a = 0 then 1 else -1 := by
  have hpre : TauCeti.additiveIntUnitsAddEquiv.symm a =
      Additive.ofMul (if a = 0 then (1 : ℤˣ) else -1) := by
    apply TauCeti.additiveIntUnitsAddEquiv.injective
    rw [TauCeti.additiveIntUnitsAddEquiv.apply_symm_apply,
      TauCeti.additiveIntUnitsAddEquiv_apply]
    have hcases : a = 0 ∨ a = 1 := by revert a; decide
    rcases hcases with rfl | rfl <;> simp
  change CFSG.LieType.Chevalley.intUnitsMap F
    (Additive.toMul (TauCeti.additiveIntUnitsAddEquiv.symm a)) = _
  rw [hpre]
  split <;> simp_all [CFSG.LieType.Chevalley.intUnitsMap]

theorem binaryUnit_injective {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (binaryUnit F) :=
  (CFSG.LieType.Chevalley.intUnitsMap_injective hF).comp
    (AddEquiv.toMultiplicative TauCeti.additiveIntUnitsAddEquiv.symm).injective

def binaryDiag {τ : Tag} (F : Type) [Field F] :
    Multiplicative (Fin τ.rank → ZMod 2) →* ModGL τ F where
  toFun v := rootDiagUnit τ (fun i => binaryUnit F (.ofAdd (v.toAdd i)))
  map_one' := by
    rw [show (fun i => binaryUnit F (.ofAdd ((1 : Multiplicative (Fin τ.rank → ZMod 2)).toAdd i))) = 1
      by funext i; exact map_one (binaryUnit F), rootDiagUnit_one]
  map_mul' v w := by
    rw [show (fun i => binaryUnit F (.ofAdd ((v * w).toAdd i))) =
        (fun i => binaryUnit F (.ofAdd (v.toAdd i))) *
          (fun i => binaryUnit F (.ofAdd (w.toAdd i))) by
      funext i; exact map_mul (binaryUnit F) _ _, rootDiagUnit_mul]

@[expose] def e7ActionRoot : Fin 3 → Fin 2 → (Fin Tag.E7.rank → ℤ) :=
  ![![![1, 0, 0, 0, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0]],
    ![![1, 0, 1, 1, 0, 0, 0], ![1, 2, 2, 3, 2, 2, 1]],
    ![![1, 0, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 1]]]

@[expose] def e7ActionIndex : Fin 3 → Fin 7 → Fin 7 :=
  ![![1, 0, 5, 3, 4, 2, 6], ![4, 6, 2, 3, 0, 5, 1], ![2, 1, 0, 6, 4, 5, 3]]

theorem e7ActionIndex_bijective : ∀ k, Function.Bijective (e7ActionIndex k) := by
  decide +kernel

def e7ActionPerm (k : Fin 3) : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective _ (e7ActionIndex_bijective k)

theorem e7ActionRoot_mem : ∀ k j, e7ActionRoot k j ∈ rootFinset .E7 := by
  decide +kernel

theorem e7ActionRoot_norm : ∀ k j, iform (e7ActionRoot k j) (e7ActionRoot k j) = 2 := by
  decide +kernel

theorem e7Action_reflect_frame : ∀ (k : Fin 3) (i : Fin 7),
    let v := frameE7Root i - iform (e7ActionRoot k 1) (frameE7Root i) • e7ActionRoot k 1
    v - iform (e7ActionRoot k 0) v • e7ActionRoot k 0 = frameE7Root (e7ActionIndex k i) ∨
      v - iform (e7ActionRoot k 0) v • e7ActionRoot k 0 = -frameE7Root (e7ActionIndex k i) := by
  decide +kernel

theorem e7ActionPerm_sq : ∀ k, e7ActionPerm k ^ 2 = 1 := by
  intro k
  apply Equiv.ext
  intro i
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  change e7ActionIndex k (e7ActionIndex k i) = i
  revert k i
  decide +kernel

theorem e7ActionPerm_zero_ne_one : e7ActionPerm 0 ≠ 1 := by
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 7) => σ 0) h
  change (1 : Fin 7) = 0 at h0
  exact (by decide : (1 : Fin 7) ≠ 0) h0

@[expose] def e7CycleIndex : Fin 7 → Fin 7 := ![3, 4, 5, 6, 2, 0, 1]

theorem e7CycleIndex_bijective : Function.Bijective e7CycleIndex := by decide +kernel

def e7Cycle : Equiv.Perm (Fin 7) := Equiv.ofBijective _ e7CycleIndex_bijective

theorem e7ActionPerm_product : e7ActionPerm 2 * e7ActionPerm 1 * e7ActionPerm 0 = e7Cycle := by
  apply Equiv.ext
  intro i
  change e7ActionIndex 2 (e7ActionIndex 1 (e7ActionIndex 0 i)) = e7CycleIndex i
  revert i
  decide +kernel

theorem e7Cycle_pow_seven : e7Cycle ^ 7 = 1 := by
  apply Equiv.ext
  intro i
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  change (e7CycleIndex^[7]) i = i
  revert i
  decide +kernel

theorem e7ActionPerm_product_seven : (e7ActionPerm 2 * e7ActionPerm 1 * e7ActionPerm 0) ^ 7 = 1 := by
  rw [e7ActionPerm_product, e7Cycle_pow_seven]

theorem e7ActionPerm_product_ne_one : e7ActionPerm 2 * e7ActionPerm 1 * e7ActionPerm 0 ≠ 1 := by
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 7) => σ 0) h
  change (3 : Fin 7) = 0 at h0
  exact (by decide : (3 : Fin 7) ≠ 0) h0

def e7Binary (F : Type) [Field F] : Multiplicative V3 →* ModGL .E7 F :=
  (binaryDiag (τ := .E7) F).comp
    (AddMonoidHom.toMultiplicative
      ({ toFun := e7Sign, map_zero' := e7Sign_zero, map_add' := e7Sign_add } :
        V3 →+ (Fin 7 → ZMod 2)))

def e8Binary (F : Type) [Field F] : Multiplicative (ZMod 2 × V3) →* ModGL .E8 F :=
  (binaryDiag (τ := .E8) F).comp
    (AddMonoidHom.toMultiplicative
      ({ toFun := fun av => e8Sign av.1 av.2
         map_zero' := e8Sign_zero
         map_add' := fun av bw => e8Sign_add av.1 bw.1 av.2 bw.2 } :
          (ZMod 2 × V3) →+ (Fin 8 → ZMod 2)))

@[expose] def e8ActionRoot : Fin 4 → Fin 2 → (Fin Tag.E8.rank → ℤ) :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0]],
    ![![1, 0, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 2, 1, 0]],
    ![![1, 0, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 2, 2, 2, 2, 1]]]

@[expose] def e8ActionIndex : Fin 4 → Fin 8 → Fin 8 :=
  ![![0, 2, 1, 6, 4, 5, 3, 7], ![0, 5, 7, 3, 4, 1, 6, 2],
    ![0, 3, 2, 1, 7, 5, 6, 4], ![1, 0, 4, 3, 2, 5, 6, 7]]

theorem e8ActionIndex_bijective : ∀ k, Function.Bijective (e8ActionIndex k) := by
  decide +kernel

def e8ActionPerm (k : Fin 4) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective _ (e8ActionIndex_bijective k)

theorem e8ActionRoot_mem : ∀ k j, e8ActionRoot k j ∈ rootFinset .E8 := by
  decide +kernel

theorem e8ActionRoot_norm : ∀ k j, iform (e8ActionRoot k j) (e8ActionRoot k j) = 2 := by
  decide +kernel

theorem e8Action_reflect_frame : ∀ (k : Fin 4) (i : Fin 8),
    let v := frameE8Root i - iform (e8ActionRoot k 1) (frameE8Root i) • e8ActionRoot k 1
    v - iform (e8ActionRoot k 0) v • e8ActionRoot k 0 = frameE8Root (e8ActionIndex k i) ∨
      v - iform (e8ActionRoot k 0) v • e8ActionRoot k 0 = -frameE8Root (e8ActionIndex k i) := by
  decide +kernel

theorem e8ActionIndex_fix_zero : ∀ k : Fin 3, e8ActionIndex k.castSucc 0 = 0 := by
  decide +kernel

theorem e8ActionPerm_sq : ∀ k, e8ActionPerm k ^ 2 = 1 := by
  intro k
  apply Equiv.ext
  intro i
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  change e8ActionIndex k (e8ActionIndex k i) = i
  revert k i
  decide +kernel

theorem e8ActionPerm_zero_ne_one : e8ActionPerm 0 ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 8) => σ 1) h
  change (2 : Fin 8) = 1 at h1
  exact (by decide : (2 : Fin 8) ≠ 1) h1

@[expose] def e8CycleIndex : Fin 8 → Fin 8 := ![0, 4, 5, 6, 7, 3, 1, 2]

theorem e8CycleIndex_bijective : Function.Bijective e8CycleIndex := by decide +kernel

def e8Cycle : Equiv.Perm (Fin 8) := Equiv.ofBijective _ e8CycleIndex_bijective

theorem e8ActionPerm_product : e8ActionPerm 2 * e8ActionPerm 1 * e8ActionPerm 0 = e8Cycle := by
  apply Equiv.ext
  intro i
  change e8ActionIndex 2 (e8ActionIndex 1 (e8ActionIndex 0 i)) = e8CycleIndex i
  revert i
  decide +kernel

theorem e8Cycle_pow_seven : e8Cycle ^ 7 = 1 := by
  apply Equiv.ext
  intro i
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  change (e8CycleIndex^[7]) i = i
  revert i
  decide +kernel

theorem e8ActionPerm_product_seven : (e8ActionPerm 2 * e8ActionPerm 1 * e8ActionPerm 0) ^ 7 = 1 := by
  rw [e8ActionPerm_product, e8Cycle_pow_seven]

theorem e8ActionPerm_product_ne_one : e8ActionPerm 2 * e8ActionPerm 1 * e8ActionPerm 0 ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 8) => σ 1) h
  change (4 : Fin 8) = 1 at h1
  exact (by decide : (4 : Fin 8) ≠ 1) h1

theorem binaryDiag_injective {τ : Tag} {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (binaryDiag (τ := τ) F) := by
  intro v w h
  have hh := rootDiagUnit_injective h
  apply Multiplicative.ext
  funext i
  exact congrArg Multiplicative.toAdd (binaryUnit_injective hF (congrFun hh i))

def e7ActionWeyl (k : Fin 3) : WeylGroup .E7 :=
  rootReflection (e7ActionRoot k 0) * rootReflection (e7ActionRoot k 1)

theorem e7ActionWeyl_frame (k : Fin 3) (i : Fin 7) :
    e7ActionWeyl k • frameE7Root i = frameE7Root (e7ActionPerm k i) ∨
      e7ActionWeyl k • frameE7Root i = -frameE7Root (e7ActionPerm k i) := by
  have h0 := mem_rootFinset.mp (e7ActionRoot_mem k 0)
  have h1 := mem_rootFinset.mp (e7ActionRoot_mem k 1)
  have hc : ∀ j : Fin 2, ∀ v : Fin Tag.E7.rank → ℤ, corootPair (e7ActionRoot k j) v =
      iform (e7ActionRoot k j) v := by
    intro j v
    unfold corootPair
    rw [e7ActionRoot_norm]
    omega
  simp only [e7ActionWeyl, mul_smul, rootReflection_smul h0, rootReflection_smul h1, hc]
  exact e7Action_reflect_frame k i

def e8ActionWeyl (k : Fin 4) : WeylGroup .E8 :=
  rootReflection (e8ActionRoot k 0) * rootReflection (e8ActionRoot k 1)

theorem e8ActionWeyl_frame (k : Fin 4) (i : Fin 8) :
    e8ActionWeyl k • frameE8Root i = frameE8Root (e8ActionPerm k i) ∨
      e8ActionWeyl k • frameE8Root i = -frameE8Root (e8ActionPerm k i) := by
  have h0 := mem_rootFinset.mp (e8ActionRoot_mem k 0)
  have h1 := mem_rootFinset.mp (e8ActionRoot_mem k 1)
  have hc : ∀ j : Fin 2, ∀ v : Fin Tag.E8.rank → ℤ, corootPair (e8ActionRoot k j) v =
      iform (e8ActionRoot k j) v := by
    intro j v
    unfold corootPair
    rw [e8ActionRoot_norm]
    omega
  simp only [e8ActionWeyl, mul_smul, rootReflection_smul h0, rootReflection_smul h1, hc]
  exact e8Action_reflect_frame k i

theorem e7Binary_injective {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (e7Binary F) := by
  intro v w h
  have hh := binaryDiag_injective hF h
  exact congrArg Multiplicative.ofAdd (e7Sign_injective (congrArg Multiplicative.toAdd hh))

theorem e8Binary_injective {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (e8Binary F) := by
  intro v w h
  have hh := binaryDiag_injective hF h
  exact congrArg Multiplicative.ofAdd (e8Sign_injective (congrArg Multiplicative.toAdd hh))

theorem binaryUnit_intCast {F : Type} [Field F] (z : ℤ) :
    binaryUnit F (.ofAdd (z : ZMod 2)) = (-1 : Fˣ) ^ z := by
  rw [binaryUnit_apply, neg_one_zpow_eq_ite]
  simp only [ZMod.intCast_eq_zero_iff_even]

theorem e7Binary_frame {F : Type} [Field F] (k : Fin 7) :
    e7Binary F (.ofAdd (e7Label k)) = rootTorusSL2 .E7 F (frameE7Root k) (-1) := by
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (mem_rootFinset.mp (frameE7Root_mem k))]
  change rootDiagUnit .E7 (fun i => binaryUnit F (.ofAdd (e7Sign (e7Label k) i))) = _
  congr 1
  funext i
  change Fin 7 at i
  rw [← e7Frame_coroot_sign k i, binaryUnit_intCast, e7Frame_norm]
  congr 1
  omega

theorem e8Binary_frame {F : Type} [Field F] (k : Fin 8) :
    e8Binary F (.ofAdd (1, e8Label k)) = rootTorusSL2 .E8 F (frameE8Root k) (-1) := by
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (mem_rootFinset.mp (frameE8Root_mem k))]
  change rootDiagUnit .E8 (fun i => binaryUnit F (.ofAdd (e8Sign 1 (e8Label k) i))) = _
  congr 1
  funext i
  change Fin 8 at i
  rw [← e8Frame_coroot_sign k i, binaryUnit_intCast, e8Frame_norm]
  congr 1
  omega

theorem e7Binary_mem {F : Type} [Field F] (v : Multiplicative V3) :
    e7Binary F v ∈ adjointGroup .E7 F := by
  by_cases hv : v.toAdd = 0
  · have hv1 : v = 1 := congrArg Multiplicative.ofAdd hv
    rw [hv1, map_one]
    exact one_mem _
  · obtain ⟨k, hk⟩ := e7Label_bijective.2 ⟨v.toAdd, hv⟩
    have hk' : e7Label k = v.toAdd := congrArg Subtype.val hk
    have hvk : v = .ofAdd (e7Label k) := congrArg Multiplicative.ofAdd hk'.symm
    rw [hvk, e7Binary_frame]
    exact rootSL2_mem_adjointGroup _ _

theorem e8Binary_mem {F : Type} [Field F] (v : Multiplicative (ZMod 2 × V3)) :
    e8Binary F v ∈ adjointGroup .E8 F := by
  obtain ⟨k, hk⟩ := e8Label_bijective.2 v.toAdd.2
  have hframe : ∀ k : Fin 8, e8Binary F (.ofAdd (1, e8Label k)) ∈ adjointGroup .E8 F := by
    intro k
    rw [e8Binary_frame]
    exact rootSL2_mem_adjointGroup _ _
  have ha : v.toAdd.1 = 0 ∨ v.toAdd.1 = 1 := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact h _
  rcases ha with ha | ha
  · have hv : v = (.ofAdd (1, e8Label k) : Multiplicative (ZMod 2 × V3)) *
        .ofAdd (1, e8Label 0) := by
      apply Multiplicative.ext
      apply Prod.ext
      · change v.toAdd.1 = (1 : ZMod 2) + 1
        rw [ha]; rfl
      · change v.toAdd.2 = e8Label k + e8Label 0
        rw [hk, show e8Label 0 = 0 by decide +kernel, add_zero]
    rw [hv, map_mul]
    exact mul_mem (hframe k) (hframe 0)
  · have hv : v = .ofAdd (1, e8Label k) := by
      apply Multiplicative.ext
      exact Prod.ext ha hk.symm
    rw [hv]
    exact hframe k

def e7BinaryAdj (F : Type) [Field F] : Multiplicative V3 →* adjointGroup .E7 F :=
  (e7Binary F).codRestrict _ e7Binary_mem

def e8BinaryAdj (F : Type) [Field F] : Multiplicative (ZMod 2 × V3) →* adjointGroup .E8 F :=
  (e8Binary F).codRestrict _ e8Binary_mem

theorem e7BinaryAdj_injective {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (e7BinaryAdj F) :=
  fun _ _ h => e7Binary_injective hF (congrArg Subtype.val h)

theorem e8BinaryAdj_injective {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Function.Injective (e8BinaryAdj F) :=
  fun _ _ h => e8Binary_injective hF (congrArg Subtype.val h)

theorem e7BinaryAdj_frame {F : Type} [Field F] (k : Fin 7) :
    e7BinaryAdj F (.ofAdd (e7Label k)) = rho F frameE7 k (-1) := by
  apply Subtype.ext
  change e7Binary F (.ofAdd (e7Label k)) = rootSL2 .E7 F (frameE7Root k) (-1)
  rw [e7Binary_frame, rootTorusSL2]
  congr 1
  exact (CFSG.LieType.HighestRoot.neg_one_eq_HSL_neg_one).symm

theorem e8BinaryAdj_frame {F : Type} [Field F] (k : Fin 8) :
    e8BinaryAdj F (.ofAdd (1, e8Label k)) = rho F frameE8 k (-1) := by
  apply Subtype.ext
  change e8Binary F (.ofAdd (1, e8Label k)) = rootSL2 .E8 F (frameE8Root k) (-1)
  rw [e8Binary_frame, rootTorusSL2]
  congr 1
  exact (CFSG.LieType.HighestRoot.neg_one_eq_HSL_neg_one).symm

theorem rho_range_eq_rootPair {τ : Tag} {F : Type} [Field F] {d : ℕ}
    (A : OrthFrame τ d) (i : Fin (d + 1)) :
    (rho F A i).range = (rootRankOneGroup τ F (A.root i)).subgroupOf (adjointGroup τ F) := by
  ext r
  change (∃ a : SL2 F, rho F A i a = r) ↔ (r : ModGL τ F) ∈ rootRankOneGroup τ F (A.root i)
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem map_conj_nrep_rootPair {τ : Tag} {F : Type} [Field F]
    (w : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ((rootRankOneGroup τ F β).subgroupOf (adjointGroup τ F)).map
        (MulAut.conj (nrep τ F w)).toMonoidHom =
      (rootRankOneGroup τ F (w • β)).subgroupOf (adjointGroup τ F) := by
  rw [map_conj_subgroupOf (exceptional_Lang_root_rank_one_data τ F β).2.2.2.2.2.1]
  congr 1
  rw [(exceptional_Lang_root_rank_one_torus_transport τ F hβ).1,
    (exceptional_Lang_root_rank_one_torus_transport τ F (IsRoot.smul hβ w)).1,
    Subgroup.map_sup]
  have htr := (canonical_weyl_root_transport τ F).2.1
  change (rootSubgroup τ F β).map (MulAut.conj (canonicalRep (coxeterSystem τ) F w)).toMonoidHom ⊔
      (rootSubgroup τ F (-β)).map (MulAut.conj (canonicalRep (coxeterSystem τ) F w)).toMonoidHom = _
  rw [htr w β hβ, htr w (-β) (IsRoot.neg hβ), smul_neg]

theorem rootPair_neg {τ : Tag} {F : Type} [Field F] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : rootRankOneGroup τ F (-β) = rootRankOneGroup τ F β := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ F (IsRoot.neg hβ)).1,
    (exceptional_Lang_root_rank_one_torus_transport τ F hβ).1, neg_neg, sup_comm]

theorem e7Action_conj_rho {F : Type} [Field F] (k : Fin 3) (i : Fin 7) :
    conjSub (nrep .E7 F (e7ActionWeyl k)) (rho F frameE7 i).range =
      (rho F frameE7 (e7ActionPerm k i)).range := by
  rw [conjSub, rho_range_eq_rootPair, rho_range_eq_rootPair]
  change ((rootRankOneGroup .E7 F (frameE7Root i)).subgroupOf (adjointGroup .E7 F)).map
    (MulAut.conj (nrep .E7 F (e7ActionWeyl k))).toMonoidHom = _
  rw [map_conj_nrep_rootPair (F := F) (e7ActionWeyl k) (mem_rootFinset.mp (frameE7Root_mem i))]
  rcases e7ActionWeyl_frame k i with h | h
  · rw [h]; rfl
  · rw [h, rootPair_neg (mem_rootFinset.mp (frameE7Root_mem _))]; rfl

theorem e8Action_conj_rho {F : Type} [Field F] (k : Fin 4) (i : Fin 8) :
    conjSub (nrep .E8 F (e8ActionWeyl k)) (rho F frameE8 i).range =
      (rho F frameE8 (e8ActionPerm k i)).range := by
  rw [conjSub, rho_range_eq_rootPair, rho_range_eq_rootPair]
  change ((rootRankOneGroup .E8 F (frameE8Root i)).subgroupOf (adjointGroup .E8 F)).map
    (MulAut.conj (nrep .E8 F (e8ActionWeyl k))).toMonoidHom = _
  rw [map_conj_nrep_rootPair (F := F) (e8ActionWeyl k) (mem_rootFinset.mp (frameE8Root_mem i))]
  rcases e8ActionWeyl_frame k i with h | h
  · rw [h]; rfl
  · rw [h, rootPair_neg (mem_rootFinset.mp (frameE8Root_mem _))]; rfl

section AbstractAction

variable {X : Type} [Group X] {Δ : Set (Subgroup X)}

theorem conj_uniqueInvolution (z : Δ → X)
    (hz : ∀ J : Δ, IsUniqueInvolution J.1 (z J))
    (g : conjSetStab Δ) (J : Δ) :
    (g : X) * z J * (g : X)⁻¹ = z (conjPermHom (le_refl (conjSetStab Δ)) g J) := by
  have hc := (hz J).conj (g : X)
  have hsub : conjSub (g : X) J.1 =
      (conjPermHom (le_refl (conjSetStab Δ)) g J : Subgroup X) := by
    rw [conjPermHom_apply]
    simp only [conjSub, CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate, inv_inv]
  rw [hsub] at hc
  exact hc.eq (hz _)

theorem mem_conjPermHom_range_of_indexed_conjugation
    {ι : Type} (e : ι ≃ Δ) (σ : Equiv.Perm ι) (x : X)
    (hx : ∀ i, conjSub x (e i).1 = (e (σ i)).1) :
    e.permCongrHom σ ∈ (conjPermHom (le_refl (conjSetStab Δ))).range := by
  have hxi : ∀ i, conjSub x⁻¹ (e i).1 = (e (σ.symm i)).1 := by
    intro i
    have h := congrArg (conjSub x⁻¹) (hx (σ.symm i))
    simpa only [σ.apply_symm_apply, conjSub_inv_conjSub] using h.symm
  have hstab : x ∈ conjSetStab Δ := by
    rw [mem_conjSetStab]
    intro J
    change J ∈ Δ ↔ conjSub x⁻¹ J ∈ Δ
    constructor
    · intro hJ
      obtain ⟨i, hi⟩ := e.surjective ⟨J, hJ⟩
      have hi' : (e i).1 = J := congrArg Subtype.val hi
      rw [← hi', hxi]
      exact (e (σ.symm i)).2
    · intro hJ
      obtain ⟨i, hi⟩ := e.surjective ⟨conjSub x⁻¹ J, hJ⟩
      have hi' : (e i).1 = conjSub x⁻¹ J := congrArg Subtype.val hi
      have hh := hx i
      rw [hi', conjSub_conjSub_inv] at hh
      exact hh.symm ▸ (e (σ i)).2
  refine ⟨⟨x, hstab⟩, ?_⟩
  apply Equiv.ext
  intro J
  obtain ⟨i, rfl⟩ := e.surjective J
  apply Subtype.ext
  rw [conjPermHom_apply]
  simpa only [conjSub, CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate,
    inv_inv, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply] using hx i

theorem exists_injective_GL32_of_binary_frame
    (e : {v : V3 // v ≠ 0} ≃ Δ)
    (z : Multiplicative V3 →* X) (hinj : Function.Injective z)
    (hz : ∀ v : {v : V3 // v ≠ 0},
      IsUniqueInvolution (e v).1 (z (.ofAdd v.1))) :
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    ∃ f : ρ.range →* GL (Fin 3) (ZMod 2), Function.Injective f ∧
      ∀ (a : ρ.range) (v : {v : V3 // v ≠ 0}),
        (f a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1 =
          (e.symm (a.1 (e v))).1 := by
  classical
  let ρ := conjPermHom (le_refl (conjSetStab Δ))
  let π : ρ.range →* Equiv.Perm {v : V3 // v ≠ 0} :=
    e.symm.permCongrHom.toMonoidHom.comp ρ.range.subtype
  have hπ : ∀ (a : ρ.range) (v : {v : V3 // v ≠ 0}),
      π a v = e.symm (a.1 (e v)) := fun _ _ => rfl
  have hconj : ∀ (a : ρ.range), ∃ g : X, ∀ v : {v : V3 // v ≠ 0},
      g * z (.ofAdd v.1) * g⁻¹ = z (.ofAdd (π a v).1) := by
    intro a
    obtain ⟨g, hg⟩ := a.2
    refine ⟨g, fun v => ?_⟩
    have hc := conj_uniqueInvolution (fun J : Δ => z (.ofAdd (e.symm J).1))
      (fun J => by simpa only [Equiv.apply_symm_apply] using hz (e.symm J)) g (e v)
    simpa only [Equiv.symm_apply_apply, hg, hπ, ρ] using hc
  have hgl : ∀ a : ρ.range, ∃ M : GL (Fin 3) (ZMod 2),
      ∀ v : {v : V3 // v ≠ 0}, (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1 = (π a v).1 := by
    intro a
    apply CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16t3_gl3_of_perm (π a)
    intro v w _ hsum
    obtain ⟨g, hg⟩ := hconj a
    apply congrArg Multiplicative.toAdd
    apply hinj
    change z (.ofAdd (π a ⟨v.1 + w.1, hsum⟩).1) =
      z ((.ofAdd (π a v).1 : Multiplicative V3) * .ofAdd (π a w).1)
    rw [map_mul, ← hg, ← hg, ← hg]
    change g * z ((.ofAdd v.1 : Multiplicative V3) * .ofAdd w.1) * g⁻¹ = _
    rw [map_mul]
    group
  let f₀ : ρ.range → GL (Fin 3) (ZMod 2) := fun a => (hgl a).choose
  have hf₀ : ∀ a v,
      (f₀ a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1 = (π a v).1 :=
    fun a => (hgl a).choose_spec
  let f : ρ.range →* GL (Fin 3) (ZMod 2) :=
    { toFun := f₀
      map_one' := by
        apply Units.ext
        apply Matrix.ext_of_mulVec_single
        intro i
        have hi : (Pi.single i (1 : ZMod 2) : V3) ≠ 0 := by
          intro h0; have := congrFun h0 i; simp at this
        simp only [hf₀ 1 ⟨_, hi⟩, map_one, Equiv.Perm.one_apply,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      map_mul' a b := by
        apply Units.ext
        apply Matrix.ext_of_mulVec_single
        intro i
        have hi : (Pi.single i (1 : ZMod 2) : V3) ≠ 0 := by
          intro h0; have := congrFun h0 i; simp at this
        let v : {v : V3 // v ≠ 0} := ⟨Pi.single i 1, hi⟩
        rw [hf₀ (a * b) v, Matrix.GeneralLinearGroup.coe_mul,
          ← Matrix.mulVec_mulVec, hf₀ b v, hf₀ a (π b v)]
        exact congrArg Subtype.val (congrArg (fun σ => σ v) (map_mul π a b)) }
  refine ⟨f, ?_, fun a v => (hf₀ a v).trans (congrArg Subtype.val (hπ a v))⟩
  intro a b hab
  apply Subtype.ext
  apply Equiv.ext
  intro J
  obtain ⟨v, rfl⟩ := e.surjective J
  apply e.symm.injective
  apply Subtype.ext
  rw [← hπ, ← hπ, ← hf₀ a v, ← hf₀ b v]
  exact congrArg (fun M : GL (Fin 3) (ZMod 2) =>
    (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1) hab

theorem surjective_GL32_of_two_seven
    {A : Type} [Group A] (f : A →* GL (Fin 3) (ZMod 2)) (a b : A)
    (ha2 : f a ^ 2 = 1) (ha1 : f a ≠ 1) (hb7 : f b ^ 7 = 1) (hb1 : f b ≠ 1) :
    Function.Surjective f := by
  have h2 : orderOf (f a) = 2 := orderOf_eq_prime ha2 ha1
  have h7 : orderOf (f b) = 7 := orderOf_eq_prime hb7 hb1
  have h2dvd : 2 ∣ Nat.card f.range := by
    have h := orderOf_dvd_natCard (⟨f a, ⟨a, rfl⟩⟩ : f.range)
    have he : orderOf (⟨f a, ⟨a, rfl⟩⟩ : f.range) = orderOf (f a) :=
      (orderOf_injective f.range.subtype Subtype.val_injective _).symm
    rwa [he, h2] at h
  have h7dvd : 7 ∣ Nat.card f.range := by
    have h := orderOf_dvd_natCard (⟨f b, ⟨b, rfl⟩⟩ : f.range)
    have he : orderOf (⟨f b, ⟨b, rfl⟩⟩ : f.range) = orderOf (f b) :=
      (orderOf_injective f.range.subtype Subtype.val_injective _).symm
    rwa [he, h7] at h
  exact MonoidHom.range_eq_top.mp
    (CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2dvd h7dvd)

theorem nonempty_equiv_GL32_of_injective_of_two_seven
    {A : Type} [Group A] [Finite A] (f : A →* GL (Fin 3) (ZMod 2))
    (hf : Function.Injective f) (a b : A)
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb7 : b ^ 7 = 1) (hb1 : b ≠ 1) :
    Nonempty (A ≃* GL (Fin 3) (ZMod 2)) := by
  have hfa : f a ≠ 1 := fun h => ha1 (hf (h.trans (map_one f).symm))
  have hfb : f b ≠ 1 := fun h => hb1 (hf (h.trans (map_one f).symm))
  have hsurj := surjective_GL32_of_two_seven f a b
    (by rw [← map_pow, ha2, map_one]) hfa (by rw [← map_pow, hb7, map_one]) hfb
  exact ⟨MulEquiv.ofBijective f ⟨hf, hsurj⟩⟩

theorem nonempty_equiv_GL32_of_e7_binary_frame
    [Finite X] (e : Fin 7 ≃ Δ)
    (z : Multiplicative V3 →* X) (hinj : Function.Injective z)
    (hz : ∀ i, IsUniqueInvolution (e i).1 (z (.ofAdd (e7Label i))))
    (hgen : ∀ k : Fin 3, ∃ x : X, ∀ i,
      conjSub x (e i).1 = (e (e7ActionPerm k i)).1) :
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* GL (Fin 3) (ZMod 2)) := by
  let ρ := conjPermHom (le_refl (conjSetStab Δ))
  let ev : {v : V3 // v ≠ 0} ≃ Δ := e7LabelEquiv.symm.trans e
  have hlabel : ∀ v : {v : V3 // v ≠ 0},
      e7Label (e7LabelEquiv.symm v) = v.1 := fun v =>
    congrArg Subtype.val (e7LabelEquiv.apply_symm_apply v)
  have hzv : ∀ v : {v : V3 // v ≠ 0}, IsUniqueInvolution (ev v).1 (z (.ofAdd v.1)) := by
    intro v
    simpa only [ev, Equiv.trans_apply, hlabel] using hz (e7LabelEquiv.symm v)
  obtain ⟨f, hf, _⟩ := exists_injective_GL32_of_binary_frame ev z hinj hzv
  have hmem : ∀ k : Fin 3, e.permCongrHom (e7ActionPerm k) ∈ ρ.range := by
    intro k
    obtain ⟨x, hx⟩ := hgen k
    exact mem_conjPermHom_range_of_indexed_conjugation e _ x hx
  let a : ρ.range := ⟨e.permCongrHom (e7ActionPerm 0), hmem 0⟩
  let b : ρ.range := ⟨e.permCongrHom (e7ActionPerm 2 * e7ActionPerm 1 * e7ActionPerm 0), by
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (hmem 2) (hmem 1)) (hmem 0)⟩
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change e.permCongrHom (e7ActionPerm 0) ^ 2 = 1
    rw [← map_pow, e7ActionPerm_sq, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply e7ActionPerm_zero_ne_one
    apply e.permCongrHom.injective
    exact (congrArg Subtype.val h).trans (map_one e.permCongrHom).symm
  have hb7 : b ^ 7 = 1 := by
    apply Subtype.ext
    change e.permCongrHom (e7ActionPerm 2 * e7ActionPerm 1 * e7ActionPerm 0) ^ 7 = 1
    rw [← map_pow, e7ActionPerm_product_seven, map_one]
  have hb1 : b ≠ 1 := by
    intro h
    apply e7ActionPerm_product_ne_one
    apply e.permCongrHom.injective
    exact (congrArg Subtype.val h).trans (map_one e.permCongrHom).symm
  exact nonempty_equiv_GL32_of_injective_of_two_seven f hf a b ha2 ha1 hb7 hb1

theorem conjPermHom_mem_affinePerms_of_binary_frame
    (e : V3 ≃ Δ) (z : Multiplicative (ZMod 2 × V3) →* X)
    (hinj : Function.Injective z)
    (hz : ∀ v : V3, IsUniqueInvolution (e v).1 (z (.ofAdd (1, v)))) :
    ∀ a : (conjPermHom (le_refl (conjSetStab Δ))).range,
      e.symm.permCongrHom a.1 ∈ CFSG.LocalAnalysis.ComponentInitial.affinePerms (Fin 3 → ZMod 2) := by
  classical
  intro a
  let σ : Equiv.Perm V3 := e.symm.permCongrHom a.1
  obtain ⟨g, hg⟩ := a.2
  have hconj : ∀ v, (g : X) * z (.ofAdd (1, v)) * (g : X)⁻¹ = z (.ofAdd (1, σ v)) := by
    intro v
    have hc := conj_uniqueInvolution (fun J : Δ => z (.ofAdd (1, e.symm J)))
      (fun J => by simpa only [Equiv.apply_symm_apply] using hz (e.symm J)) g (e v)
    simpa only [σ, hg, Equiv.symm_apply_apply, Equiv.permCongrHom_coe,
      Equiv.permCongr_apply, Equiv.symm_symm] using hc
  have hsum : ∀ v w, σ (v + w) = σ v + σ w + σ 0 := by
    intro v w
    have hcoords : (.ofAdd (1, v + w) : Multiplicative (ZMod 2 × V3)) =
        .ofAdd (1, v) * .ofAdd (1, w) * .ofAdd (1, (0 : V3)) := by
      apply Multiplicative.ext
      apply Prod.ext
      · change (1 : ZMod 2) = 1 + 1 + 1
        rfl
      · change v + w = v + w + 0
        rw [add_zero]
    have himage : (.ofAdd (1, σ (v + w)) : Multiplicative (ZMod 2 × V3)) =
        .ofAdd (1, σ v) * .ofAdd (1, σ w) * .ofAdd (1, σ 0) := by
      apply hinj
      rw [map_mul, map_mul, ← hconj, ← hconj, ← hconj, ← hconj]
      rw [hcoords, map_mul, map_mul]
      group
    exact congrArg (fun v : Multiplicative (ZMod 2 × V3) => v.toAdd.2) himage
  let f : V3 → V3 := fun v => σ v - σ 0
  have hf0 : f 0 = 0 := sub_self _
  have hfadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    dsimp only [f]
    funext i
    change σ (v + w) i - σ 0 i = (σ v i - σ 0 i) + (σ w i - σ 0 i)
    rw [show σ (v + w) i = σ v i + σ w i + σ 0 i by
      exact congrFun (hsum v w) i]
    exact (by decide +kernel : ∀ a b c : ZMod 2, (a + b + c) - c = (a - c) + (b - c))
      (σ v i) (σ w i) (σ 0 i)
  let fH : V3 →+ V3 := { toFun := f, map_zero' := hf0, map_add' := hfadd }
  let lin : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) := fH.toZModLinearMap 2
  have hfbij : Function.Bijective lin := by
    constructor
    · intro v w h
      change σ v - σ 0 = σ w - σ 0 at h
      exact σ.injective (sub_left_injective h)
    · intro w
      refine ⟨σ.symm (w + σ 0), ?_⟩
      change σ (σ.symm (w + σ 0)) - σ 0 = w
      rw [σ.apply_symm_apply, add_sub_cancel_right]
  let A := LinearEquiv.ofBijective lin hfbij
  refine ⟨σ 0, A, fun v => ?_⟩
  change σ v = σ 0 + (σ v - σ 0)
  abel

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight

theorem eq_affinePerms_of_two_seven_generators
    (K : Subgroup (Equiv.Perm V3)) (hK : K ≤ affinePerms V3)
    (s : Fin 3 → Equiv.Perm V3) (hs : ∀ k, s k ∈ K) (hs0 : ∀ k, s k 0 = 0)
    (hs2 : s 0 ^ 2 = 1) (hs1 : s 0 ≠ 1)
    (hs7 : (s 2 * s 1 * s 0) ^ 7 = 1) (hs71 : s 2 * s 1 * s 0 ≠ 1)
    (t : Equiv.Perm V3) (ht : t ∈ K) (ht0 : t 0 ≠ 0) : K = affinePerms V3 := by
  classical
  let H := K ⊓ MulAction.stabilizer (Equiv.Perm V3) (0 : V3)
  let α : H →* affinePerms V3 := H.subtype.codRestrict _ (fun h => hK h.2.1)
  let f : H →* GL (Fin 3) (ZMod 2) :=
    glLin.symm.toMonoidHom.comp (affineLinearPartHom.comp α)
  have hf : ∀ (h : H) v, glLin (f h) v = (h : Equiv.Perm V3) v := by
    intro h v
    change glLin (glLin.symm (affineLinearPartHom (α h))) v = _
    rw [glLin.apply_symm_apply, affineLinearPartHom_apply]
    have hzero : (h : Equiv.Perm V3) 0 = 0 := MulAction.mem_stabilizer_iff.mp h.2.2
    change (h : Equiv.Perm V3) v - (h : Equiv.Perm V3) 0 = _
    rw [hzero, sub_zero]
  have hfinj : Function.Injective f := by
    intro h j hh
    apply Subtype.ext
    apply Equiv.ext
    intro v
    rw [← hf h v, ← hf j v, hh]
  let ss : Fin 3 → H := fun k => ⟨s k, hs k, MulAction.mem_stabilizer_iff.mpr (hs0 k)⟩
  have ha2 : ss 0 ^ 2 = 1 := Subtype.ext hs2
  have ha1 : ss 0 ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hb7 : (ss 2 * ss 1 * ss 0) ^ 7 = 1 := Subtype.ext hs7
  have hb1 : ss 2 * ss 1 * ss 0 ≠ 1 := fun h => hs71 (congrArg Subtype.val h)
  have hfsurj : Function.Surjective f := surjective_GL32_of_two_seven f
    (ss 0) (ss 2 * ss 1 * ss 0)
    (by rw [← map_pow, ha2, map_one])
    (fun h => ha1 (hfinj (h.trans (map_one f).symm)))
    (by rw [← map_pow, hb7, map_one])
    (fun h => hb1 (hfinj (h.trans (map_one f).symm)))
  have hstab : H = linearPerms V3 := by
    ext σ
    constructor
    · intro hσ
      refine ⟨glLin (f ⟨σ, hσ⟩), fun v => (hf ⟨σ, hσ⟩ v).symm⟩
    · rintro ⟨A, hA⟩
      obtain ⟨h, hh⟩ := hfsurj (glLin.symm A)
      have heq : (h : Equiv.Perm V3) = σ := by
        apply Equiv.ext
        intro v
        rw [← hf h v, hh, glLin.apply_symm_apply, hA]
      exact heq ▸ h.2
  have hlin : ∀ A : V3 ≃ₗ[ZMod 2] V3, A.toEquiv ∈ K := by
    intro A
    have hA : A.toEquiv ∈ linearPerms V3 := ⟨A, fun _ => rfl⟩
    rw [← hstab] at hA
    exact hA.1
  have hdim : Module.finrank (ZMod 2) V3 = 3 := Module.finrank_fin_fun (ZMod 2)
  have h0 : ∀ w : V3, ∃ k ∈ K, k 0 = w := by
    intro w
    by_cases hw : w = 0
    · exact ⟨1, one_mem _, by simpa only [Equiv.Perm.one_apply] using hw.symm⟩
    · obtain ⟨A, hA⟩ := BinaryAffineEight.exists_linearEquiv_apply_eq hdim ht0 hw
      refine ⟨A.toEquiv * t, mul_mem (hlin A) ht, ?_⟩
      exact hA
  have htrans : ∀ v w : V3, ∃ k ∈ K, k v = w := by
    intro v w
    obtain ⟨a, ha, hav⟩ := h0 v
    obtain ⟨b, hb, hbw⟩ := h0 w
    refine ⟨b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
    rw [Equiv.Perm.mul_apply, ← hav]
    change b (a.symm (a 0)) = w
    rw [a.symm_apply_apply, hbw]
  exact (binary_affine_eight_full_linear_point_stabilizer hdim K htrans hstab).1

theorem exists_twoKernel_quotient_GL32_affine :
    ∃ (N : Subgroup (affinePerms V3)) (_ : N.Normal), IsPGroup 2 N ∧
      Nat.card N = 8 ∧ Nonempty (affinePerms V3 ⧸ N ≃* GL (Fin 3) (ZMod 2)) := by
  let f : affinePerms V3 →* GL (Fin 3) (ZMod 2) :=
    glLin.symm.toMonoidHom.comp affineLinearPartHom
  have hf : ∀ (a : affinePerms V3) v,
      glLin (f a) v = (a : Equiv.Perm V3) v - (a : Equiv.Perm V3) 0 := by
    intro a v
    change glLin (glLin.symm (affineLinearPartHom a)) v = _
    rw [glLin.apply_symm_apply, affineLinearPartHom_apply]
  have hfsurj : Function.Surjective f := by
    intro M
    let a : affinePerms V3 := ⟨(glLin M).toEquiv, 0, glLin M, fun _ => (zero_add _).symm⟩
    refine ⟨a, ?_⟩
    apply glLin.injective
    apply LinearEquiv.ext
    intro v
    rw [hf]
    change glLin M v - glLin M 0 = glLin M v
    rw [map_zero, sub_zero]
  have hker : f.ker = (translationPerms V3).subgroupOf (affinePerms V3) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro ha
      refine ⟨(a : Equiv.Perm V3) 0, fun v => ?_⟩
      have h := hf a v
      rw [ha, map_one] at h
      change v = (a : Equiv.Perm V3) v - (a : Equiv.Perm V3) 0 at h
      exact eq_add_of_sub_eq' h.symm
    · rintro ⟨b, hb⟩
      apply glLin.injective
      apply LinearEquiv.ext
      intro v
      rw [hf, hb, hb, add_zero, add_sub_cancel_left, map_one]
      rfl
  have h2 : IsPGroup 2 f.ker := by
    intro a
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro v
    have ha : (a : affinePerms V3) ∈ (translationPerms V3).subgroupOf (affinePerms V3) :=
      hker ▸ a.2
    obtain ⟨b, hb⟩ := ha
    change ((affinePerms V3).subtype (a : affinePerms V3))
      (((affinePerms V3).subtype (a : affinePerms V3)) v) = v
    rw [hb, hb, ← add_assoc]
    have hself : b + b = 0 := funext (fun i => CharTwo.add_self_eq_zero (b i))
    rw [hself, zero_add]
  have hTK : translationPerms V3 ≤ affinePerms V3 := by
    rintro σ ⟨b, hb⟩
    exact ⟨b, LinearEquiv.refl _ _, hb⟩
  have hcard : Nat.card f.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]
    let e : translationPerms V3 ≃ V3 :=
      { toFun := fun σ => σ.1 0
        invFun := fun b => ⟨Equiv.addLeft b, b, fun _ => rfl⟩
        left_inv := by
          rintro ⟨σ, b, hb⟩
          apply Subtype.ext
          apply Equiv.ext
          intro v
          change σ 0 + v = σ v
          rw [hb, hb, add_zero]
        right_inv := fun b => add_zero b }
    rw [Nat.card_congr e]
    change Nat.card (Fin 3 → ZMod 2) = 8
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rfl
  exact ⟨f.ker, inferInstance, h2, hcard, ⟨QuotientGroup.quotientKerEquivOfSurjective f hfsurj⟩⟩

end AbstractAction

theorem nonempty_equiv_GL32_of_e7_coordinate_frame
    {F X : Type} [Field F] [Finite F] [Group X] [Finite X]
    (hodd : Odd (Nat.card F)) (hF : ringChar F ≠ 2)
    (ψ : adjointGroup .E7 F →* X) (hψ : Function.Injective ψ) :
    let Δ := Set.range (fun i : Fin 7 => (rho F frameE7 i).range.map ψ)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* GL (Fin 3) (ZMod 2)) := by
  classical
  let Δ := Set.range (fun i : Fin 7 => (rho F frameE7 i).range.map ψ)
  let R : Fin 7 → Subgroup X := fun i => (rho F frameE7 i).range.map ψ
  let z : Multiplicative V3 →* X := ψ.comp (e7BinaryAdj F)
  have hinj : Function.Injective z := hψ.comp (e7BinaryAdj_injective hF)
  have huniq : ∀ i, IsUniqueInvolution (R i) (z (.ofAdd (e7Label i))) := by
    intro i
    have hu := CFSG.ClassicalInvolution.G2D4Models.isUniqueInvolution_range_sl2
      (φ := ψ.comp (rho F frameE7 i)) hodd (hψ.comp (rho_injective frameE7 i))
    simpa only [R, MonoidHom.range_comp, z, MonoidHom.comp_apply, e7BinaryAdj_frame] using hu
  have hRinj : Function.Injective R := by
    intro i j hij
    have hu := huniq i
    rw [hij] at hu
    have hz := hu.eq (huniq j)
    have hl := congrArg Multiplicative.toAdd (hinj hz)
    exact e7LabelEquiv.injective (Subtype.ext hl)
  let e : Fin 7 ≃ Δ := Equiv.ofBijective (fun i => ⟨R i, ⟨i, rfl⟩⟩)
    ⟨fun i j h => hRinj (congrArg Subtype.val h), by rintro ⟨_, i, rfl⟩; exact ⟨i, rfl⟩⟩
  apply nonempty_equiv_GL32_of_e7_binary_frame e z hinj (fun i => huniq i)
  intro k
  let x := nrep .E7 F (e7ActionWeyl k)
  refine ⟨ψ x, fun i => ?_⟩
  change conjSub (ψ x) ((rho F frameE7 i).range.map ψ) =
    (rho F frameE7 (e7ActionPerm k i)).range.map ψ
  rw [conjSub, ← Subgroup.map_map_conj, ← conjSub, e7Action_conj_rho]

theorem nonempty_equiv_affine_of_e8_coordinate_frame
    {F X : Type} [Field F] [Finite F] [Group X] [Finite X]
    (hodd : Odd (Nat.card F)) (hF : ringChar F ≠ 2)
    (ψ : adjointGroup .E8 F →* X) (hψ : Function.Injective ψ) :
    let Δ := Set.range (fun i : Fin 8 => (rho F frameE8 i).range.map ψ)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃*
      CFSG.LocalAnalysis.ComponentInitial.affinePerms V3) := by
  classical
  let Δ := Set.range (fun i : Fin 8 => (rho F frameE8 i).range.map ψ)
  let R : Fin 8 → Subgroup X := fun i => (rho F frameE8 i).range.map ψ
  let z : Multiplicative (ZMod 2 × V3) →* X := ψ.comp (e8BinaryAdj F)
  have hinj : Function.Injective z := hψ.comp (e8BinaryAdj_injective hF)
  have huniq : ∀ i, IsUniqueInvolution (R i) (z (.ofAdd (1, e8Label i))) := by
    intro i
    have hu := CFSG.ClassicalInvolution.G2D4Models.isUniqueInvolution_range_sl2
      (φ := ψ.comp (rho F frameE8 i)) hodd (hψ.comp (rho_injective frameE8 i))
    simpa only [R, MonoidHom.range_comp, z, MonoidHom.comp_apply, e8BinaryAdj_frame] using hu
  have hRinj : Function.Injective R := by
    intro i j hij
    have hu := huniq i
    rw [hij] at hu
    have hz := hu.eq (huniq j)
    have hl := congrArg (fun v : Multiplicative (ZMod 2 × V3) => v.toAdd.2) (hinj hz)
    exact e8LabelEquiv.injective hl
  let e : Fin 8 ≃ Δ := Equiv.ofBijective (fun i => ⟨R i, ⟨i, rfl⟩⟩)
    ⟨fun i j h => hRinj (congrArg Subtype.val h), by rintro ⟨_, i, rfl⟩; exact ⟨i, rfl⟩⟩
  let ev : V3 ≃ Δ := e8LabelEquiv.symm.trans e
  let ρ := conjPermHom (le_refl (conjSetStab Δ))
  let φ : ρ.range →* Equiv.Perm V3 := ev.symm.permCongrHom.toMonoidHom.comp ρ.range.subtype
  have hφinj : Function.Injective φ := ev.symm.permCongrHom.injective.comp Subtype.val_injective
  have hφaff : ∀ a : ρ.range, φ a ∈ CFSG.LocalAnalysis.ComponentInitial.affinePerms V3 := by
    apply conjPermHom_mem_affinePerms_of_binary_frame ev z hinj
    intro v
    have hlabel : e8Label (e8LabelEquiv.symm v) = v := e8LabelEquiv.apply_symm_apply v
    have hu := huniq (e8LabelEquiv.symm v)
    change IsUniqueInvolution (R (e8LabelEquiv.symm v)) (z (.ofAdd (1, v)))
    simpa only [hlabel] using hu
  have hmem : ∀ k : Fin 4, e.permCongrHom (e8ActionPerm k) ∈ ρ.range := by
    intro k
    apply mem_conjPermHom_range_of_indexed_conjugation e _
      (ψ (nrep .E8 F (e8ActionWeyl k)))
    intro i
    change conjSub (ψ (nrep .E8 F (e8ActionWeyl k))) ((rho F frameE8 i).range.map ψ) = _
    rw [conjSub, ← Subgroup.map_map_conj, ← conjSub, e8Action_conj_rho]
    rfl
  let c : Equiv.Perm (Fin 8) ≃* Equiv.Perm V3 := e8LabelEquiv.permCongrHom
  have himage : ∀ k : Fin 4, c (e8ActionPerm k) ∈ φ.range := by
    intro k
    refine ⟨⟨e.permCongrHom (e8ActionPerm k), hmem k⟩, ?_⟩
    apply Equiv.ext
    intro v
    change e8LabelEquiv (e.symm (e.permCongrHom (e8ActionPerm k) (e (e8LabelEquiv.symm v)))) = _
    simp only [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  let ss : Fin 3 → Equiv.Perm V3 := fun k => c (e8ActionPerm k.castSucc)
  have hs0 : ∀ k, ss k 0 = 0 := by
    intro k
    change e8LabelEquiv (e8ActionPerm k.castSucc (e8LabelEquiv.symm 0)) = 0
    have hzero : e8LabelEquiv.symm 0 = 0 := e8LabelEquiv.injective (by rw [e8LabelEquiv.apply_symm_apply]; exact (show e8LabelEquiv 0 = 0 by decide +kernel).symm)
    rw [hzero]
    change e8Label (e8ActionIndex k.castSucc 0) = 0
    rw [e8ActionIndex_fix_zero]
    decide +kernel
  have hs2 : ss 0 ^ 2 = 1 := by
    change c (e8ActionPerm 0) ^ 2 = 1
    rw [← map_pow, e8ActionPerm_sq, map_one]
  have hs1 : ss 0 ≠ 1 := by
    intro h
    exact e8ActionPerm_zero_ne_one (c.injective (h.trans (map_one c).symm))
  have hs7 : (ss 2 * ss 1 * ss 0) ^ 7 = 1 := by
    change (c (e8ActionPerm 2) * c (e8ActionPerm 1) * c (e8ActionPerm 0)) ^ 7 = 1
    rw [← map_mul, ← map_mul, ← map_pow, e8ActionPerm_product_seven, map_one]
  have hs71 : ss 2 * ss 1 * ss 0 ≠ 1 := by
    intro h
    apply e8ActionPerm_product_ne_one
    apply c.injective
    change c (e8ActionPerm 2) * c (e8ActionPerm 1) * c (e8ActionPerm 0) = 1 at h
    simpa only [map_mul, map_one] using h
  have ht0 : c (e8ActionPerm 3) 0 ≠ 0 := by
    change e8Label (e8ActionIndex 3 (e8LabelEquiv.symm 0)) ≠ 0
    have hzero : e8LabelEquiv.symm 0 = 0 := e8LabelEquiv.injective (by rw [e8LabelEquiv.apply_symm_apply]; exact (show e8LabelEquiv 0 = 0 by decide +kernel).symm)
    rw [hzero]
    decide +kernel
  have hrange : φ.range = CFSG.LocalAnalysis.ComponentInitial.affinePerms V3 :=
    eq_affinePerms_of_two_seven_generators φ.range
      (by rintro _ ⟨a, rfl⟩; exact hφaff a)
      ss (fun k => himage k.castSucc) hs0 hs2 hs1 hs7 hs71
      (c (e8ActionPerm 3)) (himage 3) ht0
  exact ⟨(MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)⟩

section NativeModels

open CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight
open CFSG.ClassicalInvolution.ModelFacts (stdRankOne e7AdjDatum)
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

theorem exists_equiv_of_central_surjections
    {U A X : Type} [Group U] [Group A] [Group X]
    (π : U →* A) (hπ : Function.Surjective π) (hπker : π.ker ≤ center U)
    (ψ : U →* X) (hψ : Function.Surjective ψ) (hψker : ψ.ker ≤ center U)
    (hA : center A = ⊥) (hX : center X = ⊥) :
    ∃ e : A ≃* X, ∀ u : U, e (π u) = ψ u := by
  have hker : ∀ {H : Type} [Group H] (f : U →* H), Function.Surjective f →
      f.ker ≤ center U → center H = ⊥ → f.ker = center U := by
    intro H _ f hf hkc hZ
    refine le_antisymm hkc ?_
    intro u hu
    have hz := Subgroup.map_center_le_center hf (show f u ∈ (center U).map f from ⟨u, hu, rfl⟩)
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have heq : π.ker = ψ.ker := (hker π hπ hπker hA).trans (hker ψ hψ hψker hX).symm
  let ep := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let es := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let e : A ≃* X := ep.symm.trans ((QuotientGroup.quotientMulEquivOfEq heq).trans es)
  refine ⟨e, fun u => ?_⟩
  have hp : ep (u : U ⧸ π.ker) = π u := rfl
  have hs : es (u : U ⧸ ψ.ker) = ψ u := rfl
  change es ((QuotientGroup.quotientMulEquivOfEq heq) (ep.symm (π u))) = ψ u
  rw [← hp, ep.symm_apply_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact hs

theorem exists_full_adjoint_frame_funSet_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E7 0 p e) (hX : LieModel X .E7 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ ψ : adjointGroup .E7 (GaloisField p e) →* X, Function.Injective ψ ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun i : Fin 7 => (rho (GaloisField p e) frameE7 i).range.map ψ) := by
  obtain ⟨ψ₀, hψ₀, hker₀, hfull⟩ := exists_full_frame_funSet_e7 hp2 hadm hX P hK
  have hZ : center X = ⊥ := (fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) hK.1).1
  let F := GaloisField p e
  let π : (modelUniv .E7 0 p e hp.out).K →* adjointGroup .E7 F := e7Isogeny F
  have hπ : Function.Surjective π := e7Isogeny_surjective F
  have hπker : π.ker ≤ center (modelUniv .E7 0 p e hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center F
  obtain ⟨E, hE⟩ := exists_equiv_of_central_surjections π hπ hπker ψ₀ hψ₀ hker₀
    center_adjointGroup_eq_bot hZ
  let ψ := E.toMonoidHom
  have hhom : ψ.comp π = ψ₀ := by ext u; exact hE u
  refine ⟨ψ, E.injective, ?_⟩
  rw [hfull]
  congr 1
  funext i
  rw [← hhom, ← Subgroup.map_map]
  have hmap : (stdRankOne (modelUniv .E7 0 p e hp.out).D (frameE7Root i)).map π =
      stdRankOne (e7AdjDatum F) (frameE7Root i) := map_stdRankOne_e7_root
        (mem_rootFinset.mp (frameE7Root_mem i))
  rw [hmap, rho_range_eq_rootPair]
  congr 1
  ext r
  rw [mem_stdRankOne_e7_iff' (mem_rootFinset.mp (frameE7Root_mem i))]
  change (∃ A : SL2 F, (r : ModGL .E7 F) = rootSL2 .E7 F (frameE7Root i) A) ↔
    (r : ModGL .E7 F) ∈ rootRankOneGroup .E7 F (frameE7Root i)
  exact exists_congr fun A => eq_comm

theorem nonempty_equiv_GL32_funSet_e7
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E7 0 p e) (hX : LieModel X .E7 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* GL (Fin 3) (ZMod 2)) := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  obtain ⟨ψ, hψ, hfull⟩ := exists_full_adjoint_frame_funSet_e7 hp2 hadm hX P hK
  rw [hfull]
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (NeZero.ne e)]
    exact (hp.out.odd_of_ne_two hp2).pow
  have hF : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  exact nonempty_equiv_GL32_of_e7_coordinate_frame hodd hF ψ hψ

theorem exists_full_adjoint_frame_funSet_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    ∃ ψ : adjointGroup .E8 (GaloisField p e) →* X, Function.Injective ψ ∧
      F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
        Set.range (fun i : Fin 8 => (rho (GaloisField p e) frameE8 i).range.map ψ) := by
  obtain ⟨ψ₀, hψ₀, hker₀, hfull⟩ := exists_full_frame_funSet_e8 hp2 hadm hX P hK
  let ψ : adjointGroup .E8 (GaloisField p e) →* X := ψ₀
  have hψker : ψ.ker ≤ center (adjointGroup .E8 (GaloisField p e)) := hker₀
  have hψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp
    (le_bot_iff.mp (hψker.trans (by rw [center_adjointGroup_eq_bot])))
  refine ⟨ψ, hψ, ?_⟩
  rw [hfull]
  congr 1
  funext i
  change (stdRankOne (e8Datum (GaloisField p e)) (frameE8Root i)).map ψ = _
  rw [rho_range_eq_rootPair]
  congr 1
  ext r
  rw [mem_stdRankOne_e8_iff' (mem_rootFinset.mp (frameE8Root_mem i))]
  change (∃ A : SL2 (GaloisField p e), (r : ModGL .E8 (GaloisField p e)) =
      rootSL2 .E8 (GaloisField p e) (frameE8Root i) A) ↔
    (r : ModGL .E8 (GaloisField p e)) ∈ rootRankOneGroup .E8 (GaloisField p e) (frameE8Root i)
  exact exists_congr fun A => eq_comm

theorem nonempty_equiv_affine_funSet_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃*
      CFSG.LocalAnalysis.ComponentInitial.affinePerms V3) := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  obtain ⟨ψ, hψ, hfull⟩ := exists_full_adjoint_frame_funSet_e8 hp2 hadm hX P hK
  rw [hfull]
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (NeZero.ne e)]
    exact (hp.out.odd_of_ne_two hp2).pow
  have hF : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  exact nonempty_equiv_affine_of_e8_coordinate_frame hodd hF ψ hψ

theorem exists_twoKernel_quotient_GL32_funSet_e8
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) (hX : LieModel X .E8 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let A := (conjPermHom (le_refl (conjSetStab Δ))).range
    ∃ (N : Subgroup A) (_ : N.Normal), IsPGroup 2 N ∧ Nat.card N = 8 ∧
      Nonempty (A ⧸ N ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨E⟩ := nonempty_equiv_affine_funSet_e8 hp2 hadm hX P hK
  obtain ⟨N, hN, hN2, hNcard, ⟨EN⟩⟩ := exists_twoKernel_quotient_GL32_affine
  let M := N.comap E.toMonoidHom
  have hM : M.Normal := hN.comap E.toMonoidHom
  let f : M →* N := (E.toMonoidHom.comp M.subtype).codRestrict N fun a => a.2
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact E.injective (congrArg Subtype.val hab)
    · intro n
      exact ⟨⟨E.symm n, by change E (E.symm n) ∈ N; rw [E.apply_symm_apply]; exact n.2⟩,
        Subtype.ext (E.apply_symm_apply n)⟩
  let EM := MulEquiv.ofBijective f hf
  have hcard : Nat.card M = 8 := (Nat.card_congr EM.toEquiv).trans hNcard
  have hpgrp : IsPGroup 2 M := hN2.of_injective f hf.1
  let : N.Normal := hN
  let : M.Normal := hM
  have hmap : M.map E.toMonoidHom = N := Subgroup.map_comap_eq_self_of_surjective E.surjective N
  exact ⟨M, hM, hpgrp, hcard, ⟨(QuotientGroup.congr M N E hmap).trans EN⟩⟩

theorem funSet_action_twoKernel_quotient_of_four_lt_exceptional
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (_hA1 : ¬ (t = .PSL ∧ n = 2)) (_hRee : t ≠ .twistedG2)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    (_hnotTwo : ¬ FunTwoType t n)
    (_hlarge : 4 < (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard) :
    let Δ := F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)
    let ρ := conjPermHom (le_refl (conjSetStab Δ))
    (∃ (m : ℕ) (N : Subgroup ρ.range) (_ : N.Normal),
      IsPGroup 2 N ∧ Nonempty (ρ.range ⧸ N ≃* Equiv.Perm (Fin m))) ∨
      (∃ (N : Subgroup ρ.range) (_ : N.Normal),
        IsPGroup 2 N ∧ IsSimpleGroup (ρ.range ⧸ N) ∧ Nat.card (ρ.range ⧸ N) = 168) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  rcases ht with rfl | rfl
  · have hn : n = 0 := hadm.2.2
    subst n
    obtain ⟨E⟩ := nonempty_equiv_GL32_funSet_e7 hp2 hadm hX P hK
    let Q := QuotientGroup.quotientBot.trans E
    exact Or.inr ⟨⊥, inferInstance, IsPGroup.of_bot,
      Q.isSimpleGroup, (Nat.card_congr Q.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh⟩
  · have hn : n = 0 := hadm.2.2
    subst n
    obtain ⟨N, hN, h2, _, ⟨E⟩⟩ := exists_twoKernel_quotient_GL32_funSet_e8 hp2 hadm hX P hK
    let : N.Normal := hN
    exact Or.inr ⟨N, hN, h2, E.isSimpleGroup,
      (Nat.card_congr E.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh⟩

end NativeModels

end CFSG.LocalAnalysis.UniquenessCase.UC22.ExceptionalAction

namespace CFSG.LocalAnalysis.UniquenessCase.UC22
export ExceptionalAction (funSet_action_twoKernel_quotient_of_four_lt_exceptional)
end CFSG.LocalAnalysis.UniquenessCase.UC22
