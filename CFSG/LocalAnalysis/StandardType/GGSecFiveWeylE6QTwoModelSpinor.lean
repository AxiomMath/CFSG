module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelAux

open Module
open CFSG.StandardType
open CFSG.StandardType.NoOffRest
open CFSG.StandardType.TableBExc.E6Three
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley

public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

abbrev e6ModelO90Sub : Type := {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90}

theorem e6ModelO90_adAct_mem (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ e6ModelO90) :
    adAct .E6 3 w x ∈ e6ModelO90 := by
  rw [e6ModelO90, Finset.mem_filter] at hx ⊢
  obtain ⟨-, hx0, hxne, hxnorm⟩ := hx
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · exact (NoOffRest.kDot_adAct w x).trans hx0
  · intro h
    apply hxne
    have h' := congrArg (adAct .E6 3 w⁻¹) h
    rwa [← TableBExc.E6Three.adAct_mul, inv_mul_cancel, TableBExc.E6Three.adAct_one] at h'
  · rw [e6ModelForm_adAct hP hV hB hα w hx0 hx0]
    exact hxnorm

@[expose] noncomputable def e6ModelActO90 (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) (x : e6ModelO90Sub) : e6ModelO90Sub :=
  ⟨adAct .E6 3 w x.1, e6ModelO90_adAct_mem hP hV hB hα w x.2⟩

theorem e6ModelActO90_apply (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) (x : e6ModelO90Sub) :
    (e6ModelActO90 hP hV hB hα w x).1 = adAct .E6 3 w x.1 := rfl

@[expose] noncomputable def e6ModelPermO90 (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) : Equiv.Perm e6ModelO90Sub where
  toFun := e6ModelActO90 hP hV hB hα w
  invFun := e6ModelActO90 hP hV hB hα w⁻¹
  left_inv := by
    intro x
    apply Subtype.ext
    rw [e6ModelActO90_apply, e6ModelActO90_apply, ← TableBExc.E6Three.adAct_mul,
      inv_mul_cancel, TableBExc.E6Three.adAct_one]
  right_inv := by
    intro x
    apply Subtype.ext
    rw [e6ModelActO90_apply, e6ModelActO90_apply, ← TableBExc.E6Three.adAct_mul,
      mul_inv_cancel, TableBExc.E6Three.adAct_one]

theorem e6ModelPermO90_apply (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) (x : e6ModelO90Sub) :
    ((e6ModelPermO90 hP hV hB hα w) x).1 = adAct .E6 3 w x.1 := rfl

private theorem e6ModelPermO90_one (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2) :
    e6ModelPermO90 hP hV hB hα 1 = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [e6ModelPermO90_apply, TableBExc.E6Three.adAct_one]
  rfl

private theorem e6ModelPermO90_mul (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w₁ w₂ : WeylGroup .E6) :
    e6ModelPermO90 hP hV hB hα (w₁ * w₂) =
      e6ModelPermO90 hP hV hB hα w₁ * e6ModelPermO90 hP hV hB hα w₂ := by
  apply Equiv.ext
  intro x
  rw [Equiv.Perm.mul_apply]
  apply Subtype.ext
  rw [e6ModelPermO90_apply, e6ModelPermO90_apply, e6ModelPermO90_apply,
    TableBExc.E6Three.adAct_mul]

private theorem e6ModelO90Sub_card : Fintype.card e6ModelO90Sub = 90 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_finsetCard, e6ModelO90_card]

noncomputable def e6ModelFixedEquiv (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (i : Fin Tag.E6.rank) :
    Function.fixedPoints (e6ModelPermO90 hP hV hB hα (simple .E6 i)) ≃
      {y : Fin Tag.E6.rank → ZMod 3 // y ∈ e6ModelO90 ∧ y i = 0} where
  toFun x := by
    have hx' : adAct .E6 3 (simple .E6 i) x.1.1 = x.1.1 := by
      have h := congrArg Subtype.val x.2
      rwa [e6ModelPermO90_apply] at h
    rw [TableBExc.E6Three.adAct_simple] at hx'
    exact ⟨x.1.1, x.1.2, (adRefl_fixed_iff i x.1.1).mp hx'⟩
  invFun y := by
    refine ⟨⟨y.1, y.2.1⟩, ?_⟩
    apply Subtype.ext
    rw [e6ModelPermO90_apply, TableBExc.E6Three.adAct_simple]
    exact (adRefl_fixed_iff i y.1).mpr y.2.2
  left_inv x := rfl
  right_inv y := rfl

private theorem e6ModelSign_simple (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (i : Fin Tag.E6.rank) :
    Equiv.Perm.sign (e6ModelPermO90 hP hV hB hα (simple .E6 i)) = 1 := by
  have hfixed : Fintype.card (Function.fixedPoints
      (e6ModelPermO90 hP hV hB hα (simple .E6 i))) = 30 := by
    rw [← Nat.card_eq_fintype_card]
    calc Nat.card (Function.fixedPoints (e6ModelPermO90 hP hV hB hα (simple .E6 i)))
        = Nat.card {y : Fin Tag.E6.rank → ZMod 3 // y ∈ e6ModelO90 ∧ y i = 0} :=
          Nat.card_congr (e6ModelFixedEquiv hP hV hB hα i)
      _ = (e6ModelO90.filter fun y => y i = 0).card := by
          rw [Nat.subtype_card (e6ModelO90.filter fun y => y i = 0)]
          intro y
          simp [Finset.mem_filter]
      _ = 30 := e6ModelO90_fixed_card i
  have hsq : (e6ModelPermO90 hP hV hB hα (simple .E6 i)) ^ 2 = 1 := by
    rw [pow_two, ← e6ModelPermO90_mul, CoxeterSystem.simple_mul_simple_self,
      e6ModelPermO90_one]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hfixed, e6ModelO90Sub_card]
  decide

private theorem e6ModelSign (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) :
    Equiv.Perm.sign (e6ModelPermO90 hP hV hB hα w) = 1 := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective w
  induction ω with
  | nil =>
      rw [CoxeterSystem.wordProd_nil, e6ModelPermO90_one]
      simp
  | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, e6ModelPermO90_mul, Equiv.Perm.sign_mul,
        e6ModelSign_simple hP hV hB hα i, ih, one_mul]

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

private theorem e6ModelForm_comm (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x y : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) (hy : y ∈ hypE6) :
    e6ModelForm x y = e6ModelForm y x := by
  obtain ⟨a, ha⟩ := (e6ModelCoord hP hV).bijective.2 ⟨x, show x ∈ e6ModelHyp from hx⟩
  obtain ⟨b, hb⟩ := (e6ModelCoord hP hV).bijective.2 ⟨y, show y ∈ e6ModelHyp from hy⟩
  have ha' : (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3) = x := by rw [ha]
  have hb' : (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3) = y := by rw [hb]
  rw [← ha', ← hb', e6ModelForm_e6Coord hP hV hB a b,
    e6ModelForm_e6Coord hP hV hB b a, bilinForm_symm hP hV hB a b]

@[expose] def e6ModelReflMap (a : Fin Tag.E6.rank → ZMod 3)
    (ha : e6ModelForm a a = 2) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 := x - e6ModelForm a x • a

theorem e6ModelReflMap_involutive (a : Fin Tag.E6.rank → ZMod 3)
    (ha : e6ModelForm a a = 2) (x : Fin Tag.E6.rank → ZMod 3) :
    e6ModelReflMap a ha (e6ModelReflMap a ha x) = x := by
  simp only [e6ModelReflMap]
  rw [e6ModelForm_sub_right, e6ModelForm_smul_right, ha]
  module

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelReflMap_mem_O90 (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {a x : Fin Tag.E6.rank → ZMod 3} (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6)
    (hx : x ∈ e6ModelO90) :
    e6ModelReflMap a ha x ∈ e6ModelO90 := by
  rw [e6ModelO90, Finset.mem_filter] at hx ⊢
  obtain ⟨-, hx0, hxne, hxnorm⟩ := hx
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · rw [e6ModelReflMap, NoOffRest.kDotP_sub, NoOffRest.kDotP_smul, hx0, ha0, mul_zero]
    exact sub_self 0
  · intro h0
    have hinv := e6ModelReflMap_involutive a ha x
    rw [h0] at hinv
    have hzero : e6ModelReflMap a ha 0 = 0 := by
      rw [e6ModelReflMap, e6ModelForm_zero_right]
      simp only [zero_smul]
      exact sub_self 0
    rw [hzero] at hinv
    exact hxne hinv.symm
  · rw [e6ModelReflMap]
    have hcomm : e6ModelForm x a = e6ModelForm a x :=
      e6ModelForm_comm hP hV hB hα hx0 ha0
    simp only [e6ModelForm_sub_left, e6ModelForm_sub_right, e6ModelForm_smul_left,
      e6ModelForm_smul_right, hcomm, ha]
    rw [hxnorm]
    ring

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] noncomputable def e6ModelReflPermO90
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (a : Fin Tag.E6.rank → ZMod 3) (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6) :
    Equiv.Perm e6ModelO90Sub where
  toFun x :=
    ⟨e6ModelReflMap a ha x.1, e6ModelReflMap_mem_O90 hP hV hB hα ha ha0 x.2⟩
  invFun x :=
    ⟨e6ModelReflMap a ha x.1, e6ModelReflMap_mem_O90 hP hV hB hα ha ha0 x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e6ModelReflMap_involutive a ha x.1
  right_inv x := by
    apply Subtype.ext
    exact e6ModelReflMap_involutive a ha x.1

theorem e6ModelReflPermO90_apply
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (a : Fin Tag.E6.rank → ZMod 3) (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6)
    (x : e6ModelO90Sub) :
    ((e6ModelReflPermO90 hP hV hB hα a ha ha0) x).1 = e6ModelReflMap a ha x.1 := rfl

noncomputable def e6ModelReflFixedEquiv
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (a : Fin Tag.E6.rank → ZMod 3) (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6) :
    Function.fixedPoints (e6ModelReflPermO90 hP hV hB hα a ha ha0) ≃
      {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90 ∧ e6ModelForm a x = 0} where
  toFun x := by
    have hfix : e6ModelReflMap a ha x.1.1 = x.1.1 := by
      have h := congrArg Subtype.val x.2
      rwa [e6ModelReflPermO90_apply] at h
    rw [e6ModelReflMap] at hfix
    have hzero : e6ModelForm a x.1.1 • a = 0 := (sub_eq_self).mp hfix
    have hc : e6ModelForm a x.1.1 = 0 := by
      rcases smul_eq_zero.mp hzero with hc | haeq
      · exact hc
      · exfalso
        rw [haeq] at ha
        simp [e6ModelForm, E6Dep.bil6] at ha
        exact absurd ha (by decide)
    exact ⟨x.1.1, x.1.2, hc⟩
  invFun y := by
    refine ⟨⟨y.1, y.2.1⟩, ?_⟩
    apply Subtype.ext
    rw [e6ModelReflPermO90_apply]
    simp [e6ModelReflMap, y.2.2]
  left_inv x := rfl
  right_inv y := rfl

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelO90_mem_hypE6 {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ e6ModelO90) :
    x ∈ hypE6 := by
  rw [e6ModelO90, Finset.mem_filter] at hx
  rw [NoOffRest.mem_hypE6]
  simpa [e6ModelO90Pred] using hx.2.1

noncomputable def e6ModelPerpEquiv
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {a : Fin Tag.E6.rank → ZMod 3} (ha0 : a ∈ hypE6) {w : WeylGroup .E6}
    (hw : adAct .E6 3 w a = e6ModelBaseTwo) :
    {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90 ∧ e6ModelForm a x = 0} ≃
      {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90 ∧ e6ModelForm e6ModelBaseTwo x = 0} where
  toFun x := by
    refine ⟨adAct .E6 3 w x.1, e6ModelO90_adAct_mem hP hV hB hα w x.2.1, ?_⟩
    have h := e6ModelForm_adAct hP hV hB hα w ha0 (e6ModelO90_mem_hypE6 x.2.1)
    rw [hw] at h
    rw [h, x.2.2]
  invFun y := by
    refine ⟨adAct .E6 3 w⁻¹ y.1, e6ModelO90_adAct_mem hP hV hB hα w⁻¹ y.2.1, ?_⟩
    have h := e6ModelForm_adAct hP hV hB hα w ha0
      (e6ModelO90_mem_hypE6 (e6ModelO90_adAct_mem hP hV hB hα w⁻¹ y.2.1))
    rw [hw] at h
    rw [show adAct .E6 3 w (adAct .E6 3 w⁻¹ y.1) = y.1 by
      rw [← TableBExc.E6Three.adAct_mul, mul_inv_cancel, TableBExc.E6Three.adAct_one]] at h
    rw [← h, y.2.2]
  left_inv x := by
    apply Subtype.ext
    show adAct .E6 3 w⁻¹ (adAct .E6 3 w x.1) = x.1
    rw [← TableBExc.E6Three.adAct_mul, inv_mul_cancel, TableBExc.E6Three.adAct_one]
  right_inv y := by
    apply Subtype.ext
    show adAct .E6 3 w (adAct .E6 3 w⁻¹ y.1) = y.1
    rw [← TableBExc.E6Three.adAct_mul, mul_inv_cancel, TableBExc.E6Three.adAct_one]

private theorem e6ModelPerp_ncard (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {a : Fin Tag.E6.rank → ZMod 3} (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90 ∧ e6ModelForm a x = 0} = 24 := by
  have ha_ne : a ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp [e6ModelForm, E6Dep.bil6] at ha
    exact absurd ha (by decide)
  have hmem : e6ModelBaseTwo ∈ Set.range (fun u : WeylGroup .E6 => adAct .E6 3 u a) := by
    rw [ggE6IsoOrbit_eq ha0 ha_ne]
    refine ⟨e6ModelBaseTwo_mem_hypE6, e6ModelBaseTwo_ne_zero, ?_⟩
    simpa [e6ModelForm, E6Dep.norm6] using e6ModelForm_baseTwo.trans ha.symm
  obtain ⟨w, hw⟩ := hmem
  calc Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ e6ModelO90 ∧ e6ModelForm a x = 0}
      = Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          x ∈ e6ModelO90 ∧ e6ModelForm e6ModelBaseTwo x = 0} :=
        Nat.card_congr (e6ModelPerpEquiv hP hV hB hα ha0 hw)
    _ = (e6ModelO90.filter fun x => e6ModelForm e6ModelBaseTwo x = 0).card := by
        rw [Nat.subtype_card (e6ModelO90.filter fun x => e6ModelForm e6ModelBaseTwo x = 0)]
        intro x
        simp [Finset.mem_filter]
    _ = 24 := e6ModelO90_perp_baseTwo_card

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

private theorem e6ModelReflSign (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (a : Fin Tag.E6.rank → ZMod 3) (ha : e6ModelForm a a = 2) (ha0 : a ∈ hypE6) :
    Equiv.Perm.sign (e6ModelReflPermO90 hP hV hB hα a ha ha0) = -1 := by
  have hfixedA : Fintype.card (Function.fixedPoints
      (e6ModelReflPermO90 hP hV hB hα a ha ha0)) = 24 := by
    rw [← Nat.card_eq_fintype_card]
    calc Nat.card (Function.fixedPoints (e6ModelReflPermO90 hP hV hB hα a ha ha0))
        = Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
            x ∈ e6ModelO90 ∧ e6ModelForm a x = 0} :=
          Nat.card_congr (e6ModelReflFixedEquiv hP hV hB hα a ha ha0)
      _ = 24 := e6ModelPerp_ncard hP hV hB hα ha ha0
  have hsq : (e6ModelReflPermO90 hP hV hB hα a ha ha0) ^ 2 = 1 := by
    rw [pow_two]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact e6ModelReflMap_involutive a ha x.1
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hfixedA, e6ModelO90Sub_card]
  decide

end CFSG.StandardType.E6QTwo

end
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

private theorem e6ModelTwoMul (c : ZMod 3) : (2 : ZMod 3) * c = -c := by
  fin_cases c <;> decide

private theorem e6ModelNegAdd (c : ZMod 3) : -c + c = 0 := by
  fin_cases c <;> decide

private theorem e6ModelThreeMul (c : ZMod 3) : (2 : ZMod 3) * c + c = 0 := by
  fin_cases c <;> decide

theorem e6ModelNotMemRefl (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {v : V} (hv : B v v = 1) {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6ModelWeyl hα)
    (hformula : ∀ u, g u = u + B v u • v) : False := by
  obtain ⟨w, hw⟩ := exists_adAct_of_mem_e6Weyl hP hV hα hg
  let a : Fin Tag.E6.rank → ZMod 3 := e6ModelCoord hP hV v
  have ha0 : a ∈ hypE6 := by
    change (e6ModelCoord hP hV v).1 ∈ e6ModelHyp
    exact (e6ModelCoord hP hV v).2
  have ha : e6ModelForm a a = 2 := by
    have h := e6ModelForm_e6Coord hP hV hB v v
    rw [hv] at h
    simpa [a] using h
  have hperm : e6ModelPermO90 hP hV hB hα w =
      e6ModelReflPermO90 hP hV hB hα a ha ha0 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [e6ModelPermO90_apply, e6ModelReflPermO90_apply]
    let y : V := (e6ModelCoord hP hV).symm ⟨x.1, e6ModelO90_mem_hypE6 x.2⟩
    have hy : (e6ModelCoord hP hV y : Fin Tag.E6.rank → ZMod 3) = x.1 := by simp [y]
    have hgw := hw y
    have hgf := hformula y
    calc adAct .E6 3 w x.1
        = adAct .E6 3 w (e6ModelCoord hP hV y : Fin Tag.E6.rank → ZMod 3) := by rw [hy]
      _ = (e6ModelCoord hP hV (g y) : Fin Tag.E6.rank → ZMod 3) := hgw.symm
      _ = (e6ModelCoord hP hV (y + B v y • v) : Fin Tag.E6.rank → ZMod 3) := by rw [hgf]
      _ = (e6ModelCoord hP hV y : Fin Tag.E6.rank → ZMod 3) + B v y • a := by
            rw [map_add, map_smul]
            rfl
      _ = x.1 - e6ModelForm a x.1 • a := by
            rw [hy]
            have hB' : B v y = 2 * e6ModelForm a x.1 := by
              have h := e6ModelForm_e6Coord hP hV hB v y
              have hQ : e6ModelForm a x.1 = 2 * B v y := by
                rw [hy.symm]
                exact h
              calc B v y = B v y * 1 := by rw [mul_one]
                _ = B v y * ((2 : ZMod 3) * 2) := by
                    rw [show (2 : ZMod 3) * 2 = 1 by decide]
                _ = 2 * (2 * B v y) := by ring
                _ = 2 * e6ModelForm a x.1 := by rw [hQ]
            rw [hB']
            have h2 : (2 : ZMod 3) * e6ModelForm a x.1 = -e6ModelForm a x.1 :=
              e6ModelTwoMul (e6ModelForm a x.1)
            rw [h2, sub_eq_add_neg]
            congr 1
            rw [eq_neg_iff_add_eq_zero, ← add_smul]
            have h3 : (2 * e6ModelForm a x.1 + e6ModelForm a x.1 : ZMod 3) = 0 :=
              e6ModelThreeMul (e6ModelForm a x.1)
            rw [e6ModelNegAdd, zero_smul]
      _ = e6ModelReflMap a ha x.1 := by rw [e6ModelReflMap]
  have hsign := congrArg Equiv.Perm.sign hperm
  rw [e6ModelSign hP hV hB hα w, e6ModelReflSign hP hV hB hα a ha ha0] at hsign
  exact (units_ne_neg_self (1 : ℤˣ)) hsign

end CFSG.StandardType.E6QTwo

end
