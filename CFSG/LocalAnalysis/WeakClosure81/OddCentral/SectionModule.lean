module
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {Y : Type*} [Group Y]

@[expose] def conjOn (A : Subgroup Y) [hA : A.Normal] (y : Y) : A →* A where
  toFun a := ⟨y * a * y⁻¹, hA.conj_mem a a.2 y⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

theorem conjOn_apply (A : Subgroup Y) [A.Normal] (y : Y) (a : A) :
    ((conjOn A y a : A) : Y) = y * a * y⁻¹ := rfl

@[expose] def secCommGroup (A B : Subgroup Y) [B.Normal]
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) : CommGroup (A ⧸ B.subgroupOf A) :=
  { (inferInstance : Group (A ⧸ B.subgroupOf A)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have := hab _ (A.inv_mem b.2) _ (A.inv_mem a.2)
      simpa [mul_assoc] using this }

theorem map_conjOn_le (A B : Subgroup Y) [A.Normal] [hB : B.Normal] (y : Y) :
    B.subgroupOf A ≤ (B.subgroupOf A).comap (conjOn A y) := fun b hb => by
  rw [mem_comap, mem_subgroupOf, conjOn_apply]
  exact hB.conj_mem _ hb y

@[expose] def secAct (A B : Subgroup Y) [A.Normal] [B.Normal] :
    DistribMulAction Y (Additive (A ⧸ B.subgroupOf A)) where
  smul y m := Additive.ofMul (QuotientGroup.map (B.subgroupOf A) (B.subgroupOf A) (conjOn A y)
    (map_conjOn_le A B y) m.toMul)
  one_smul m := by
    induction m using Additive.rec with
    | ofMul m =>
    induction m using QuotientGroup.induction_on with
    | H a =>
    show Additive.ofMul (QuotientGroup.map _ _ _ _ (QuotientGroup.mk a)) = _
    rw [QuotientGroup.map_mk]
    congr 2
    ext; simp [conjOn_apply]
  mul_smul y₁ y₂ m := by
    induction m using Additive.rec with
    | ofMul m =>
    induction m using QuotientGroup.induction_on with
    | H a =>
    show Additive.ofMul (QuotientGroup.map _ _ _ _ (QuotientGroup.mk a)) =
      Additive.ofMul (QuotientGroup.map _ _ _ _
        (Additive.toMul (Additive.ofMul (QuotientGroup.map _ _ _ _ (QuotientGroup.mk a)))))
    simp only [QuotientGroup.map_mk, toMul_ofMul]
    congr 2
    ext; simp only [conjOn_apply]; group
  smul_zero y := by
    show Additive.ofMul (QuotientGroup.map _ _ _ _ 1) = Additive.ofMul 1
    rw [map_one]
  smul_add y m₁ m₂ :=
    congrArg Additive.ofMul (map_mul (QuotientGroup.map (B.subgroupOf A) (B.subgroupOf A)
      (conjOn A y) (map_conjOn_le A B y)) m₁.toMul m₂.toMul)

theorem secAct_mk (A B : Subgroup Y) [A.Normal] [B.Normal] (y : Y) (a : A) :
    (secAct A B).smul y (Additive.ofMul (QuotientGroup.mk a : A ⧸ B.subgroupOf A)) =
      Additive.ofMul (QuotientGroup.mk (conjOn A y a) : A ⧸ B.subgroupOf A) := by
  show Additive.ofMul (QuotientGroup.map _ _ _ _ (QuotientGroup.mk a)) = _
  rw [QuotientGroup.map_mk]

theorem mk_eq_mk_iff (A B : Subgroup Y) [hB : B.Normal] (a a' : A) :
    (QuotientGroup.mk a : A ⧸ B.subgroupOf A) = QuotientGroup.mk a' ↔
      (a' : Y) * (a : Y)⁻¹ ∈ B := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro h
    have := hB.conj_mem _ h a
    simpa [mul_assoc] using this
  · intro h
    have := hB.conj_mem _ h (a : Y)⁻¹
    simpa [mul_assoc] using this

theorem secAct_mk_eq_iff (A B : Subgroup Y) [A.Normal] [hB : B.Normal] (y : Y) (a : A) :
    (secAct A B).smul y (Additive.ofMul (QuotientGroup.mk a : A ⧸ B.subgroupOf A)) =
      Additive.ofMul (QuotientGroup.mk a) ↔ y * a * y⁻¹ * (a : Y)⁻¹ ∈ B := by
  rw [secAct_mk, EmbeddingLike.apply_eq_iff_eq, mk_eq_mk_iff, conjOn_apply, ← B.inv_mem_iff,
    show ((a : Y) * (y * a * y⁻¹)⁻¹)⁻¹ = y * a * y⁻¹ * (a : Y)⁻¹ by group]

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

