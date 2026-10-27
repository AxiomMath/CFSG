module

public import CFSG.Monster.Spin.Pairing
public import CFSG.Foundations.Basic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Subgroup
open scoped commutatorElement

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem eq_one_of_ne_zero : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private theorem add_self_C'' (a : C) : a + a = 0 := add_self_C a

private theorem add_self_cocode' (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2) δ, two_eq_zero', zero_smul]

@[ext] structure SpinCoord where
  s : ZMod 2
  a : C
  δ : Cocode

namespace SpinCoord

instance : Mul SpinCoord := ⟨fun x y => ⟨x.s + y.s + pair y.a x.δ, x.a + y.a, x.δ + y.δ⟩⟩

instance : One SpinCoord := ⟨⟨0, 0, 0⟩⟩

instance : Inv SpinCoord := ⟨fun x => ⟨x.s + pair x.a x.δ, x.a, x.δ⟩⟩

@[simp] theorem mul_s (x y : SpinCoord) : (x * y).s = x.s + y.s + pair y.a x.δ := rfl

@[simp] theorem mul_a (x y : SpinCoord) : (x * y).a = x.a + y.a := rfl

@[simp] theorem mul_δ (x y : SpinCoord) : (x * y).δ = x.δ + y.δ := rfl

@[simp] theorem one_s : (1 : SpinCoord).s = 0 := rfl

@[simp] theorem one_a : (1 : SpinCoord).a = 0 := rfl

@[simp] theorem one_δ : (1 : SpinCoord).δ = 0 := rfl

@[simp] theorem inv_s (x : SpinCoord) : x⁻¹.s = x.s + pair x.a x.δ := rfl

@[simp] theorem inv_a (x : SpinCoord) : x⁻¹.a = x.a := rfl

@[simp] theorem inv_δ (x : SpinCoord) : x⁻¹.δ = x.δ := rfl

instance : Group SpinCoord where
  mul_assoc x y z := by
    ext
    · simp only [mul_s, mul_a, mul_δ, pair_add_left, pair_add_right]
      ring
    · simp only [mul_a, add_assoc]
    · simp only [mul_δ, add_assoc]
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_s, inv_s, inv_δ, one_s]
      linear_combination (x.s + pair x.a x.δ) * two_eq_zero'
    · simp only [mul_a, inv_a, one_a, add_self_C'']
    · simp only [mul_δ, inv_δ, one_δ, add_self_cocode']

@[expose] def equivProd : SpinCoord ≃ ZMod 2 × C × Cocode where
  toFun x := (x.s, x.a, x.δ)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard : Nat.card SpinCoord = 2 ^ 25 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_zmod, natCard_C,
    natCard_cocode]
  norm_num

@[expose] def z : SpinCoord := ⟨1, 0, 0⟩

theorem sq_eq (x : SpinCoord) : x ^ 2 = ⟨pair x.a x.δ, 0, 0⟩ := by
  rw [pow_two]
  ext
  · simp only [mul_s]
    linear_combination x.s * two_eq_zero'
  · simp only [mul_a, add_self_C'']
  · simp only [mul_δ, add_self_cocode']

theorem commutatorElement_eq (x y : SpinCoord) :
    ⁅x, y⁆ = ⟨pair x.a y.δ + pair y.a x.δ, 0, 0⟩ := by
  rw [commutatorElement_def]
  ext
  · simp only [mul_s, mul_δ, inv_s, inv_a, inv_δ, pair_add_right]
    linear_combination (x.s + y.s + pair y.a x.δ + pair x.a x.δ + pair y.a y.δ) * two_eq_zero'
  · simp only [mul_a, inv_a]
    rw [show x.a + y.a + x.a + y.a = (x.a + x.a) + (y.a + y.a) by abel, add_self_C'',
      add_self_C'', add_zero]
  · simp only [mul_δ, inv_δ]
    rw [show x.δ + y.δ + x.δ + y.δ = (x.δ + x.δ) + (y.δ + y.δ) by abel, add_self_cocode',
      add_self_cocode', add_zero]

theorem z_sq : z ^ 2 = 1 := by
  rw [sq_eq]
  ext <;> simp [z]

theorem z_ne_one : z ≠ 1 := fun h => by
  have := congrArg SpinCoord.s h
  simp [z] at this

theorem orderOf_z : orderOf z = 2 := orderOf_eq_prime z_sq z_ne_one

theorem mem_zpowers_z {x : SpinCoord} : x ∈ zpowers z ↔ x.a = 0 ∧ x.δ = 0 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    let K : Subgroup SpinCoord :=
      { carrier := {x | x.a = 0 ∧ x.δ = 0}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, mul_a, mul_δ] at *
          rw [hx.1, hx.2, hy.1, hy.2, add_zero, add_zero]
          exact ⟨rfl, rfl⟩
        one_mem' := ⟨rfl, rfl⟩
        inv_mem' := fun {x} hx => hx }
    have : z ^ k ∈ K := K.zpow_mem ⟨rfl, rfl⟩ k
    exact this
  · rintro ⟨ha, hδ⟩
    rcases zmod2_cases x.s with h | h
    · have : x = 1 := SpinCoord.ext h ha hδ
      rw [this]
      exact one_mem _
    · have : x = z := SpinCoord.ext h ha hδ
      rw [this]
      exact mem_zpowers z

theorem natCard_zpowers_z : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_z]

theorem mem_center_iff' {x : SpinCoord} : x ∈ center SpinCoord ↔ x.a = 0 ∧ x.δ = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨eq_zero_of_forall_pair_left fun ε => ?_, eq_zero_of_forall_pair fun b => ?_⟩
    · have := congrArg SpinCoord.s (h ⟨0, 0, ε⟩)
      simp only [mul_s, pair_zero_left, add_zero, zero_add] at this
      linear_combination this
    · have := congrArg SpinCoord.s (h ⟨0, b, 0⟩)
      simp only [mul_s, pair_zero_right, add_zero, zero_add] at this
      linear_combination -this
  · rintro ⟨ha, hδ⟩ g
    ext
    · simp only [mul_s, ha, hδ, pair_zero_left, pair_zero_right, add_zero]
      exact add_comm _ _
    · simp only [mul_a, ha, add_zero, zero_add]
    · simp only [mul_δ, hδ, add_zero, zero_add]

theorem center_eq : center SpinCoord = zpowers z := by
  ext x
  rw [mem_center_iff', mem_zpowers_z]

theorem commutator_eq : commutator SpinCoord = zpowers z := by
  apply le_antisymm
  · rw [_root_.commutator_def, commutator_le]
    intro g _ h _
    rw [mem_zpowers_z, commutatorElement_eq]
    exact ⟨rfl, rfl⟩
  · rw [zpowers_le, _root_.commutator_def]
    have h : ⁅(⟨0, ΩC, 0⟩ : SpinCoord), ⟨0, 0, Submodule.Quotient.mk (Pi.single 0 1)⟩⁆ = z := by
      rw [commutatorElement_eq]
      ext <;> simp [z, pair_ΩC_mk_single]
    rw [← h]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

@[expose] def hyp (φ : Module.Dual (ZMod 2) (C × Cocode)) : Subgroup SpinCoord where
  carrier := {x | φ (x.a, x.δ) = 0}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, mul_a, mul_δ] at *
    rw [← Prod.mk_add_mk, map_add, hx, hy, add_zero]
  one_mem' := by
    show φ (0, 0) = 0
    rw [Prod.mk_zero_zero, map_zero]
  inv_mem' := fun {x} hx => hx

theorem mem_hyp {φ : Module.Dual (ZMod 2) (C × Cocode)} {x : SpinCoord} :
    x ∈ hyp φ ↔ φ (x.a, x.δ) = 0 := Iff.rfl

theorem isCoatom_hyp {φ : Module.Dual (ZMod 2) (C × Cocode)} (hφ : φ ≠ 0) :
    IsCoatom (hyp φ) := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun v => by
      by_contra hv
      exact h ⟨v, hv⟩)
  rw [SetLike.isCoatom_iff]
  refine ⟨fun h => hv ?_, fun H g hle hg hgH => eq_top_iff.2 fun y _ => ?_⟩
  · have : (⟨0, v.1, v.2⟩ : SpinCoord) ∈ hyp φ := h ▸ mem_top _
    exact this
  · by_cases hy : φ (y.a, y.δ) = 0
    · exact hle hy
    · have hg1 : φ (g.a, g.δ) = 1 := eq_one_of_ne_zero _ hg
      have hy1 : φ (y.a, y.δ) = 1 := eq_one_of_ne_zero _ hy
      have hyg : y * g⁻¹ ∈ hyp φ := by
        rw [mem_hyp, mul_a, mul_δ, inv_a, inv_δ, ← Prod.mk_add_mk, map_add, hg1, hy1]
        rfl
      have := H.mul_mem (hle hyg) hgH
      rwa [inv_mul_cancel_right] at this

theorem frattini_eq : frattini SpinCoord = zpowers z := by
  apply le_antisymm
  · intro x hx
    rw [mem_zpowers_z]
    by_contra hne
    have hv : ((x.a, x.δ) : C × Cocode) ≠ 0 := fun h =>
      hne ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (C × Cocode), φ (x.a, x.δ) ≠ 0 := by
      by_contra h
      exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 fun φ => by
        by_contra hφ
        exact h ⟨φ, hφ⟩)
    have hφ0 : φ ≠ 0 := fun h => hφ (by rw [h, LinearMap.zero_apply])
    exact hφ (frattini_le_coatom (isCoatom_hyp hφ0) hx)
  · rw [zpowers_le]
    show z ∈ Order.radical (Subgroup SpinCoord)
    rw [Order.radical]
    simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq]
    intro M hM
    by_contra hz
    have hsup : M ⊔ zpowers z = ⊤ :=
      hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hz (h ▸ mem_sup_right (mem_zpowers z)))
    have : (zpowers z).Normal := by rw [← center_eq]; infer_instance
    have hrep : ∀ g : SpinCoord, ∃ m ∈ M, m.a = g.a ∧ m.δ = g.δ := by
      intro g
      have hg : g ∈ (↑(M ⊔ zpowers z) : Set SpinCoord) := by
        rw [hsup]
        exact mem_top g
      rw [mul_normal, Set.mem_mul] at hg
      obtain ⟨m, hm, n, hn, rfl⟩ := hg
      rw [SetLike.mem_coe, mem_zpowers_z] at hn
      exact ⟨m, hm, by simp [hn.1], by simp [hn.2]⟩
    obtain ⟨m₁, hm₁, ha₁, hδ₁⟩ := hrep ⟨0, ΩC, 0⟩
    obtain ⟨m₂, hm₂, ha₂, hδ₂⟩ := hrep ⟨0, 0, Submodule.Quotient.mk (Pi.single 0 1)⟩
    have hcomm : ⁅m₁, m₂⁆ = z := by
      rw [commutatorElement_eq]
      ext <;> simp [ha₁, hδ₁, ha₂, hδ₂, pair_ΩC_mk_single, z]
    apply hz
    rw [← hcomm, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

theorem isExtraspecialPGroup : IsExtraspecialPGroup 2 SpinCoord :=
  ⟨IsPGroup.of_card natCard, by rw [commutator_eq, center_eq], by rw [frattini_eq, center_eq],
    by rw [center_eq, natCard_zpowers_z]⟩

end SpinCoord

end CFSG.Monster.Spin
