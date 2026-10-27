module

public import CFSG.Quasithin.Background.RonanF95Lin2

public section

namespace CFSG.Quasithin.RonanF95

open Module

namespace OrderTwoInv

variable {A : Type*} [CommGroup A]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2_add_self : ∀ w : ZMod 2, w + w = 0 := by decide

theorem two_nsmul_additive (hexp : ∀ x : A, x * x = 1) (x : Additive A) :
    (2 : ℕ) • x = 0 := by
  rw [two_nsmul]
  exact hexp (Additive.toMul x)

abbrev addZMod2 (hexp : ∀ x : A, x * x = 1) : Module (ZMod 2) (Additive A) :=
  AddCommGroup.zmodModule (two_nsmul_additive hexp)

@[expose] def subm [Module (ZMod 2) (Additive A)] (X : Subgroup A) :
    Submodule (ZMod 2) (Additive A) where
  carrier := {x | Additive.toMul x ∈ X}
  add_mem' := fun {x y} hx hy => by
    show Additive.toMul (x + y) ∈ X
    rw [toMul_add]
    exact X.mul_mem hx hy
  zero_mem' := by
    show Additive.toMul (0 : Additive A) ∈ X
    exact X.one_mem
  smul_mem' := fun c {x} hx => by
    show Additive.toMul (c • x) ∈ X
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact X.one_mem
    · rw [one_smul]
      exact hx

theorem mem_subm [Module (ZMod 2) (Additive A)] {X : Subgroup A} {x : Additive A} :
    x ∈ subm X ↔ Additive.toMul x ∈ X := Iff.rfl

theorem card_subm [Module (ZMod 2) (Additive A)] (X : Subgroup A) :
    Nat.card (subm X) = Nat.card X :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun _ => Iff.rfl))

theorem card_eq_two_pow [Module (ZMod 2) (Additive A)] [Finite A] (X : Subgroup A) :
    Nat.card X = 2 ^ finrank (ZMod 2) (subm X) := by
  rw [← card_subm X, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_cases [Module (ZMod 2) (Additive A)] [Finite A] {X : Subgroup A}
    (hd : Nat.card X = 4 ∨ Nat.card X = 16) :
    finrank (ZMod 2) (subm X) = 2 ∨ finrank (ZMod 2) (subm X) = 4 := by
  rw [card_eq_two_pow X] at hd
  rcases hd with h | h
  · exact Or.inl (Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : (4 : ℕ) = 2 ^ 2)))
  · exact Or.inr (Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : (16 : ℕ) = 2 ^ 4)))

theorem subm_isCompl [Module (ZMod 2) (Additive A)] {X Y : Subgroup A} (hXY : IsCompl X Y) :
    IsCompl (subm X) (subm Y) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxX hxY
    have hX' : Additive.toMul x ∈ X := hxX
    have hY' : Additive.toMul x ∈ Y := hxY
    exact congrArg Additive.ofMul (Subgroup.disjoint_def.mp hXY.disjoint hX' hY')
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hmem : Additive.toMul x ∈ X ⊔ Y := by
      rw [hXY.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
    exact Submodule.mem_sup.mpr ⟨Additive.ofMul y, hy, Additive.ofMul z, hz,
      congrArg Additive.ofMul hyz⟩

@[expose] noncomputable def autLin [Module (ZMod 2) (Additive A)] (a : A ≃* A) :
    Module.End (ZMod 2) (Additive A) :=
  (MulEquiv.toAdditive a).toAddMonoidHom.toZModLinearMap 2

theorem autLin_apply [Module (ZMod 2) (Additive A)] (a : A ≃* A) (x : Additive A) :
    autLin a x = Additive.ofMul (a (Additive.toMul x)) := rfl

theorem autLin_sq [Module (ZMod 2) (Additive A)] (a : A ≃* A) (ha : ∀ x, a (a x) = x) :
    autLin a * autLin a = 1 := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, Module.End.one_apply, autLin_apply, autLin_apply]
  exact congrArg Additive.ofMul (ha (Additive.toMul x))

theorem mem_subm_iff_fix [Module (ZMod 2) (Additive A)] (a : A ≃* A) {X : Subgroup A}
    (hXa : ∀ x, x ∈ X ↔ a x = x) (x : Additive A) :
    x ∈ subm X ↔ autLin a x = x := by
  rw [mem_subm, hXa, autLin_apply]
  exact ⟨fun h => congrArg Additive.ofMul h, fun h => congrArg Additive.toMul h⟩

theorem autLin_add_mem [Module (ZMod 2) (Additive A)] (a : A ≃* A) {X : Subgroup A}
    (haX : ∀ x, a x * x ∈ X) (y : Additive A) : autLin a y + y ∈ subm X := by
  rw [mem_subm, toMul_add, autLin_apply, toMul_ofMul]
  exact haX _

theorem beta_one_left {β : A → A → ZMod 2} (hβl : ∀ x y z, β (x * y) z = β x z + β y z)
    (z : A) : β 1 z = 0 := by
  have h := hβl 1 1 z
  rw [mul_one] at h
  exact h.trans (zmod2_add_self _)

theorem beta_one_right {β : A → A → ZMod 2} (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (z : A) : β z 1 = 0 := by
  have h := hβr z 1 1
  rw [mul_one] at h
  exact h.trans (zmod2_add_self _)

@[expose] noncomputable def formB [Module (ZMod 2) (Additive A)] (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z) :
    Additive A →ₗ[ZMod 2] Additive A →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun x y => β (Additive.toMul x) (Additive.toMul y))
    (fun x y z => hβl (Additive.toMul x) (Additive.toMul y) (Additive.toMul z))
    (fun c x y => by
      rcases zmod2_cases c with rfl | rfl
      · simp [beta_one_left hβl]
      · simp)
    (fun x y z => hβr (Additive.toMul x) (Additive.toMul y) (Additive.toMul z))
    (fun c x y => by
      rcases zmod2_cases c with rfl | rfl
      · simp [beta_one_right hβr]
      · simp)

theorem formB_nondeg [Module (ZMod 2) (Additive A)] {β : A → A → ZMod 2}
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hnd : ∀ x, (∀ y, β x y = 0) → x = 1) (x : Additive A)
    (h : ∀ y : Additive A, formB β hβl hβr x y = 0) : x = 0 := by
  have h1 : Additive.toMul x = 1 := hnd (Additive.toMul x) (fun y => h (Additive.ofMul y))
  exact congrArg Additive.ofMul h1

@[expose] noncomputable def twoInv [Module (ZMod 2) (Additive A)] (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hβalt : ∀ x, β x x = 0) (hnd : ∀ x, (∀ y, β x y = 0) → x = 1)
    (q : A → ZMod 2) (hqf : ∀ x y, q (x * y) = q x + q y + β x y)
    (a b : A ≃* A) (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b x) = x)
    (hqa : ∀ x, q (a x) = q x) (hqb : ∀ x, q (b x) = q x)
    (X Y : Subgroup A) (hXa : ∀ x, x ∈ X ↔ a x = x) (hYb : ∀ y, y ∈ Y ↔ b y = y)
    (haX : ∀ x, a x * x ∈ X) (hbY : ∀ y, b y * y ∈ Y)
    (hXY : IsCompl X Y) (hqX : ∀ x ∈ X, q x = 0) (hqY : ∀ y ∈ Y, q y = 0) :
    TwoInv (Additive A) where
  b := formB β hβl hβr
  q := fun x => q (Additive.toMul x)
  v := autLin a
  i := autLin b
  X := subm X
  Y := subm Y
  hq := fun x y => hqf (Additive.toMul x) (Additive.toMul y)
  hbalt := fun x => hβalt (Additive.toMul x)
  hbnd := fun x h => formB_nondeg hβl hβr hnd x h
  hv := autLin_sq a ha
  hi := autLin_sq b hb
  hqv := fun x => hqa (Additive.toMul x)
  hqi := fun x => hqb (Additive.toMul x)
  hXv := fun x => mem_subm_iff_fix a hXa x
  hYi := fun y => mem_subm_iff_fix b hYb y
  hvX := fun y => autLin_add_mem a haX y
  hiY := fun x => autLin_add_mem b hbY x
  hXY := subm_isCompl hXY
  hqX := fun x hx => hqX (Additive.toMul x) hx
  hqY := fun y hy => hqY (Additive.toMul y) hy

theorem tpow_apply [Module (ZMod 2) (Additive A)] (a b : A ≃* A) (k : ℕ) (y : A) :
    ((autLin a * autLin b) ^ k) (Additive.ofMul y) = Additive.ofMul (((a * b) ^ k) y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, MulAut.mul_apply, ih, autLin_apply,
      toMul_ofMul]

end OrderTwoInv

theorem order_of_two_involutions {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (q : A → ZMod 2) (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hq : ∀ x y, q (x * y) = q x + q y + β x y) (hβalt : ∀ x, β x x = 0)
    (hnd : ∀ x, (∀ y, β x y = 0) → x = 1)
    (a b : A ≃* A) (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b x) = x)
    (hqa : ∀ x, q (a x) = q x) (hqb : ∀ x, q (b x) = q x)
    (X Y : Subgroup A) (hXa : ∀ x, x ∈ X ↔ a x = x) (hYb : ∀ y, y ∈ Y ↔ b y = y)
    (haX : ∀ x, a x * x ∈ X) (hbY : ∀ y, b y * y ∈ Y)
    (hXY : IsCompl X Y) (hqX : ∀ x ∈ X, q x = 0) (hqY : ∀ y ∈ Y, q y = 0)
    (hd : Nat.card X = 4 ∨ Nat.card X = 16) :
    (a * b) ^ 2 ≠ 1 ∧
      ((a * b) ^ 3 = 1 ∨ (Nat.card X = 16 ∧ ((a * b) ^ 5 = 1 ∨ (a * b) ^ 6 = 1))) := by
  letI : Module (ZMod 2) (Additive A) := OrderTwoInv.addZMod2 hexp
  obtain ⟨S, hSv, hSi, hSX⟩ : ∃ S : TwoInv (Additive A),
      S.v = OrderTwoInv.autLin a ∧ S.i = OrderTwoInv.autLin b ∧ S.X = OrderTwoInv.subm X :=
    ⟨OrderTwoInv.twoInv β hβl hβr hβalt hnd q hq a b ha hb hqa hqb X Y hXa hYb haX hbY hXY hqX hqY,
      rfl, rfl, rfl⟩
  have hSt : S.t = OrderTwoInv.autLin a * OrderTwoInv.autLin b := by
    show S.v * S.i = OrderTwoInv.autLin a * OrderTwoInv.autLin b
    rw [hSv, hSi]
  have hfin : finrank (ZMod 2) S.X = 2 ∨ finrank (ZMod 2) S.X = 4 := by
    rw [hSX]
    exact OrderTwoInv.finrank_cases hd
  obtain ⟨h2, h3⟩ := TwoInv.order_t S hfin
  have hpow : ∀ k : ℕ, S.t ^ k = 1 ↔ (a * b) ^ k = 1 := by
    intro k
    rw [hSt]
    constructor
    · intro h
      apply MulEquiv.ext
      intro y
      have h' := congrArg (fun f : Module.End (ZMod 2) (Additive A) => f (Additive.ofMul y)) h
      simp only [OrderTwoInv.tpow_apply, Module.End.one_apply] at h'
      rw [MulAut.one_apply]
      exact congrArg Additive.toMul h'
    · intro h
      have key : ∀ y : A, ((OrderTwoInv.autLin a * OrderTwoInv.autLin b) ^ k) (Additive.ofMul y)
          = (1 : Module.End (ZMod 2) (Additive A)) (Additive.ofMul y) := by
        intro y
        rw [OrderTwoInv.tpow_apply, h, MulAut.one_apply, Module.End.one_apply]
      apply LinearMap.ext
      intro x
      exact key (Additive.toMul x)
  refine ⟨fun h => h2 ((hpow 2).mpr h), ?_⟩
  rcases h3 with h3 | ⟨h4, h56⟩
  · exact Or.inl ((hpow 3).mp h3)
  · refine Or.inr ⟨?_, ?_⟩
    · calc Nat.card X = 2 ^ finrank (ZMod 2) (OrderTwoInv.subm X) :=
            OrderTwoInv.card_eq_two_pow X
        _ = 2 ^ 4 := by rw [← hSX, h4]
        _ = 16 := by norm_num
    · rcases h56 with h5 | h6
      · exact Or.inl ((hpow 5).mp h5)
      · exact Or.inr ((hpow 6).mp h6)

end CFSG.Quasithin.RonanF95
