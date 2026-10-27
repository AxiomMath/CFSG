module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OutdiagModel

theorem isElemAbelian_comm {H : Type*} [Group H] {p : ℕ} {E : Subgroup H} (h : IsElemAbelian p E)
    {a b : H} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_iff.mp h.1) ⟨a, ha⟩ ⟨b, hb⟩)

section Induces

variable {C G : Type*} [Group C] [Group G]

@[expose] def Induces (χ : C →* G) (m : G) (α : MulAut C) : Prop :=
  ∀ x : C, m * χ x * m⁻¹ = χ (α x)

namespace Induces

variable {χ : C →* G} {m n : G} {α β : MulAut C}

theorem one : Induces χ 1 1 := fun x => by simp

theorem mul (hm : Induces χ m α) (hn : Induces χ n β) : Induces χ (m * n) (α * β) := fun x => by
  calc m * n * χ x * (m * n)⁻¹ = m * (n * χ x * n⁻¹) * m⁻¹ := by group
    _ = χ ((α * β) x) := by rw [hn x, hm, MulAut.mul_apply]

theorem inv (hm : Induces χ m α) : Induces χ m⁻¹ α⁻¹ := fun x => by
  have h : m * χ (α⁻¹ x) * m⁻¹ = χ x := by rw [hm (α⁻¹ x), MulAut.apply_inv_self]
  calc m⁻¹ * χ x * m⁻¹⁻¹ = m⁻¹ * (m * χ (α⁻¹ x) * m⁻¹) * m := by rw [h]; group
    _ = χ (α⁻¹ x) := by group

theorem pow (hm : Induces χ m α) (k : ℕ) : Induces χ (m ^ k) (α ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact Induces.one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hm

theorem conj (g : C) : Induces χ (χ g) (MulAut.conj g) := fun x => by
  simp [MulAut.conj_apply]

theorem unique (hχ : Function.Injective χ) (hα : Induces χ m α) (hβ : Induces χ m β) : α = β :=
  MulEquiv.ext fun x => hχ ((hα x).symm.trans (hβ x))

theorem inj (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) (hm : Induces χ m α)
    (hn : Induces χ n α) : m = n := by
  have h : Induces χ (m⁻¹ * n) (α⁻¹ * α) := hm.inv.mul hn
  rw [inv_mul_cancel] at h
  have hmem : m⁻¹ * n ∈ Subgroup.centralizer (χ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h1 := h x
    rw [MulAut.one_apply] at h1
    calc χ x * (m⁻¹ * n) = ((m⁻¹ * n) * χ x * (m⁻¹ * n)⁻¹) * (m⁻¹ * n) := by rw [h1]
      _ = (m⁻¹ * n) * χ x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

end Induces

theorem exists_induces {χ : C →* G} (hχ : Function.Injective χ) {m : G}
    (hm : m ∈ Subgroup.normalizer (χ.range : Set G)) : ∃ α : MulAut C, Induces χ m α := by
  have h1 : ∀ x : C, ∃ y : C, χ y = m * χ x * m⁻¹ := fun x =>
    (Subgroup.mem_normalizer_iff.mp hm (χ x)).mp ⟨x, rfl⟩
  have hm' : m⁻¹ ∈ Subgroup.normalizer (χ.range : Set G) := Subgroup.inv_mem _ hm
  have h2 : ∀ x : C, ∃ y : C, χ y = m⁻¹ * χ x * m⁻¹⁻¹ := fun x =>
    (Subgroup.mem_normalizer_iff.mp hm' (χ x)).mp ⟨x, rfl⟩
  choose f hf using h1
  choose g hg using h2
  have hgf : ∀ x, g (f x) = x := fun x => hχ (by rw [hg, hf]; group)
  have hfg : ∀ x, f (g x) = x := fun x => hχ (by rw [hf, hg]; group)
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y =>
    hχ (by simp only [hf, map_mul]; group)
  exact ⟨MulEquiv.mk' ⟨f, g, hgf, hfg⟩ hmul, fun x => (hf x).symm⟩

end Induces

section Subgroups

variable {C G : Type*} [Group C] [Group G] {χ : C →* G}

@[expose] def inducedSub (χ : C →* G) (E : Subgroup G) : Subgroup (MulAut C) where
  carrier := {α | ∃ e ∈ E, Induces χ e α}
  one_mem' := ⟨1, E.one_mem, Induces.one⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, h⟩ ⟨e', he', h'⟩
    exact ⟨e * e', E.mul_mem he he', h.mul h'⟩
  inv_mem' := by
    rintro _ ⟨e, he, h⟩
    exact ⟨e⁻¹, E.inv_mem he, h.inv⟩

@[expose] def liftSub (χ : C →* G) (X : Subgroup (MulAut C)) : Subgroup G where
  carrier := {m | ∃ α ∈ X, Induces χ m α}
  one_mem' := ⟨1, X.one_mem, Induces.one⟩
  mul_mem' := by
    rintro _ _ ⟨α, hα, h⟩ ⟨β, hβ, h'⟩
    exact ⟨α * β, X.mul_mem hα hβ, h.mul h'⟩
  inv_mem' := by
    rintro _ ⟨α, hα, h⟩
    exact ⟨α⁻¹, X.inv_mem hα, h.inv⟩

theorem innerAut_le_inducedSub {E : Subgroup G} (hE : χ.range ≤ E) :
    (MulAut.conj : C →* MulAut C).range ≤ inducedSub χ E := by
  rintro _ ⟨g, rfl⟩
  exact ⟨χ g, hE ⟨g, rfl⟩, Induces.conj g⟩

theorem mem_of_conj_induces (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) {E : Subgroup G}
    {y m : G} {α β : MulAut C} (hy : Induces χ y α) (hm : Induces χ m β)
    (h : β⁻¹ * α * β ∈ inducedSub χ E) : m⁻¹ * y * m ∈ E := by
  obtain ⟨e, he, hel⟩ := h
  have h1 : Induces χ (m⁻¹ * y * m) (β⁻¹ * α * β) := (hm.inv.mul hy).mul hm
  rw [Induces.inj hC h1 hel]
  exact he

theorem card_inducedSub [Finite G] (hχ : Function.Injective χ)
    (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (χ.range : Set G)) :
    Nat.card (inducedSub χ E) = Nat.card E := by
  classical
  have hex : ∀ e : E, ∃ α : MulAut C, Induces χ e α := fun e => exists_induces hχ (hE e.2)
  choose F hF using hex
  let Φ : E → inducedSub χ E := fun e => ⟨F e, e, e.2, hF e⟩
  have hbij : Function.Bijective Φ := by
    refine ⟨fun e e' h => Subtype.ext (Induces.inj hC (hF e) ?_), fun α => ?_⟩
    · have h' : F e = F e' := congrArg Subtype.val h
      rw [h']
      exact hF e'
    · obtain ⟨_, e, he, hel⟩ := α
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact Induces.unique hχ (hF ⟨e, he⟩) hel
  exact (Nat.card_eq_of_bijective Φ hbij).symm

theorem isElemAbelian_inducedSub {p : ℕ} (hχ : Function.Injective χ) {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (inducedSub χ E) := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, ?_⟩
  · obtain ⟨α, e, he, ha⟩ := a
    obtain ⟨β, e', he', hb⟩ := b
    have h1 : Induces χ (e * e') (α * β) := ha.mul hb
    have h2 : Induces χ (e * e') (β * α) := by
      rw [isElemAbelian_comm hE he he']
      exact hb.mul ha
    exact Induces.unique hχ h1 h2
  · rintro _ ⟨e, he, h⟩
    have h1 := h.pow p
    rw [hE.2 e he] at h1
    exact Induces.unique hχ h1 Induces.one

theorem isElemAbelian_liftSub {p : ℕ} (hC : Subgroup.centralizer (χ.range : Set G) = ⊥)
    {X : Subgroup (MulAut C)} (hX : IsElemAbelian p X) : IsElemAbelian p (liftSub χ X) := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, ?_⟩
  · obtain ⟨a', α, hα, ha⟩ := a
    obtain ⟨b', β, hβ, hb⟩ := b
    have h1 : Induces χ (a' * b') (α * β) := ha.mul hb
    have h2 : Induces χ (b' * a') (α * β) := by
      rw [isElemAbelian_comm hX hα hβ]
      exact hb.mul ha
    exact Induces.inj hC h1 h2
  · rintro _ ⟨α, hα, h⟩
    have h1 := h.pow p
    rw [hX.2 α hα] at h1
    exact Induces.inj hC h1 Induces.one

theorem card_le_liftSub [Finite G] (hχ : Function.Injective χ) {X : Subgroup (MulAut C)}
    (hX : X ≤ inducedSub χ ⊤) : Nat.card X ≤ Nat.card (liftSub χ X) := by
  classical
  let f : liftSub χ X → X := fun m => ⟨Classical.choose m.2, (Classical.choose_spec m.2).1⟩
  have hsurj : Function.Surjective f := by
    intro α
    obtain ⟨m, -, hm⟩ := hX α.2
    have hmem : m ∈ liftSub χ X := ⟨α, α.2, hm⟩
    refine ⟨⟨m, hmem⟩, Subtype.ext ?_⟩
    exact Induces.unique hχ (Classical.choose_spec hmem).2 hm
  exact Nat.card_le_card_of_surjective f hsurj

end Subgroups

end OutdiagModel

end CFSG.StandardType
