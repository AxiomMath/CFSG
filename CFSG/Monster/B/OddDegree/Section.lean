module

public import CFSG.Monster.B.Gen.UnipotentTwo
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.B.OddDegree

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def Invariant (ρ : G →* Module.End (ZMod 2) W) (U : Submodule (ZMod 2) W) : Prop :=
  ∀ g, ∀ u ∈ U, ρ g u ∈ U

@[expose] def TrivialOn (ρ : G →* Module.End (ZMod 2) W) (U' U : Submodule (ZMod 2) W) : Prop :=
  ∀ g, ∀ u ∈ U, ρ g u - u ∈ U'

@[expose] def secKer (ρ : G →* Module.End (ZMod 2) W) (U' U : Submodule (ZMod 2) W)
    (hU' : Invariant ρ U') (hU : Invariant ρ U) : Subgroup G where
  carrier := {g | ∀ u ∈ U, ρ g u - u ∈ U'}
  one_mem' u _ := by simp
  mul_mem' {g h} hg hh u hu := by
    have e : ρ (g * h) u - u = (ρ g (ρ h u - u) - (ρ h u - u)) + (ρ g u - u) + (ρ h u - u) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [e]
    refine U'.add_mem (U'.add_mem ?_ (hg u hu)) (hh u hu)
    have h1 : ρ h u - u ∈ U' := hh u hu
    exact U'.sub_mem (hU' g _ h1) h1
  inv_mem' {g} hg u hu := by
    have hu' : ρ g⁻¹ u ∈ U := hU g⁻¹ u hu
    have h1 : ρ g (ρ g⁻¹ u) - ρ g⁻¹ u ∈ U' := hg _ hu'
    have h2 : ρ g (ρ g⁻¹ u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2] at h1
    have : ρ g⁻¹ u - u = -(u - ρ g⁻¹ u) := by abel
    rw [this]
    exact U'.neg_mem h1

theorem mem_secKer {ρ : G →* Module.End (ZMod 2) W} {U' U : Submodule (ZMod 2) W}
    {hU' : Invariant ρ U'} {hU : Invariant ρ U} {g : G} :
    g ∈ secKer ρ U' U hU' hU ↔ ∀ u ∈ U, ρ g u - u ∈ U' := Iff.rfl

theorem secKer_normal (ρ : G →* Module.End (ZMod 2) W) (U' U : Submodule (ZMod 2) W)
    (hU' : Invariant ρ U') (hU : Invariant ρ U) : (secKer ρ U' U hU' hU).Normal := by
  constructor
  intro k hk g u hu
  have hu' : ρ g⁻¹ u ∈ U := hU g⁻¹ u hu
  have h1 : ρ k (ρ g⁻¹ u) - ρ g⁻¹ u ∈ U' := hk _ hu'
  have e : ρ (g * k * g⁻¹) u - u = ρ g (ρ k (ρ g⁻¹ u) - ρ g⁻¹ u) := by
    rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ g) (ρ g⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  change ρ (g * k * g⁻¹) u - u ∈ U'
  rw [e]
  exact hU' g _ h1

theorem trivialOn_iff_secKer_eq_top {ρ : G →* Module.End (ZMod 2) W} {U' U : Submodule (ZMod 2) W}
    (hU' : Invariant ρ U') (hU : Invariant ρ U) :
    TrivialOn ρ U' U ↔ secKer ρ U' U hU' hU = ⊤ := by
  rw [eq_top_iff]
  exact ⟨fun h g _ => h g, fun h g => h (Subgroup.mem_top g)⟩

@[expose] def NontrivSec (ρ : G →* Module.End (ZMod 2) W) (U' U : Submodule (ZMod 2) W) : Prop :=
  Invariant ρ U' ∧ Invariant ρ U ∧ U' ≤ U ∧ ¬ TrivialOn ρ U' U

theorem invariant_bot (ρ : G →* Module.End (ZMod 2) W) : Invariant ρ ⊥ := by
  intro g u hu
  rw [Submodule.mem_bot] at hu ⊢
  rw [hu, map_zero]

theorem invariant_top (ρ : G →* Module.End (ZMod 2) W) : Invariant ρ ⊤ := fun _ _ _ => trivial

variable [IsSimpleGroup G]

theorem trivial_of_trivial_of_trivial (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ρ : G →* Module.End (ZMod 2) W) {U' X U : Submodule (ZMod 2) W} (hU' : Invariant ρ U')
    (hU : Invariant ρ U) (h1 : TrivialOn ρ U' X) (h2 : TrivialOn ρ X U) :
    TrivialOn ρ U' U := by
  rw [trivialOn_iff_secKer_eq_top hU' hU]
  have hsq : ∀ g, g * g ∈ secKer ρ U' U hU' hU := by
    intro g u hu
    have hA : ρ g u - u ∈ X := h2 g u hu
    have hB : ρ g (ρ g u - u) - (ρ g u - u) ∈ U' := h1 g _ hA
    have e : ρ (g * g) u - u = (ρ g (ρ g u - u) - (ρ g u - u)) + ((ρ g u - u) + (ρ g u - u)) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [e, zmod_two_add_self, add_zero]
    exact hB
  set K := secKer ρ U' U hU' hU
  have := secKer_normal ρ U' U hU' hU
  have hq := eq_one_of_mul_self_eq_one_of_simple hnonab (QuotientGroup.mk' K) fun g => by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hsq g
  rw [eq_top_iff]
  intro g _
  have := hq g
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

variable [FiniteDimensional (ZMod 2) W]

theorem exists_irreducible_section (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ρ : G →* Module.End (ZMod 2) W) (hρ : ¬ TrivialOn ρ ⊥ ⊤) :
    ∃ U' U, NontrivSec ρ U' U ∧
      (∀ X, Invariant ρ X → U' ≤ X → X ≤ U → X = U' ∨ X = U) ∧
      Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) U' ≤ Module.finrank (ZMod 2) W ∧
      ((∃ X, Invariant ρ X ∧ X ≠ ⊥ ∧ X ≠ ⊤) →
        Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) U' < Module.finrank (ZMod 2) W) := by
  classical
  let P : ℕ → Prop := fun d => ∃ U' U, NontrivSec ρ U' U ∧
    Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) U' = d
  have hW : P (Module.finrank (ZMod 2) W) := ⟨⊥, ⊤, ⟨invariant_bot ρ, invariant_top ρ, bot_le, hρ⟩,
    by rw [finrank_bot, Nat.sub_zero, finrank_top]⟩
  have hex : ∃ d, P d := ⟨_, hW⟩
  obtain ⟨U', U, hsec, hd⟩ := Nat.find_spec hex
  have hmin : ∀ d < Nat.find hex, ¬ P d := fun d hd => Nat.find_min hex hd
  have hgap : ∀ {A B : Submodule (ZMod 2) W}, A < B →
      Module.finrank (ZMod 2) A < Module.finrank (ZMod 2) B :=
    fun h => Submodule.finrank_lt_finrank_of_lt h
  have hle : ∀ {A B : Submodule (ZMod 2) W}, A ≤ B →
      Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) B :=
    fun h => Submodule.finrank_mono h
  have htriv : ∀ A B : Submodule (ZMod 2) W, Invariant ρ A → Invariant ρ B → A ≤ B →
      Module.finrank (ZMod 2) B - Module.finrank (ZMod 2) A < Nat.find hex → TrivialOn ρ A B := by
    intro A B hA hB hAB hlt
    by_contra hn
    exact hmin _ hlt ⟨A, B, ⟨hA, hB, hAB, hn⟩, rfl⟩
  refine ⟨U', U, hsec, fun X hX h1 h2 => ?_, ?_, fun ⟨X, hX, hX0, hX1⟩ => ?_⟩
  · by_contra hne
    push Not at hne
    have hlt1 : U' < X := lt_of_le_of_ne h1 (Ne.symm hne.1)
    have hlt2 : X < U := lt_of_le_of_ne h2 hne.2
    have e1 := hgap hlt1
    have e2 := hgap hlt2
    have t1 := htriv U' X hsec.1 hX h1 (by rw [← hd]; omega)
    have t2 := htriv X U hX hsec.2.1 h2 (by rw [← hd]; omega)
    exact hsec.2.2.2 (trivial_of_trivial_of_trivial hnonab ρ hsec.1 hsec.2.1 t1 t2)
  · rw [hd]
    exact Nat.find_min' hex hW
  ·
    have hlt1 : (⊥ : Submodule (ZMod 2) W) < X := bot_lt_iff_ne_bot.2 hX0
    have hlt2 : X < ⊤ := lt_top_iff_ne_top.2 hX1
    have e1 := hgap hlt1
    have e2 := hgap hlt2
    rw [finrank_bot] at e1
    rw [finrank_top] at e2
    rw [hd]
    by_cases h0 : TrivialOn ρ ⊥ X
    · by_cases h1 : TrivialOn ρ X ⊤
      · exact absurd (trivial_of_trivial_of_trivial hnonab ρ (invariant_bot ρ) (invariant_top ρ)
          h0 h1) hρ
      · exact lt_of_le_of_lt (Nat.find_min' hex ⟨X, ⊤, ⟨hX, invariant_top ρ, le_top, h1⟩, rfl⟩)
          (by rw [finrank_top]; omega)
    · exact lt_of_le_of_lt (Nat.find_min' hex ⟨⊥, X, ⟨invariant_bot ρ, hX, bot_le, h0⟩, rfl⟩)
        (by rw [finrank_bot]; omega)

end CFSG.Monster.B.OddDegree
