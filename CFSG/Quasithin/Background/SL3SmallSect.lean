module

public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.Quasithin.SL3Small

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fix_of_fix_sub {ρ : Representation (ZMod 2) G V} (hG : commutator G = ⊤)
    {U U' : Submodule (ZMod 2) V} (hUU' : U ≤ U') (h1 : ∀ g, ∀ u ∈ U, ρ g u = u)
    (h2 : ∀ g, ∀ v ∈ U', ρ g v - v ∈ U) : ∀ g, ∀ v ∈ U', ρ g v = v := by
  have hinv : ∀ g, ∀ v ∈ U', ρ g v ∈ U' := fun g v hv => by
    have : ρ g v = v + (ρ g v - v) := by abel
    rw [this]
    exact U'.add_mem hv (hUU' (h2 g v hv))
  have key : ∀ g h, ∀ w ∈ U', ρ g (ρ h w) = ρ h (ρ g w) := by
    intro g h w hw
    have a1 := h2 h w hw
    have a2 := h2 g w hw
    calc ρ g (ρ h w) = ρ g w + ρ g (ρ h w - w) := by rw [map_sub, add_sub_cancel]
      _ = ρ g w + (ρ h w - w) := by rw [h1 g _ a1]
      _ = ρ h w + (ρ g w - w) := by abel
      _ = ρ h w + ρ h (ρ g w - w) := by rw [h1 h _ a2]
      _ = ρ h (ρ g w) := by rw [map_sub, add_sub_cancel]
  let H : Subgroup G :=
    { carrier := {g | ∀ v ∈ U', ρ g v = v}
      mul_mem' := fun {a b} ha hb v hv => by
        rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
      one_mem' := fun v _ => by rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha v hv => by
        have h3 := ha (ρ a⁻¹ v) (hinv _ v hv)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h3
        exact h3.symm }
  have hcomm : commutator G ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _ v hv
    show ρ (g * h * g⁻¹ * h⁻¹) v = v
    have hw : ρ g⁻¹ (ρ h⁻¹ v) ∈ U' := hinv _ _ (hinv _ _ hv)
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      Module.End.mul_apply, key g h _ hw, ← Module.End.mul_apply (ρ g), ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  intro g
  have : g ∈ H := hcomm (hG ▸ Subgroup.mem_top g)
  exact this

theorem exists_section [Finite V] {ρ : Representation (ZMod 2) G V} (hG : commutator G = ⊤)
    (hnt : ∃ g v, ρ g v ≠ v) :
    ∃ U U' : Submodule (ZMod 2) V, U < U' ∧ (∀ g, ∀ v ∈ U', ρ g v ∈ U') ∧
      (∀ g, ∀ u ∈ U, ρ g u = u) ∧
      (∀ X : Submodule (ZMod 2) V, U ≤ X → X ≤ U' → (∀ g, ∀ v ∈ X, ρ g v ∈ X) →
        X = U ∨ X = U') ∧
      ∃ g, ∃ v ∈ U', ρ g v - v ∉ U := by
  classical
  have : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun X : Submodule (ZMod 2) V => (X : Set V)) SetLike.coe_injective
  set S : Set (Submodule (ZMod 2) V) :=
    {X | (∀ g, ∀ v ∈ X, ρ g v ∈ X) ∧ ∃ g, ∃ v ∈ X, ρ g v ≠ v} with hS
  have hSne : (⊤ : Submodule (ZMod 2) V) ∈ S := by
    obtain ⟨g, v, hv⟩ := hnt
    exact ⟨fun _ _ _ => Submodule.mem_top, g, v, Submodule.mem_top, hv⟩
  obtain ⟨U', hU'S, hU'min⟩ := wellFounded_lt.has_min S ⟨⊤, hSne⟩
  have hU'bot : (⊥ : Submodule (ZMod 2) V) < U' := by
    rw [bot_lt_iff_ne_bot]
    rintro rfl
    obtain ⟨-, g, v, hv, hne⟩ := hU'S
    rw [Submodule.mem_bot] at hv
    subst hv
    exact hne (map_zero _)
  set T : Set (Submodule (ZMod 2) V) := {X | (∀ g, ∀ v ∈ X, ρ g v ∈ X) ∧ X < U'} with hT
  have hTne : (⊥ : Submodule (ZMod 2) V) ∈ T := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero], hU'bot⟩
  obtain ⟨U, hUT, hUmax⟩ := wellFounded_gt.has_min T ⟨⊥, hTne⟩
  have hUtriv : ∀ g, ∀ u ∈ U, ρ g u = u := by
    by_contra hne
    push Not at hne
    obtain ⟨g, u, hu, hgu⟩ := hne
    exact hU'min U ⟨hUT.1, g, u, hu, hgu⟩ hUT.2
  refine ⟨U, U', hUT.2, hU'S.1, hUtriv, fun X hUX hXU' hX => ?_, ?_⟩
  · rcases eq_or_lt_of_le hXU' with h | h
    · exact Or.inr h
    · rcases eq_or_lt_of_le hUX with h' | h'
      · exact Or.inl h'.symm
      · exact absurd h' (hUmax X ⟨hX, h⟩)
  · by_contra hne
    push Not at hne
    obtain ⟨-, g, v, hv, hgv⟩ := hU'S
    exact hgv (fix_of_fix_sub hG hUT.2.le hUtriv hne g v hv)

end CFSG.Quasithin.SL3Small
