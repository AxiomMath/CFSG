module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

theorem preconnected_induce_of_surjOn {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {s : Set V} {t : Set W} (hmaps : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (hs : (G.induce s).Preconnected) : (H.induce t).Preconnected := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨a', ha', rfl⟩ := hsurj ha
  obtain ⟨b', hb', rfl⟩ := hsurj hb
  exact (hs ⟨a', ha'⟩ ⟨b', hb'⟩).map (induceHom f hmaps)

theorem preconnected_induce_preimage {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    {ψ : α → β} (hψ : Function.Surjective ψ)
    (hadj : ∀ a a', a ≠ a' → (G.Adj a a' ↔ ψ a = ψ a' ∨ H.Adj (ψ a) (ψ a'))) {T : Set β}
    (hT : (H.induce T).Preconnected) : (G.induce (ψ ⁻¹' T)).Preconnected := by
  have step : ∀ a a' : ψ ⁻¹' T, (ψ a = ψ a' ∨ H.Adj (ψ a) (ψ a')) →
      (G.induce (ψ ⁻¹' T)).Reachable a a' := by
    intro a a' h
    by_cases e : a = a'
    · rw [e]
    · exact Adj.reachable ((hadj a a' fun h' => e (Subtype.ext h')).2 h)
  have key : ∀ (x y : T) (_ : (H.induce T).Walk x y) (a b : ψ ⁻¹' T), ψ a = x → ψ b = y →
      (G.induce (ψ ⁻¹' T)).Reachable a b := by
    intro x y w
    induction w with
    | nil => exact fun a b ha hb => step a b (Or.inl (ha.trans hb.symm))
    | @cons x z y hxz _ ih =>
      intro a b ha hb
      obtain ⟨c, hc⟩ := hψ z
      have hcT : c ∈ ψ ⁻¹' T := by
        rw [Set.mem_preimage, hc]
        exact z.2
      refine (step a ⟨c, hcT⟩ (Or.inr ?_)).trans (ih ⟨c, hcT⟩ b hc hb)
      rw [ha]
      exact hc ▸ hxz
  rintro a b
  obtain ⟨w⟩ := hT ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩
  exact key _ _ w a b rfl rfl

end CFSG.Monster.B.GSide
