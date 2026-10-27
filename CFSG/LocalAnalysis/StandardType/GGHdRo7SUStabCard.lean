module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SUStabCardAux_ext {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} {b : Module.Basis (Fin m) (ZMod p) V} {a₁ a₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ i, a₁ (b i) = a₂ (b i)) : a₁ = a₂ := by
  have hlin : (a₁ : V →ₗ[ZMod p] V) = (a₂ : V →ₗ[ZMod p] V) := b.ext h
  exact LinearEquiv.ext (fun v => congrArg (fun f : V →ₗ[ZMod p] V => f v) hlin)

private lemma hdRo7SUStabCardAux_injective (hN : SUNormalizerLeaf) {p : ℕ} [Fact p.Prime]
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {b : Module.Basis (Fin m) (ZMod p) V} {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : SULinData p m V b H A) :
    ∃ f : {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a (SUOnes p b) = SUOnes p b} →
        Equiv.Perm (Fin m) ⊕ Equiv.Perm (Fin m), Function.Injective f := by
  classical
  let d : (a : {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a (SUOnes p b) = SUOnes p b}) →
      (SUPerm p b a.1 ∨ ∃ σ : Equiv.Perm (Fin m),
        ∀ i, a.1 (b i) = -b (σ i) + (2 / (m : ZMod p)) • SUOnes p b) := fun a =>
    hN p hD.hp m hD.hm hD.h3 V b a.1 (hD.hStab a.1 (hD.hHA a.2.1) a.2.2) a.2.2
  let f : (a : {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a (SUOnes p b) = SUOnes p b}) →
      Equiv.Perm (Fin m) ⊕ Equiv.Perm (Fin m) := fun a =>
    if h : SUPerm p b a.1 then Sum.inl (Classical.choose h)
    else Sum.inr (Classical.choose ((d a).resolve_left h))
  refine ⟨f, ?_⟩
  intro a₁ a₂ heq
  have key : a₁.1 = a₂.1 := by
    by_cases h1 : SUPerm p b a₁.1
    · by_cases h2 : SUPerm p b a₂.1
      · have hf1 : f a₁ = Sum.inl (Classical.choose h1) := by
          dsimp only [f]; exact dif_pos h1
        have hf2 : f a₂ = Sum.inl (Classical.choose h2) := by
          dsimp only [f]; exact dif_pos h2
        have hσ : Classical.choose h1 = Classical.choose h2 := by
          have h := heq
          rw [hf1, hf2] at h
          exact Sum.inl_injective h
        exact hdRo7SUStabCardAux_ext (fun i => by
          rw [Classical.choose_spec h1 i, hσ, ← Classical.choose_spec h2 i])
      · have hf1 : f a₁ = Sum.inl (Classical.choose h1) := by
          dsimp only [f]; exact dif_pos h1
        have hf2 : f a₂ = Sum.inr (Classical.choose ((d a₂).resolve_left h2)) := by
          dsimp only [f]; exact dif_neg h2
        have h := heq
        rw [hf1, hf2] at h
        exact (Sum.inl_ne_inr h).elim
    · by_cases h2 : SUPerm p b a₂.1
      · have hf1 : f a₁ = Sum.inr (Classical.choose ((d a₁).resolve_left h1)) := by
          dsimp only [f]; exact dif_neg h1
        have hf2 : f a₂ = Sum.inl (Classical.choose h2) := by
          dsimp only [f]; exact dif_pos h2
        have h := heq
        rw [hf1, hf2] at h
        exact (Sum.inr_ne_inl h).elim
      · have hf1 : f a₁ = Sum.inr (Classical.choose ((d a₁).resolve_left h1)) := by
          dsimp only [f]; exact dif_neg h1
        have hf2 : f a₂ = Sum.inr (Classical.choose ((d a₂).resolve_left h2)) := by
          dsimp only [f]; exact dif_neg h2
        have hσ : Classical.choose ((d a₁).resolve_left h1)
            = Classical.choose ((d a₂).resolve_left h2) := by
          have h := heq
          rw [hf1, hf2] at h
          exact Sum.inr_injective h
        exact hdRo7SUStabCardAux_ext (fun i => by
          rw [Classical.choose_spec ((d a₁).resolve_left h1) i, hσ,
            ← Classical.choose_spec ((d a₂).resolve_left h2) i])
  exact Subtype.ext key

theorem su_stabCard_holds : SUStabCardLeaf := by
  intro hN p hpFact m V instAC instMod b H A hD
  obtain ⟨f, hf⟩ := hdRo7SUStabCardAux_injective hN hD
  have hcard : Nat.card (Equiv.Perm (Fin m) ⊕ Equiv.Perm (Fin m)) = 2 * m.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_perm, Fintype.card_fin]
    ring
  calc Nat.card {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a (SUOnes p b) = SUOnes p b}
      ≤ Nat.card (Equiv.Perm (Fin m) ⊕ Equiv.Perm (Fin m)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 * m.factorial := hcard

end CFSG.StandardType.HdRo7SU
