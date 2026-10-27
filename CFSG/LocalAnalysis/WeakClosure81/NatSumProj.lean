module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NatSum

open CFSG.SignalizerFunctorTheorem.Quadratic

theorem exists_projection_onto_summand {G : Type} [Group G] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : G →* LGL 2 W) (W₂ : Submodule (ZMod 2) W)
    (hW₂ : ∀ g : G, ∀ w ∈ W₂, ρ g w ∈ W₂) (s : Finset (Submodule (ZMod 2) W))
    (hsinv : ∀ U ∈ s, ∀ g : G, ∀ u ∈ U, ρ g u ∈ U) (hsle : ∀ U ∈ s, W₂ ≤ U)
    (hsup : s.sup id ⊔ W₂ = ⊤) (hind : ∀ U ∈ s, U ⊓ ((s.erase U).sup id ⊔ W₂) ≤ W₂)
    {U : Submodule (ZMod 2) W} (hU : U ∈ s) {K : Type} [Field K]
    (φ : G →* Matrix.SpecialLinearGroup (Fin 2) K) (ψ : ↥U →+ (Fin 2 → K))
    (hψker : ∀ w : ↥U, ψ w = 0 ↔ (w : W) ∈ W₂)
    (hψeq : ∀ (g : G) (w : ↥U) (hw : ρ g (w : W) ∈ U),
      ψ ⟨ρ g (w : W), hw⟩ = (φ g : Matrix (Fin 2) (Fin 2) K).mulVec (ψ w)) :
    ∃ Ψ : W →+ (Fin 2 → K), (∀ u : ↥U, Ψ (u : W) = ψ u) ∧
      (∀ r ∈ (s.erase U).sup id ⊔ W₂, Ψ r = 0) ∧
      ∀ (g : G) (w : W), Ψ (ρ g w) = (φ g : Matrix (Fin 2) (Fin 2) K).mulVec (Ψ w) := by
  classical
  have hsup_inv : ∀ T : Finset (Submodule (ZMod 2) W),
      (∀ M ∈ T, ∀ g : G, ∀ m ∈ M, ρ g m ∈ M) →
      ∀ g : G, ∀ m ∈ T.sup id, ρ g m ∈ T.sup id := by
    intro T hT g
    refine Finset.sup_induction (p := fun M => ∀ m ∈ M, ρ g m ∈ M) ?_ ?_ ?_
    · intro m hm
      rw [Submodule.mem_bot] at hm ⊢
      rw [hm, map_zero]
    · intro M₁ hM₁ M₂ hM₂ m hm
      rw [Submodule.mem_sup] at hm ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      exact ⟨ρ g a, hM₁ a ha, ρ g b, hM₂ b hb, (map_add (ρ g) a b).symm⟩
    · intro M hM
      exact hT M hM g
  have hRinv : ∀ g : G, ∀ m ∈ (s.erase U).sup id ⊔ W₂,
      ρ g m ∈ (s.erase U).sup id ⊔ W₂ := by
    intro g m hm
    rw [Submodule.mem_sup] at hm ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    exact ⟨ρ g a,
      hsup_inv (s.erase U) (fun M hM => hsinv M (Finset.mem_of_mem_erase hM)) g a ha,
      ρ g b, hW₂ g b hb, (map_add (ρ g) a b).symm⟩
  have hUR : U ⊔ ((s.erase U).sup id ⊔ W₂) = ⊤ := by
    have h : s.sup id = U ⊔ (s.erase U).sup id := by
      conv_lhs => rw [← Finset.insert_erase hU]
      rw [Finset.sup_insert]
      rfl
    rw [← sup_assoc, ← h, hsup]
  let σ : ↥U × ↥((s.erase U).sup id ⊔ W₂) →+ W :=
    AddMonoidHom.mk' (fun p => (p.1 : W) + (p.2 : W)) (by
      intro p q
      change ((p.1 : W) + (q.1 : W)) + ((p.2 : W) + (q.2 : W)) =
        ((p.1 : W) + (p.2 : W)) + ((q.1 : W) + (q.2 : W))
      abel)
  have hσ : Function.Surjective σ := by
    intro w
    have hw : w ∈ U ⊔ ((s.erase U).sup id ⊔ W₂) := by
      rw [hUR]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hw
    obtain ⟨u, hu, r, hr, huw⟩ := hw
    exact ⟨(⟨u, hu⟩, ⟨r, hr⟩), huw⟩
  let Φ : ↥U × ↥((s.erase U).sup id ⊔ W₂) →+ (Fin 2 → K) :=
    ψ.comp (AddMonoidHom.fst ↥U ↥((s.erase U).sup id ⊔ W₂))
  have hker : σ.ker ≤ Φ.ker := by
    intro p hp
    rw [AddMonoidHom.mem_ker] at hp ⊢
    change ψ p.1 = 0
    rw [hψker]
    have hsum : (p.1 : W) + (p.2 : W) = 0 := hp
    refine hind U hU ⟨p.1.2, ?_⟩
    rw [add_eq_zero_iff_eq_neg] at hsum
    rw [hsum]
    exact Submodule.neg_mem _ p.2.2
  let Ψ : W →+ (Fin 2 → K) := (AddMonoidHom.liftOfSurjective σ hσ) ⟨Φ, hker⟩
  have hΨσ : ∀ p, Ψ (σ p) = Φ p := by
    intro p
    exact AddMonoidHom.liftOfRightInverse_comp_apply σ (Function.surjInv hσ)
      (Function.rightInverse_surjInv hσ) ⟨Φ, hker⟩ p
  have hΨu : ∀ u : ↥U, Ψ (u : W) = ψ u := by
    intro u
    have h : (u : W) = σ (u, 0) := by
      change (u : W) = (u : W) + (0 : W)
      simp
    rw [h, hΨσ]
    rfl
  have hΨr : ∀ r ∈ (s.erase U).sup id ⊔ W₂, Ψ r = 0 := by
    intro r hr
    have h : r = σ (0, (⟨r, hr⟩ : ↥((s.erase U).sup id ⊔ W₂))) := by
      change r = (0 : W) + r
      simp
    rw [h, hΨσ]
    change ψ (0 : ↥U) = 0
    simp
  refine ⟨Ψ, hΨu, hΨr, ?_⟩
  intro g w
  obtain ⟨p, hp⟩ := hσ w
  have hp1 : ρ g (p.1 : W) ∈ U := hsinv U hU g p.1 p.1.2
  have hp2 : ρ g (p.2 : W) ∈ (s.erase U).sup id ⊔ W₂ := hRinv g p.2 p.2.2
  have hgw : ρ g w = σ (⟨ρ g (p.1 : W), hp1⟩, ⟨ρ g (p.2 : W), hp2⟩) := by
    have h1 : σ p = (p.1 : W) + (p.2 : W) := rfl
    rw [← hp, h1, map_add]
    rfl
  have hwΨ : Ψ w = ψ p.1 := by
    rw [← hp, hΨσ]
    rfl
  rw [hgw, hΨσ, hwΨ]
  exact hψeq g p.1 hp1

end CFSG.LocalAnalysis.WeakClosure81.NatSum

end
