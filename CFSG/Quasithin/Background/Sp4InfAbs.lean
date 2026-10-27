module

public import CFSG.Quasithin.Background.B69Swap

public section

namespace CFSG.Quasithin

namespace B69

theorem swapGeo_of_two_parabolics {G₀ : Type} [Group G₀] {TP : MulAut G₀ → Prop}
    (h : ∀ S₀ : Sylow 2 G₀, ∃ Q₁ Q₂ : Subgroup G₀, Q₁ ≠ ⊤ ∧ Q₂ ≠ ⊤ ∧ Q₁ ⊔ Q₂ = ⊤ ∧
      (S₀ : Subgroup G₀) ≤ Q₁ ∧ (S₀ : Subgroup G₀) ≤ Q₂ ∧
      ∀ φ : MulAut G₀, (S₀ : Subgroup G₀).map (φ : G₀ →* G₀) = S₀ → TP φ →
        Q₁.map (φ : G₀ →* G₀) = Q₁ ∧ Q₂.map (φ : G₀ →* G₀) = Q₂) :
    SwapGeo G₀ TP := by
  intro Λ _ _ _ ι S₀ hS₀p hS₀i hS₀ne Ybar Tbar Mbar hInn hTM hMY hgen hmax hTS
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G₀ := Finite.of_equiv Λ ι.toEquiv
  have hS₀'p : IsPGroup 2 ↥(S₀.map (ι : Λ →* G₀)) :=
    hS₀p.of_equiv (S₀.equivMapOfInjective (ι : Λ →* G₀) ι.injective)
  have hS₀'i : ¬ 2 ∣ (S₀.map (ι : Λ →* G₀)).index := by
    rw [Subgroup.index_map_equiv]
    exact hS₀i
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hsup, hSQ₁, hSQ₂, hfix⟩ := h (hS₀'p.toSylow hS₀'i)
  have hsyl : ((hS₀'p.toSylow hS₀'i : Sylow 2 G₀) : Subgroup G₀) = S₀.map (ι : Λ →* G₀) := rfl
  rw [hsyl] at hSQ₁ hSQ₂ hfix
  set R₁ : Subgroup Λ := Q₁.map (ι.symm : G₀ →* Λ) with hR₁
  set R₂ : Subgroup Λ := Q₂.map (ι.symm : G₀ →* Λ) with hR₂
  have hmapι : ∀ Q : Subgroup G₀,
      (Q.map (ι.symm : G₀ →* Λ)).map (ι : Λ →* G₀) = Q := by
    intro Q
    rw [Subgroup.map_map]
    have : (ι : Λ →* G₀).comp (ι.symm : G₀ →* Λ) = MonoidHom.id _ := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  have hSR : ∀ Q : Subgroup G₀, S₀.map (ι : Λ →* G₀) ≤ Q →
      S₀ ≤ Q.map (ι.symm : G₀ →* Λ) := by
    intro Q hQ x hx
    exact ⟨ι x, hQ ⟨x, hx, rfl⟩, by simp⟩
  have hR₁top : R₁ ≠ ⊤ := fun h => hQ₁ (by
    rw [← hmapι Q₁, ← hR₁, h, Subgroup.map_top_of_surjective _ ι.surjective])
  have hR₂top : R₂ ≠ ⊤ := fun h => hQ₂ (by
    rw [← hmapι Q₂, ← hR₂, h, Subgroup.map_top_of_surjective _ ι.surjective])
  have hR₁bot : R₁ ≠ ⊥ := fun h => hS₀ne (le_bot_iff.1 (h ▸ hSR Q₁ hSQ₁))
  have hR₂bot : R₂ ≠ ⊥ := fun h => hS₀ne (le_bot_iff.1 (h ▸ hSR Q₂ hSQ₂))
  have hR₁₂ : R₁ ⊔ R₂ = ⊤ := by
    rw [hR₁, hR₂, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ ι.symm.surjective]
  have hTR : ∀ φ ∈ Tbar, φ ∈ autStab R₁ ∧ φ ∈ autStab R₂ := by
    intro φ hφ
    have hS' : (S₀.map (ι : Λ →* G₀)).map
        ((MulAut.congr ι φ : MulAut G₀) : G₀ →* G₀) = S₀.map (ι : Λ →* G₀) := by
      rw [Subgroup.map_map]
      have : ((MulAut.congr ι φ : MulAut G₀) : G₀ →* G₀).comp (ι : Λ →* G₀) =
          (ι : Λ →* G₀).comp (φ : Λ →* Λ) := by
        ext x
        simp [MulAut.congr_apply]
      rw [this, ← Subgroup.map_map, hTS φ hφ]
    obtain ⟨h1, h2⟩ := hfix (MulAut.congr ι φ) hS' (hcon φ hφ)
    refine ⟨?_, ?_⟩
    · rw [mem_autStab, hR₁, map_map_congr, h1]
    · rw [mem_autStab, hR₂, map_map_congr, h2]
  have hprop : ∀ R : Subgroup Λ, R ≠ ⊤ → R ≠ ⊥ → (∀ φ ∈ Tbar, φ ∈ autStab R) →
      ∀ x ∈ R, MulAut.conj x ∈ Mbar := by
    intro R hRt hRb hTR' x hx
    have hlt : Ybar ⊓ autStab R < Ybar := by
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have hY : Ybar ≤ autStab R := inf_eq_left.1 heq
      have hnorm : R.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have := hY (hInn g)
        rw [mem_autStab] at this
        rw [← this]
        exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exact hRb h
      · exact hRt h
    have hTV : Tbar ≤ Ybar ⊓ autStab R := fun φ hφ => ⟨(hTM.trans hMY.le) hφ, hTR' φ hφ⟩
    exact hmax _ hTV hlt ⟨hInn x, conj_mem_autStab hx⟩
  have hInnM : ∀ x : Λ, MulAut.conj x ∈ Mbar := by
    have hH : Mbar.comap (MulAut.conj : Λ →* MulAut Λ) = ⊤ := by
      rw [eq_top_iff, ← hR₁₂]
      exact sup_le (fun x hx => hprop R₁ hR₁top hR₁bot (fun φ hφ => (hTR φ hφ).1) x hx)
        (fun x hx => hprop R₂ hR₂top hR₂bot (fun φ hφ => (hTR φ hφ).2) x hx)
    intro x
    have : x ∈ Mbar.comap (MulAut.conj : Λ →* MulAut Λ) := by rw [hH]; trivial
    exact this
  exact absurd (hgen Mbar hTM hInnM) (not_le_of_gt hMY)

end B69

end CFSG.Quasithin
