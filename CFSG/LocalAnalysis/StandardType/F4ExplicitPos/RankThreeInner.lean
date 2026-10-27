module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Center
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart28

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.RankThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem sepB_B3 : sepB (TauCeti.DynkinType.B 3).cartanMatrix 6 = true := by
  rw [TauCeti.DynkinType.cartanMatrix_B]
  decide +kernel

theorem sepB_C3 : sepB (TauCeti.DynkinType.C 3).cartanMatrix 6 = true := by
  rw [TauCeti.DynkinType.cartanMatrix_C]
  decide +kernel

theorem eq_one_of_cartanMatrix_B3 (σ : Equiv.Perm (Fin (TauCeti.DynkinType.B 3).rank))
    (h : ∀ i j, (TauCeti.DynkinType.B 3).cartanMatrix (σ i) (σ j) =
      (TauCeti.DynkinType.B 3).cartanMatrix i j) : σ = 1 :=
  eq_one_of_sepB (M := (TauCeti.DynkinType.B 3).cartanMatrix) (K := 6) sepB_B3 h

theorem eq_one_of_cartanMatrix_C3 (σ : Equiv.Perm (Fin (TauCeti.DynkinType.C 3).rank))
    (h : ∀ i j, (TauCeti.DynkinType.C 3).cartanMatrix (σ i) (σ j) =
      (TauCeti.DynkinType.C 3).cartanMatrix i j) : σ = 1 :=
  eq_one_of_sepB (M := (TauCeti.DynkinType.C 3).cartanMatrix) (K := 6) sepB_C3 h

theorem cartan_type_B3_or_C3
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : compRank Ψ = 3) (hc : Ψ.ncard = 18) :
    ∃ (t : TauCeti.DynkinType) (_ : t.Valid) (e : simpleRoots Ψ ≃ Fin t.rank),
      (t = .B 3 ∨ t = .C 3) ∧
      ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ) := by
  classical
  have hne : Ψ.Nonempty := by
    rcases Ψ.eq_empty_or_nonempty with rfl | h
    · exfalso
      have h0 : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by simp [compRank]
      rw [h0] at hr
      omega
    · exact h
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : t.rank = 3 := by
    rw [← hcardΔ, ← compRank_eq_card hΨ, hr]
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he', ncard_setOf_isOrbitRoot_cartanMatrix t ht]
  have hnum : t.numRoots = 18 := by rw [← hN, hc]
  have htBC : t = .B 3 ∨ t = .C 3 := by
    cases t with
    | A n =>
      simp only [TauCeti.DynkinType.rank_A] at hrank
      simp only [TauCeti.DynkinType.numRoots_A] at hnum
      rw [hrank] at hnum
      norm_num at hnum
    | B n =>
      simp only [TauCeti.DynkinType.rank_B] at hrank
      subst hrank
      exact Or.inl rfl
    | C n =>
      simp only [TauCeti.DynkinType.rank_C] at hrank
      subst hrank
      exact Or.inr rfl
    | D n =>
      simp only [TauCeti.DynkinType.valid_D, TauCeti.DynkinType.rank_D] at ht hrank
      omega
    | E6 =>
      simp only [TauCeti.DynkinType.rank_E6] at hrank
      norm_num at hrank
    | E7 =>
      simp only [TauCeti.DynkinType.rank_E7] at hrank
      norm_num at hrank
    | E8 =>
      simp only [TauCeti.DynkinType.rank_E8] at hrank
      norm_num at hrank
    | F4 =>
      simp only [TauCeti.DynkinType.rank_F4] at hrank
      norm_num at hrank
    | G2 =>
      simp only [TauCeti.DynkinType.rank_G2] at hrank
      norm_num at hrank
  exact ⟨t, ht, e, htBC, he'⟩

theorem isInner_of_compRank_three_ncard_eighteen
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : compRank Ψ = 3) (hc : Ψ.ncard = 18)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f) :
    ∃ u ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, f γ = u • γ := by
  classical
  obtain ⟨t, ht, e, htBC, he'⟩ := cartan_type_B3_or_C3 hΨ hr hc
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ fun γ => f (w • γ) := hf.comp_smul hΨ hw
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨f (w • (β : Fin τ.rank → ℤ)), hf'.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : f (w • (β : Fin τ.rank → ℤ)) = f (w • (γ : Fin τ.rank → ℤ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (hf'.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'def
  have hσ' : ∀ j, f (w • (e.symm j : Fin τ.rank → ℤ)) = e.symm (σ' j) := fun j => by
    rw [hσ'def]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hπe, Equiv.ofBijective_apply, hπ]
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have h1 := he' (e.symm (σ' i)) (e.symm (σ' j))
    have h2 := he' (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ', ← hσ']
    exact corootPair_isometry hf' (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ'1 : σ' = 1 := by
    rcases htBC with h | h
    · subst h
      exact eq_one_of_cartanMatrix_B3 σ' hσ'M
    · subst h
      exact eq_one_of_cartanMatrix_C3 σ' hσ'M
  have hfix : ∀ β ∈ simpleRoots Ψ, f (w • β) = β := by
    intro β hβ
    have h : σ' (e ⟨β, hβ⟩) = e ⟨β, hβ⟩ := by
      have := congrArg (fun g : Equiv.Perm (Fin t.rank) => g (e ⟨β, hβ⟩)) hσ'1
      simpa using this
    have h2 : e.symm (e ⟨β, hβ⟩) = ⟨β, hβ⟩ := Equiv.symm_apply_apply e _
    have h3 := hσ' (e ⟨β, hβ⟩)
    rw [h2] at h3
    have h4' : e.symm (σ' (e ⟨β, hβ⟩)) = ⟨β, hβ⟩ := by
      rw [h, Equiv.symm_apply_apply]
    rw [h4'] at h3
    exact h3
  obtain ⟨u, hu, hfu⟩ := exists_smul_eq_of_isIsometry hΨ hf hw hfix
  exact ⟨u, hu, hfu⟩

theorem f4_rankThree_component_rho_isInner
    {L : Type} [Field L] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} (hρ : FrobRootMap D ρ)
    {a : Fin Tag.F4.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 3)
    (hc : (componentRoots (rootCharHom a) i).ncard = 18)
    (hstable : (fun γ => ρ γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i) :
    ∃ u ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      ∀ γ ∈ componentRoots (rootCharHom a) i, ρ γ = u • γ := by
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
    isRootComponent_componentRoots i
  have hbij : Set.BijOn (fun γ => ρ γ)
      (componentRoots (rootCharHom a) i) (componentRoots (rootCharHom a) i) :=
    ⟨fun γ hγ => by rw [← hstable]; exact ⟨γ, hγ, rfl⟩,
      ρ.injective.injOn,
      fun γ hγ => by
        rw [← hstable] at hγ
        obtain ⟨δ, hδ, hδγ⟩ := hγ
        exact ⟨δ, hδ, hδγ⟩⟩
  have hf : IsIsometry (componentRoots (rootCharHom a) i) (fun γ => ρ γ) :=
    ⟨hbij, fun γ _ δ _ => hρ.iform_eq γ δ, fun γ _ => hρ.neg_eq γ⟩
  exact isInner_of_compRank_three_ncard_eighteen hΨ hr hc hf

end CFSG.StandardType.F4ExplicitPos.RankThreeInner

end

end
