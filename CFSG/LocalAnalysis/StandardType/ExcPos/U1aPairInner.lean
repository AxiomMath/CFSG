module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallInner
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankOne
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPair
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallPerfect
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel


private theorem u1aE3i_image_eq_of_componentOrbitLength_eq_one {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : componentOrbitLength ρ Ψ = 1) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ := by
  let S : Set ℕ :=
    {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ}
  have hS : componentOrbitLength ρ Ψ = sInf S := rfl
  have hne : S.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [hS, hc] at h
  have hmem := Nat.sInf_mem hne
  rw [← hS, h] at hmem
  simpa [S] using hmem.2

private theorem u1aE3i_ratOrbit_eq_of_image_eq {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ) :
    LieCore.ratOrbit (fun u => ρ u) Ψ = Ψ := by
  have hiter : ∀ k : ℕ, (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ = Ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.image_comp, ih, h]
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    rw [← hiter k]
    exact Set.mem_image_of_mem _ hδ
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem u1aE3i_curve_inter_model_le
    {τ : Tag} {p : ℕ} (S : LangSetup τ GGL p)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {σ : GGL ≃+* GGL} {z : ModGL τ GGL}
    (hnorm : ∀ g : ModGL τ GGL,
      g ∈ componentRootSpan GGL χ i ↔ z * g * z⁻¹ ∈ componentRootSpan GGL χ i)
    (hstep : ∀ g ∈ componentRootSpan GGL χ i,
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperf : Group.IsPerfect (componentRootSpan (fixSubfield σ) χ i))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ componentRoots χ i) :
    excCurve β z ⊓ S.D.model ≤
      ⁅componentRootSpan GGL χ i ⊓ S.Γ,
        componentRootSpan GGL χ i ⊓ S.Γ⁆ := by
  classical
  obtain ⟨-, hrange⟩ :=
    CFSG.StandardType.F4ExplicitPos.FixedCover.range_eq_derived_fixed_component
      (S := S) (χ := χ) i σ z hnorm hstep hperf
  intro x hx
  obtain ⟨hxcurve, hxmodel⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hyU, hyx⟩ := Subgroup.mem_map.1 hxcurve
  rw [mem_rootSubgroup] at hyU
  obtain ⟨c, rfl⟩ := hyU
  change MulAut.conj z (pinnedX τ GGL β c) = x at hyx
  rw [MulAut.conj_apply] at hyx
  have hxeq : x = z * pinnedX τ GGL β c * z⁻¹ := hyx.symm
  have hmodel : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := (S.D.mem_model.1 hxmodel).2
  have hxstep : S.D.step x = x := by
    change (MulAut.conj S.D.n) (S.D.Φ x) = x
    rw [MulAut.conj_apply]
    exact hmodel
  have hfix : frobGL σ (pinnedX τ GGL β c) = pinnedX τ GGL β c := by
    have h := hstep (pinnedX τ GGL β c) (pinnedX_mem_rootSpan hβ c)
    rw [← hxeq, hxstep] at h
    refine (MulAut.conj z).injective ?_
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact h.symm.trans hxeq
  have hσc : σ c = c := by
    have h1 : pinnedX τ GGL β (σ c) = pinnedX τ GGL β c := by
      rw [← CFSG.StandardType.F4ExplicitPos.NativePinFinal.frobGL_pinnedX_native σ β c]
      exact hfix
    exact pinnedX_injective τ GGL β h1
  have hc : c ∈ fixSubfield σ := (mem_fixSubfield (σ := σ)).2 hσc
  let c' : fixSubfield σ := ⟨c, hc⟩
  have hpin :=
    CFSG.StandardType.F4ExplicitPos.FixedCover.range_eq_derived_fixed_component_pinnedX
      (i := i) (σ := σ) (z := z) hβ c'
  rw [← hrange]
  refine ⟨⟨pinnedX τ (fixSubfield σ) β c', pinnedX_mem_rootSpan hβ c'⟩, ?_⟩
  exact hpin.trans hxeq.symm

theorem exists_stable_pair_inner {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (Δ : LangDatum τ GGL) (hq : Δ.q = 2 ^ f) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {a₁ a₂ : Fin τ.rank → GGLˣ}
    (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus) (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus)
    (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (hinner : twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ)
    (hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ))) :
    ∃ (α : Fin τ.rank → ℤ) (w : ModGL τ GGL),
      α ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ ∧
      w ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (LieCore.jointChar a₁ a₂)) ∧
      (excCurve α w).map Δ.step = excCurve α w ∧
      (excCurve (-α) w).map Δ.step = excCurve (-α) w ∧
      excCurve α w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) ∧
      excCurve (-α) w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum Δ ρ hρ hfin hf hq
  have himg : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) ''
      componentRoots (LieCore.jointChar a₁ a₂) iJ =
      componentRoots (LieCore.jointChar a₁ a₂) iJ :=
    u1aE3i_image_eq_of_componentOrbitLength_eq_one hb
  have hrat : LieCore.ratOrbit (fun u => ρ u)
      (componentRoots (LieCore.jointChar a₁ a₂) iJ) =
      componentRoots (LieCore.jointChar a₁ a₂) iJ :=
    u1aE3i_ratOrbit_eq_of_image_eq himg
  have hker : ∀ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂),
      ρ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂) := by
    intro γ hγ
    rw [kernelRoots] at hγ ⊢
    refine ⟨(hρ.isRoot_iff γ).2 hγ.1, ?_⟩
    have h1 : rootChar a₁ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₁ ha₁ γ hγ.1]
      have h := congrArg Prod.fst hγ.2
      change rootChar a₁ γ = 1 at h
      rw [h, one_pow]
    have h2 : rootChar a₂ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₂ ha₂ γ hγ.1]
      have h := congrArg Prod.snd hγ.2
      change rootChar a₂ γ = 1 at h
      rw [h, one_pow]
    show (rootChar a₁ (ρ γ), rootChar a₂ (ρ γ)) = 1
    rw [h1, h2]
    rfl
  obtain ⟨σ, z, hσ, hzZ, hnorm, hstep⟩ :=
    CFSG.StandardType.F4ExplicitPos.JointUntwist.exists_untwist_of_kernel_stable
      (S := S) (χ := LieCore.jointChar a₁ a₂) iJ (s := 1) one_pos
      (by simpa [Function.iterate_one, hSρ] using hker)
      (by simpa [Function.iterate_one, hSρ] using hinner)
  have hσq : ∀ c, σ c = c ^ (2 ^ f) := by
    intro c
    rw [hσ c, hSD, hq, pow_one]
  have hstepS : ∀ g ∈ componentRootSpan GGL (LieCore.jointChar a₁ a₂) iJ,
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    have h := hstep g hg
    rwa [iterHom_eq_iterate, Function.iterate_one] at h
  have hstepΔ : ∀ g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ),
      Δ.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    have h := hstep g hg
    rwa [iterHom_eq_iterate, Function.iterate_one, hSD] at h
  have hnormC : ∀ g : ModGL τ GGL,
      g ∈ componentRootSpan GGL (LieCore.jointChar a₁ a₂) iJ ↔
        z * g * z⁻¹ ∈ componentRootSpan GGL (LieCore.jointChar a₁ a₂) iJ :=
    fun g => hnorm iJ g
  have hΨ : IsRootComponent (componentRoots (LieCore.jointChar a₁ a₂) iJ) :=
    isRootComponent_componentRoots iJ
  have hperf : Group.IsPerfect
      (componentRootSpan (fixSubfield σ) (LieCore.jointChar a₁ a₂) iJ) := by
    by_cases hq4 : 4 ≤ Δ.q
    · have hq4' : 4 ≤ 2 ^ f := by rwa [hq] at hq4
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := GGL) σ hσq (by omega) hq4'
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.isPerfect_componentRootSpan_of_sq_ne_one
        (K := fixSubfield σ) ht iJ
    · have hq2 : Δ.q = 2 := by
        have hle : 2 ^ f ≤ 3 := by rw [← hq]; omega
        have hf1 : f = 1 := by
          by_contra hne
          have h2 : 2 ≤ f := by omega
          have h4 : 4 ≤ 2 ^ f :=
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
          omega
        rw [hq, hf1]
        norm_num
      have hσ2 : ∀ c, σ c = c ^ 2 := by
        intro c
        rw [hσ c, hSD, hq2, pow_one]
      have hΨne : (componentRoots (LieCore.jointChar a₁ a₂) iJ).Nonempty := by
        obtain ⟨⟨α, hαk⟩, hαi⟩ := Quotient.exists_rep iJ
        exact ⟨α, hαk, hαi⟩
      have hrankpos : 1 ≤ compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
        have hspan_ne : Submodule.span ℚ
            ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) ''
              componentRoots (LieCore.jointChar a₁ a₂) iJ) ≠ ⊥ := by
          intro hbot
          obtain ⟨α, hα⟩ := hΨne
          have hmem : (fun i => (α i : ℚ)) ∈ Submodule.span ℚ
              ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) ''
                componentRoots (LieCore.jointChar a₁ a₂) iJ) :=
            Submodule.subset_span ⟨α, hα, rfl⟩
          rw [hbot] at hmem
          have hzero : α = 0 := by
            ext j
            have hfun : (fun i => (α i : ℚ)) = 0 := by simpa using hmem
            have := congrFun hfun j
            have h0 : (α j : ℚ) = 0 := by simpa using this
            exact_mod_cast h0
          exact (hΨ.isRoot α hα).ne_zero hzero
        rw [compRank]
        exact (Submodule.one_le_finrank_iff).2 hspan_ne
      by_cases hr1 : compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1
      · exfalso
        have hsl : SimplyLacedTag τ := by
          rcases hτ with rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        have h2 : (componentRoots (LieCore.jointChar a₁ a₂) iJ).ncard = 2 :=
          CFSG.StandardType.LangRat.j4d_rank_one_ncard hsl hΨ hr1
        have hstep' : ∀ g ∈ rootSpan τ GGL
            (componentRoots (LieCore.jointChar a₁ a₂) iJ),
            iterHom Δ.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
          intro g hg
          have h := hstep g hg
          rwa [hSD] at h
        have hI : IsSolvable
            ↥(LieCore.twoElemGp
              (rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)) :=
          LieCore.isSolvable_twoElemGp_of_rankOne Δ iJ hσ2
            (fun g => hnorm iJ g) hstep' h2
        haveI : Group.IsSolvable ↥(LieCore.twoElemGp
            (rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)) := hI
        have hcomm :=
          (LieCore.commutator_twoElemGp_eq_of_untwist Δ iJ hσ2
            (fun g => hnorm iJ g) hstep').2.1
        have hratComp_le : LieCore.ratComp ρ Δ.Γ
            (componentRoots (LieCore.jointChar a₁ a₂) iJ) ≤
            ⁅LieCore.twoElemGp (rootSpan τ GGL
                (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model),
              LieCore.twoElemGp (rootSpan τ GGL
                (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)⁆ := by
          rw [LieCore.ratComp, hrat]
          exact (Subgroup.commutator_mono
            (inf_le_inf_left _ (Subgroup.commutator_le_self Δ.model))
            (inf_le_inf_left _ (Subgroup.commutator_le_self Δ.model))).trans hcomm
        have hsolv : Group.IsSolvable ↥(LieCore.ratComp ρ Δ.Γ
            (componentRoots (LieCore.jointChar a₁ a₂) iJ)) :=
          Group.isSolvable_of_isSolvable_injective
            (f := Subgroup.inclusion
              (hratComp_le.trans (Subgroup.commutator_le_self _)))
            (Subgroup.inclusion_injective _)
        haveI : Group.IsPerfect ↥(LieCore.ratComp ρ Δ.Γ
            (componentRoots (LieCore.jointChar a₁ a₂) iJ)) := ⟨hqs.1⟩
        haveI : Nontrivial ↥(LieCore.ratComp ρ Δ.Γ
            (componentRoots (LieCore.jointChar a₁ a₂) iJ)) := by
          haveI : Nontrivial (↥(LieCore.ratComp ρ Δ.Γ
              (componentRoots (LieCore.jointChar a₁ a₂) iJ)) ⧸
              Subgroup.center ↥(LieCore.ratComp ρ Δ.Γ
                (componentRoots (LieCore.jointChar a₁ a₂) iJ))) := hqs.2.toNontrivial
          exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(LieCore.ratComp ρ Δ.Γ
            (componentRoots (LieCore.jointChar a₁ a₂) iJ)))).nontrivial
        exact Group.IsPerfect.not_isSolvable _ hsolv
      · have hr2 : 2 ≤ compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by omega
        have hsl : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
          rcases hτ with rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        have hbig : ∃ α ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ,
            ∃ δ ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ, δ ≠ α ∧ δ ≠ -α := by
          have hcard : 2 ≤ (simpleRoots
              (componentRoots (LieCore.jointChar a₁ a₂) iJ)).card := by
            rw [← CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ]
            exact hr2
          obtain ⟨α, hα, δ, hδ, hne⟩ :=
            Finset.one_lt_card.1 (show 1 < (simpleRoots
              (componentRoots (LieCore.jointChar a₁ a₂) iJ)).card by omega)
          refine ⟨α, simpleRoots_subset hα, δ, simpleRoots_subset hδ, hne.symm, ?_⟩
          have hp : 0 < height δ := simpleRoots_height_pos hδ
          have hn : height (-α) < 0 := by
            rw [height_neg]
            have := simpleRoots_height_pos hα
            omega
          intro h
          rw [h] at hp
          omega
        exact isPerfect_componentRootSpan_simplyLaced hsl iJ hbig
  have hratComp : LieCore.ratComp ρ Δ.Γ
      (componentRoots (LieCore.jointChar a₁ a₂) iJ) =
      ⁅componentRootSpan GGL (LieCore.jointChar a₁ a₂) iJ ⊓ Δ.Γ,
        componentRootSpan GGL (LieCore.jointChar a₁ a₂) iJ ⊓ Δ.Γ⁆ := by
    rw [LieCore.ratComp, hrat]
    rfl
  obtain ⟨⟨α, hαk⟩, hαi⟩ := Quotient.exists_rep iJ
  have hα : α ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ := ⟨hαk, hαi⟩
  have hcurve : ∀ {β : Fin τ.rank → ℤ},
      β ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ →
      excCurve β z ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
    intro β hβ
    rw [hratComp]
    simpa only [LangSetup.Γ, hSD] using
      u1aE3i_curve_inter_model_le S iJ hnormC hstepS hperf hβ
  exact ⟨α, z, hα, hzZ, F4ExplicitPos.SelectedPair.rootSubgroup_conj_step_stable Δ hstepΔ hα,
    F4ExplicitPos.SelectedPair.rootSubgroup_conj_step_stable Δ hstepΔ (hΨ.neg_mem α hα),
    hcurve hα, hcurve (hΨ.neg_mem α hα)⟩

end CFSG.StandardType.LieKnownR2.ExcPos
