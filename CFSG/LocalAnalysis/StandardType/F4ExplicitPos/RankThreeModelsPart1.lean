module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.InnerSelectedPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB3Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RankThreeModels

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.F4ExplicitPos.RationalC3

open CFSG.StandardType.F4ExplicitPos.RationalC3Attach

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.RankThreeInner

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG.StandardType.F4ExplicitPos.RationalB3

open scoped Matrix

theorem f4_rankThree_component_rho_isInner_generic
    {Ω : Type} [Field Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {D : LangDatum Tag.F4 Ω} {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 3)
    (hc : (componentRoots χ i).ncard = 18)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i) :
    ∃ u ∈ componentWeylGroup (componentRoots χ i),
      ∀ γ ∈ componentRoots χ i, ρ γ = u • γ := by
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hbij : Set.BijOn (fun γ => ρ γ) (componentRoots χ i) (componentRoots χ i) :=
    ⟨fun γ hγ => by rw [← hstable]; exact ⟨γ, hγ, rfl⟩,
      ρ.injective.injOn,
      fun γ hγ => by
        rw [← hstable] at hγ
        obtain ⟨δ, hδ, hδγ⟩ := hγ
        exact ⟨δ, hδ, hδγ⟩⟩
  have hf : IsIsometry (componentRoots χ i) (fun γ => ρ γ) :=
    ⟨hbij, fun γ _ δ _ => hρ.iform_eq γ δ, fun γ _ => hρ.neg_eq γ⟩
  exact isInner_of_compRank_three_ncard_eighteen hΨ hr hc hf

theorem twistInner_of_compRank_three_ncard_eighteen_generic
    {Ω : Type} [Field Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {D : LangDatum Tag.F4 Ω} {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 3)
    (hc : (componentRoots χ i).ncard = 18)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i) :
    twistInner (componentRoots χ i) ρ := by
  obtain ⟨u, hu, huγ⟩ :=
    f4_rankThree_component_rho_isInner_generic (Ω := Ω) (χ := χ) hρ i hr hc hstable
  have hWle : componentWeylGroup (componentRoots χ i) ≤
      Subgroup.closure {s : WeylGroup Tag.F4 |
        ∃ γ ∈ componentRoots χ i, s = rootReflection γ} := by
    rw [componentWeylGroup]
    exact Subgroup.closure_mono
      (by rintro _ ⟨β, hβ, rfl⟩; exact ⟨β, simpleRoots_subset hβ, rfl⟩)
  exact ⟨u, hWle hu, huγ⟩

theorem frobGL_eq_bcGL {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) :
    frobGL (τ := Tag.F4) σ = bcGL (τ := Tag.F4) σ.toRingHom := by
  rw [bcGL, bcEndHom_eq_entrywiseHom]

theorem f4_rankThree_c3_actual_model_producer
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (hk : Nat.card K = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i)
    (h3 : compRank (componentRoots χ i) = 3)
    (h18 : (componentRoots χ i).ncard = 18)
    (v : WeylGroup Tag.F4)
    (hshape : componentRoots χ i = (fun α => v • α) '' C3Range.c3RootSet)
    (Ccent : Subgroup (ModGL Tag.F4 Ω))
    (hHcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent)
    (P : Subgroup (ModGL Tag.F4 Ω))
    (hP : CFSG.Assembly.IsComponentOf P (D.Γ ⊓ Ccent))
    (hPleH : P ≤ rootSpan Tag.F4 Ω (componentRoots χ i)) :
    ∃ (σ : Ω ≃+* Ω) (z : ModGL Tag.F4 Ω)
      (Φ : ↥(StatedSp 3 K) →* ModGL Tag.F4 Ω),
      (∀ c, σ c = c ^ D.q) ∧
      z ∈ Zsub χ ∧ normalizesAll χ z ∧
      (∀ g, g ∈ MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v)) ↔
        z * g * z⁻¹ ∈ MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v))) ∧
      (∀ g ∈ MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v)),
        D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹) ∧
      Φ = (((MulAut.conj z).toMonoidHom.comp
        (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v))).comp
        (statedSpMap (algebraMap K Ω) 3)) ∧
      Function.Injective Φ ∧
      MonoidHom.range Φ =
        MonoidHom.range (conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v)) ⊓ D.model ∧
      P = MonoidHom.range Φ := by
  classical
  have hinner : twistInner (componentRoots χ i) ρ :=
    twistInner_of_compRank_three_ncard_eighteen_generic (Ω := Ω) (χ := χ) hρ i h3 h18 hstable
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      (χ := χ) D f hf hq ρ hρ i hker hinner
  set n : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω v with hn_def
  have hn_adj : n ∈ adjointGroup Tag.F4 Ω :=
    canonicalRep_mem_adjointGroup (τ := Tag.F4) (coxeterSystem Tag.F4) Ω v
  have hn : bcGL (τ := Tag.F4) σ.toRingHom n = n := by
    rw [hn_def]
    exact bcGL_canonicalRep (τ := Tag.F4) σ.toRingHom (coxeterSystem Tag.F4) v
  have hz_adj : z ∈ adjointGroup Tag.F4 Ω :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub_le_adjointGroup χ hzZ
  have hKq : Nat.card K = D.q := hk.trans hq.symm
  have hFr : ∀ c, σ.toRingHom c = c ^ Nat.card K := by
    intro c
    change σ c = c ^ Nat.card K
    rw [hσc, ← hKq]
  have hrange_n : MonoidHom.range (conjIM Ω n) =
      rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [hn_def, range_conjIM_canonicalRep, ← hshape]
  have hzH : ∀ g, g ∈ MonoidHom.range (conjIM Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjIM Ω n) := by
    intro g
    rw [hrange_n]
    exact CFSG.StandardType.F4ExplicitPos.NativePinFinal.normalizesAll_apply hnorm i g
  have hfrob_bcgl : frobGL (τ := Tag.F4) σ = bcGL (τ := Tag.F4) σ.toRingHom :=
    frobGL_eq_bcGL (Ω := Ω) σ
  have hzF : ∀ g ∈ MonoidHom.range (conjIM Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) σ.toRingHom g * z⁻¹ := by
    intro g hg
    rw [hrange_n] at hg
    rw [← hfrob_bcgl]
    exact hgoal g hg
  have hHcent' : MonoidHom.range (conjIM Ω n) ≤ Ccent := by
    rw [hrange_n]; exact hHcent
  have hPleH' : P ≤ MonoidHom.range (conjIM Ω n) := by
    rw [hrange_n]; exact hPleH
  refine ⟨σ, z, (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
      (statedSpMap (algebraMap K Ω) 3)), hσc, hzZ, hnorm, hzH, hzF, rfl, ?_, ?_, ?_⟩
  · exact Phi_injective (Ω := Ω) n z
  · exact range_Phi_eq_inf_model (Ω := Ω) (K := K) D σ.toRingHom hFr n z
      hn_adj hz_adj hn hzH hzF
  · exact component_eq_range_Phi_of_le_cent (Ω := Ω) (K := K) D σ.toRingHom hFr n z
      hn_adj hz_adj hn hzH hzF rfl hHcent' hP hPleH'

end CFSG.StandardType.F4ExplicitPos.RankThreeModels
end

end
