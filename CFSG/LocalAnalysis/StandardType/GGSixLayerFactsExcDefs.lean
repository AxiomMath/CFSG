module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFinal
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule

namespace LayerFacts

@[expose] def GGAbelianCoreAt (L : Type) [Group L] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ A : Subgroup L, IsPGroup p A →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ (β : Type) (S : β → Subgroup L),
        LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S

theorem centralizer_eq_comap_map {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (A : Subgroup L) :
    Subgroup.centralizer (A : Set L) =
      (Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup L') : Set L')).comap
        e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hx _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hx a ha]
  · intro hx a ha
    exact e.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hx (e a) ⟨a, ha, rfl⟩)

theorem ggAbelianCoreAt_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : GGAbelianCoreAt L') : GGAbelianCoreAt L := by
  intro p hp hp2 A hA hAc
  have hAc' : ∀ a ∈ A.map e.toMonoidHom, ∀ b ∈ A.map e.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  obtain ⟨β, S, hS⟩ := h p hp hp2 _ (hA.map e.toMonoidHom) hAc'
  refine ⟨β, fun c => (S c).comap e.toMonoidHom, ?_⟩
  rw [centralizer_eq_comap_map e A]
  exact hS.comap e.toMonoidHom e.injective (by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top)

theorem ggLayer_of_abelianCore {L : Type} [Group L] [Finite L] (hZL : Subgroup.center L = ⊥)
    (hcore : GGAbelianCoreAt L) {G : Type*} [Group G] {ψ : L →* G}
    (hker : ψ.ker ≤ Subgroup.center L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsPGroup p E) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hinner : ∀ e ∈ E, ∃ g ∈ ψ.range, e * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
    exact hker
  exact ggLayer_of_inner hinj hZL hE hcomm hinner fun A hA hAc => hcore p hp hp2 A hA hAc

end LayerFacts

section Tags

@[expose] def GGExcAdjCoreInput (τ : CFSG.Blueprint.Chevalley.Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], LayerFacts.GGAbelianCoreAt ↥(adjointGroup τ K)

theorem ggLayerTags_F4_of_core (hcore : GGExcAdjCoreInput .F4) :
    GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_⟩ <;>
  · obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have h := LayerFacts.ggLayer_of_abelianCore (L := ↥(adjointGroup .F4 (GaloisField 2 f)))
      center_adjointGroup_eq_bot (hcore (GaloisField 2 f)) hker hp hp2 hE hcomm
      fun e he => PsiDiag.Adj.exists_mem_centralizer_F4 ψ hker (hdiag e he)
    first
    | exact h.1
    | exact h.2

theorem ggLayerTags_E8_of_core (hcore : GGExcAdjCoreInput .E8) :
    GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_⟩ <;>
  · obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have h := LayerFacts.ggLayer_of_abelianCore (L := ↥(adjointGroup .E8 (GaloisField 2 f)))
      center_adjointGroup_eq_bot (hcore (GaloisField 2 f)) hker hp hp2 hE hcomm
      fun e he => PsiDiag.Adj.exists_mem_centralizer_E8 ψ hker (hdiag e he)
    first
    | exact h.1
    | exact h.2

theorem ggLayerTags_E7_of_core (hcore : GGExcAdjCoreInput .E7) :
    GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_⟩ <;>
  · obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have : Finite ↥(e7Data_valid.minGroup (GaloisField 2 f)) :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e7Data_valid
    have h := LayerFacts.ggLayer_of_abelianCore
      (L := ↥(e7Data_valid.minGroup (GaloisField 2 f)))
      CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
      (LayerFacts.ggAbelianCoreAt_of_mulEquiv
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f))
        (hcore (GaloisField 2 f))) hker hp hp2 hE hcomm
      fun e he => PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker (hdiag e he)
    first
    | exact h.1
    | exact h.2

theorem ggLayerInputs_of_exc_cores (hF4 : GGExcAdjCoreInput .F4) (hE7 : GGExcAdjCoreInput .E7)
    (hE8 : GGExcAdjCoreInput .E8) (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining_five (ggLayerTags_F4_of_core hF4) hE6 (ggLayerTags_E7_of_core hE7)
    (ggLayerTags_E8_of_core hE8) hTwE6

end Tags

end CFSG.StandardType
