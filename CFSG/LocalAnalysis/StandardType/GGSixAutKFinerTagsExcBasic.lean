module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcDefs
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Tag

@[expose] def GGLayerNotExcThreeTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        GGNotExcThreeOrder (ggCQ C)

theorem ggLayerNotDFourTwoTag_of_notExcThree {t : StatedLieTag} (h : GGLayerNotExcThreeTag t) :
    GGLayerNotDFourTwoTag t := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC
  exact (ggAKFG_not_excThree (h G n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC)).1

theorem ggLayerNotUFourAltSixTag_of_notExcThree {t : StatedLieTag}
    (h : GGLayerNotExcThreeTag t) : GGLayerNotUFourAltSixTag t := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC
  exact (ggAKFG_not_excThree (h G n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC)).2

end Tag

@[expose] def GGCentCompNotExcThree (L : Type) [Group L] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ s : L, s ^ p = 1 →
    ∀ C : Subgroup L, IsComponentOf C (Subgroup.centralizer ({s} : Set L)) →
      GGNotExcThreeOrder (ggCQ C)

namespace TagsExc

variable {L M : Type*} [Group L] [Group M]

theorem isComponentOf_comap (f : L →* M) (hf : Function.Injective f) {H : Subgroup L}
    {C : Subgroup M} (hC : IsComponentOf C (H.map f)) : IsComponentOf (C.comap f) H := by
  obtain ⟨hCH, hsn, hq⟩ := hC
  have hCr : C ≤ f.range := hCH.trans (Subgroup.map_le_range f H)
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hCH hx
    rw [← hf hyx]
    exact hy
  · have h := LayerCores.ggSubnormal_comap f hsn
    rwa [Subgroup.comap_map_eq_self_of_injective hf] at h
  · have e : ↥(C.comap f) ≃* ↥C :=
      (Subgroup.equivMapOfInjective (C.comap f) f hf).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hCr))
    rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem centralizer_singleton_eq_comap (e : L ≃* M) (s : L) :
    Subgroup.centralizer ({s} : Set L) =
      (Subgroup.centralizer ({e s} : Set M)).comap e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact e.injective (by rw [map_mul, map_mul, h])

end TagsExc

theorem ggCentCompNotExcThree_of_mulEquiv {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : GGCentCompNotExcThree M) : GGCentCompNotExcThree L := by
  intro p hp hp2 s hs C hC
  have hes : e s ^ p = 1 := by rw [← map_pow, hs, map_one]
  have hcent : Subgroup.centralizer ({s} : Set L) =
      (Subgroup.centralizer ({e s} : Set M)).map e.symm.toMonoidHom := by
    rw [TagsExc.centralizer_singleton_eq_comap e s, Subgroup.comap_equiv_eq_map_symm']
  rw [hcent] at hC
  have hC' := TagsExc.isComponentOf_comap e.symm.toMonoidHom e.symm.injective hC
  have h1 := h p hp hp2 (e s) hes _ hC'
  have h2 : ggCQ (C.comap e.symm.toMonoidHom) = ggCQ C :=
    ggCQ_comap_of_injective e.symm.toMonoidHom e.symm.injective (by
      rw [MonoidHom.range_eq_top.mpr e.symm.surjective]
      exact le_top)
  rwa [h2] at h1

theorem ggNotExcThree_of_isComponentOf_inner {L : Type} [Group L]
    (hZL : Subgroup.center L = ⊥) (hL : GGCentCompNotExcThree L) {G : Type} [Group G]
    {ψ : L →* G} (hker : ψ.ker ≤ Subgroup.center L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : G} (hy : y ^ p = 1)
    (hinner : ∃ g ∈ ψ.range, y * g ∈ Subgroup.centralizer (ψ.range : Set G))
    {C : Subgroup G} (hC : IsComponentOf C (ψ.range ⊓ Subgroup.centralizer {y})) :
    GGNotExcThreeOrder (ggCQ C) := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
    exact hker
  obtain ⟨g, ⟨l, rfl⟩, hcg⟩ := hinner
  have hact : ∀ u : L, y * ψ u * y⁻¹ = ψ (l⁻¹ * u * l) := by
    intro u
    have h := Subgroup.mem_centralizer_iff.mp hcg (ψ (l⁻¹ * u * l)) ⟨_, rfl⟩
    have h2 : ψ (l⁻¹ * u * l) * (y * ψ l) = y * ψ u * ψ l := by
      rw [h, mul_assoc y (ψ l), ← map_mul, show l * (l⁻¹ * u * l) = u * l by group, map_mul,
        ← mul_assoc]
    calc y * ψ u * y⁻¹ = y * ψ u * ψ l * (ψ l)⁻¹ * y⁻¹ := by group
      _ = ψ (l⁻¹ * u * l) * (y * ψ l) * (ψ l)⁻¹ * y⁻¹ := by rw [h2]
      _ = ψ (l⁻¹ * u * l) := by group
  have hactk : ∀ k : ℕ, ∀ u : L, y ^ k * ψ u * (y ^ k)⁻¹ = ψ (l⁻¹ ^ k * u * (l⁻¹ ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      calc y ^ (k + 1) * ψ u * (y ^ (k + 1))⁻¹ = y ^ k * (y * ψ u * y⁻¹) * (y ^ k)⁻¹ := by
            rw [pow_succ]; group
        _ = ψ (l⁻¹ ^ k * (l⁻¹ * u * l) * (l⁻¹ ^ k)⁻¹) := by rw [hact, ih]
        _ = ψ (l⁻¹ ^ (k + 1) * u * (l⁻¹ ^ (k + 1))⁻¹) := by
            congr 1
            rw [pow_succ]
            group
  have hsp : l⁻¹ ^ p = 1 := by
    have hz : l⁻¹ ^ p ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h1 := hactk p u
      rw [hy, one_mul, inv_one, mul_one] at h1
      have h2 := hinj h1
      calc u * l⁻¹ ^ p = l⁻¹ ^ p * u * (l⁻¹ ^ p)⁻¹ * l⁻¹ ^ p := by rw [← h2]
        _ = l⁻¹ ^ p * u := by group
    rwa [hZL, Subgroup.mem_bot] at hz
  have hH : ψ.range ⊓ Subgroup.centralizer {y} =
      (Subgroup.centralizer ({l⁻¹} : Set L)).map ψ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
      refine ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      have h1 : y * ψ u * y⁻¹ = ψ u := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hu]
        group
      have h2 := hinj ((hact u).symm.trans h1)
      calc u * l⁻¹ = l⁻¹ * u * l * l⁻¹ := by rw [h2]
        _ = l⁻¹ * u := by group
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : l⁻¹ * u * l = u := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hu]
        group
      have h2 := hact u
      rw [h1] at h2
      calc ψ u * y = y * ψ u * y⁻¹ * y := by rw [h2]
        _ = y * ψ u := by group
  rw [hH] at hC
  have hCr : C ≤ ψ.range := hC.1.trans (Subgroup.map_le_range ψ _)
  have h1 := hL p hp hp2 l⁻¹ hsp _ (TagsExc.isComponentOf_comap ψ hinj hC)
  rwa [ggCQ_comap_of_injective ψ hinj hCr] at h1

theorem TagsExc.four_le_card_galoisField {f : ℕ} (hf : 2 ≤ f) :
    4 ≤ Nat.card (GaloisField 2 f) :=
  CFSG.StandardType.LayerExcThree.ggAKFG_four_le_card_galoisField hf

section Tags

theorem ggLayerNotExcThreeTag_F4_of_cent
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      GGCentCompNotExcThree ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 K)) :
    GGLayerNotExcThreeTag .F4 := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact ggNotExcThree_of_isComponentOf_inner
    (L := ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f)))
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (h _ (TagsExc.four_le_card_galoisField hf)) hker hp hp2 hy
    (PsiDiag.Adj.exists_mem_centralizer_F4 ψ hker hdiag) hC

theorem ggLayerNotExcThreeTag_E8_of_cent
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      GGCentCompNotExcThree ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 K)) :
    GGLayerNotExcThreeTag .E8 := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact ggNotExcThree_of_isComponentOf_inner
    (L := ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)))
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (h _ (TagsExc.four_le_card_galoisField hf)) hker hp hp2 hy
    (PsiDiag.Adj.exists_mem_centralizer_E8 ψ hker hdiag) hC

theorem ggLayerNotExcThreeTag_E7_of_cent
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      GGCentCompNotExcThree ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K)) :
    GGLayerNotExcThreeTag .E7 := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  exact ggNotExcThree_of_isComponentOf_inner
    (L := ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f)))
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
    (ggCentCompNotExcThree_of_mulEquiv
      (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f))
      (h _ (TagsExc.four_le_card_galoisField hf))) hker hp hp2 hy
    (PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker hdiag) hC

end Tags

end CFSG.StandardType
