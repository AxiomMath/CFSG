module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace LayerPDiv

open LayerCores LayerFacts

variable {n : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem exists_mem_ggConjPairs_sp [Finite F] [CharP F 2] (hn : 2 ≤ n) (ψ : StatedSp n F →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {y : G}
    (hy : GGPsiInnerDiag (Symplectic.rootDatum n F) ψ y) : ∃ t, (y, t) ∈ ggConjPairs ψ := by
  obtain ⟨g, ⟨s, rfl⟩, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer hn ψ hker hy
  refine ⟨s⁻¹, fun u => ?_⟩
  have h := Subgroup.mem_centralizer_iff.mp hcg (ψ (s⁻¹ * u * s)) ⟨_, rfl⟩
  have h2 : ψ (s⁻¹ * u * s) * y * ψ s = y * ψ u * ψ s := by
    calc ψ (s⁻¹ * u * s) * y * ψ s = ψ (s⁻¹ * u * s) * (y * ψ s) := by group
      _ = y * ψ s * ψ (s⁻¹ * u * s) := h
      _ = y * ψ (s * (s⁻¹ * u * s)) := by rw [map_mul ψ s]; group
      _ = y * ψ u * ψ s := by rw [show s * (s⁻¹ * u * s) = u * s by group, map_mul]; group
  rw [inv_inv]
  calc ψ (s⁻¹ * u * s) = ψ (s⁻¹ * u * s) * y * ψ s * (ψ s)⁻¹ * y⁻¹ := by group
    _ = y * ψ u * ψ s * (ψ s)⁻¹ * y⁻¹ := by rw [h2]
    _ = y * ψ u * y⁻¹ := by group

theorem dvd_card_of_isComponentOf_sp (hAltP : AltFactorPDivInput)
    (hHermP : HermFactorPDivInput) [Finite G] [Finite F] [CharP F 2] {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F ^ 2 - 1) {E : Subgroup G} (hE : IsPGroup p E)
    (hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ) {K : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) : p ∣ Nat.card K := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) n).le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  set A := ggConjLifts ψ E with hA
  have hAp : IsPGroup p A := by
    intro t
    obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp t.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (ggConjPairs ψ).pow_mem het (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    simpa using hZ1 _ h1
  have hH : ψ.range ⊓ Subgroup.centralizer (E : Set G) =
      (Subgroup.centralizer (A : Set (StatedSp n F))).map ψ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
      refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, rfl⟩
      obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp ht
      have h2 : e * ψ u * e⁻¹ = ψ u := by
        rw [Subgroup.mem_centralizer_iff.mp hu e he]
        group
      have h3 := hinj ((het u).trans h2)
      calc t * u = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [h3]
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      obtain ⟨t, het⟩ := hlift e he
      have htA : t ∈ A := mem_ggConjLifts.mpr ⟨e, he, het⟩
      have h1 := het u
      have h2 : t * u * t⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.mp hu t htA]
        group
      rw [h2] at h1
      calc e * ψ u = e * ψ u * e⁻¹ * e := by group
        _ = ψ u * e := by rw [← h1]
  obtain ⟨β, S, ⟨hSle, hSn, hSq, hder, -⟩, hdvd⟩ :=
    exists_coreFamily_sp_pDiv hAltP hHermP hp hp2 hpF hAp
  rw [hH] at hK
  obtain ⟨c, rfl⟩ := exists_eq_map_of_isComponentOf ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) S hSle hSn hSq
    hder hK
  rw [Subgroup.card_map_of_injective hinj]
  exact hdvd c

end LayerPDiv

section Tags

open LayerFacts in
theorem ggLayerPDivTag_PSp_of_factors (hAltP : LayerPDiv.AltFactorPDivInput)
    (hHermP : LayerPDiv.HermFactorPDivInput) : GGLayerPDivTag .PSp := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  rw [← hrange, ← ggCentralizer_zpowers_eq] at hK
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by have := hadm.2.1; omega)
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hdiag
  have hlift : ∀ e ∈ Subgroup.zpowers y, ∃ t, (e, t) ∈ ggConjPairs ψ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨t ^ k, (ggConjPairs ψ).zpow_mem ht k⟩
  exact LayerPDiv.dvd_card_of_isComponentOf_sp (F := GaloisField 2 f) hAltP hHermP hker hp hp2
    (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) (ggIsPGroup_zpowers_of_pow_eq_one hy)
    hlift hK

end Tags

end CFSG.StandardType
