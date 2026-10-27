module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

theorem shapeConj_mem_normalizer_conj_iff {G : Type} [Group G] {H : Subgroup G} {m c : G}
    (hm : m ∈ Subgroup.normalizer (H : Set G)) :
    m⁻¹ * c * m ∈ Subgroup.normalizer (H : Set G) ↔
      c ∈ Subgroup.normalizer (H : Set G) := by
  constructor
  · intro hc
    have h1 : m * (m⁻¹ * c * m) * m⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.mul_mem (Subgroup.normalizer (H : Set G))
        (Subgroup.mul_mem (Subgroup.normalizer (H : Set G)) hm hc)
        (Subgroup.inv_mem (Subgroup.normalizer (H : Set G)) hm)
    simpa [mul_assoc] using h1
  · intro hc
    exact Subgroup.mul_mem (Subgroup.normalizer (H : Set G))
      (Subgroup.mul_mem (Subgroup.normalizer (H : Set G))
        (Subgroup.inv_mem (Subgroup.normalizer (H : Set G)) hm) hc) hm

theorem shapeConj_range_comp {U : Type*} [Group U] {G : Type*} [Group G] {ψ : U →* G}
    {m : G} (hm : m ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ((MulAut.conj m).toMonoidHom.comp ψ).range = ψ.range := by
  rw [MonoidHom.range_comp]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hm

theorem shapeConj_ggPsiInnerDiag_conj {U : Type*} [Group U] (Δ : UniversalRootDatum U)
    {G : Type*} [Group G] {ψ : U →* G} {m c : G}
    (hm : m ∈ Subgroup.normalizer (ψ.range : Set G)) :
    GGPsiInnerDiag Δ ((MulAut.conj m).toMonoidHom.comp ψ) c ↔
      GGPsiInnerDiag Δ ψ (m⁻¹ * c * m) := by
  unfold GGPsiInnerDiag
  constructor
  · rintro ⟨g, hg, hroot⟩
    have hg0 : g ∈ ψ.range := by
      rw [shapeConj_range_comp hm] at hg
      exact hg
    have hg' : m⁻¹ * g * m ∈ ψ.range := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) g).mp hg0
      simpa only [inv_inv] using h1
    refine ⟨m⁻¹ * g * m, hg', fun γ hγ => ?_⟩
    obtain ⟨h, hh, hhroot⟩ := hroot γ hγ
    refine ⟨h, hh, fun z hz => ?_⟩
    have key := hhroot z hz
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at key
    calc (m⁻¹ * c * m * (m⁻¹ * g * m))⁻¹ * ψ z * (m⁻¹ * c * m * (m⁻¹ * g * m))
        = m⁻¹ * ((c * g)⁻¹ * (m * ψ z * m⁻¹) * (c * g)) * m := by group
      _ = m⁻¹ * (m * ψ (h * z * h⁻¹) * m⁻¹) * m := by rw [key]
      _ = ψ (h * z * h⁻¹) := by group
  · rintro ⟨g, hg, hroot⟩
    have hg' : m * g * m⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hm g).mp hg
    refine ⟨m * g * m⁻¹, by rwa [shapeConj_range_comp hm], fun γ hγ => ?_⟩
    obtain ⟨h, hh, hhroot⟩ := hroot γ hγ
    refine ⟨h, hh, fun z hz => ?_⟩
    have key := hhroot z hz
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at key ⊢
    calc (c * (m * g * m⁻¹))⁻¹ * (m * ψ z * m⁻¹) * (c * (m * g * m⁻¹))
        = m * ((m⁻¹ * c * m * g)⁻¹ * ψ z * (m⁻¹ * c * m * g)) * m⁻¹ := by group
      _ = m * ψ (h * z * h⁻¹) * m⁻¹ := by rw [key]

theorem shapeConj_ggG1_comp_conj
    {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G} {m : G}
    (hm : m ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ggG1 ((MulAut.conj m).toMonoidHom.comp ψ) =
      (ggG1 ψ).map (MulAut.conj m).toMonoidHom := by
  have hrange := shapeConj_range_comp hm
  ext c
  constructor
  · rintro ⟨hcN, hcD⟩
    have hcN' : m⁻¹ * c * m ∈ Subgroup.normalizer (ψ.range : Set G) := by
      rw [hrange] at hcN
      exact (shapeConj_mem_normalizer_conj_iff (H := ψ.range) hm).mpr hcN
    have hcD' : GGPsiInnerDiag (ggU t n f).D ψ (m⁻¹ * c * m) :=
      (shapeConj_ggPsiInnerDiag_conj (ggU t n f).D hm).mp hcD
    exact ⟨m⁻¹ * c * m, ⟨hcN', hcD'⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  · rintro ⟨d, hd, rfl⟩
    have hdN : m * d * m⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) := by
      simpa only [inv_inv] using
        (shapeConj_mem_normalizer_conj_iff (H := ψ.range) (Subgroup.inv_mem _ hm)).mpr hd.1
    have hdD : GGPsiInnerDiag (ggU t n f).D ψ (m⁻¹ * (m * d * m⁻¹) * m) := by
      rw [show m⁻¹ * (m * d * m⁻¹) * m = d by group]
      exact hd.2
    refine ⟨?_, (shapeConj_ggPsiInnerDiag_conj (ggU t n f).D hm).mpr hdD⟩
    rwa [shapeConj_range_comp hm]

theorem shapeConj_ggTransvection_map_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    (a g : G) :
    GGTransvection p (Bs.map (MulAut.conj g).toMonoidHom) (g * a * g⁻¹) ↔
      GGTransvection p Bs a := by
  unfold GGTransvection
  have hcomm : (⁅Bs.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (g * a * g⁻¹)⁆ :
      Subgroup G) = (⁅Bs, Subgroup.zpowers a⁆ : Subgroup G).map
        (MulAut.conj g).toMonoidHom := by
    rw [show Subgroup.zpowers (g * a * g⁻¹) =
        (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
    rw [← Subgroup.map_commutator]
  have hcent : Subgroup.centralizer ({g * a * g⁻¹} : Set G) =
      (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom :=
    (CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g a).symm
  rw [hcomm, hcent, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    map_conj_le_map_conj_iff]

theorem shapeConj_ggControlsStrongFusion_map_conj {G : Type} [Group G] {H E : Subgroup G}
    (g : G) :
    GGControlsStrongFusion (H.map (MulAut.conj g).toMonoidHom)
      (E.map (MulAut.conj g).toMonoidHom) ↔ GGControlsStrongFusion H E := by
  have key : ∀ y : G, (E.map (MulAut.conj y⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (E.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (g * y * g⁻¹)⁻¹).toMonoidHom := by
    intro y
    rw [map_conj_map_conj, map_conj_map_conj]
    congr 1
    group
  have key' : ∀ x : G, (E.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom =
      (E.map (MulAut.conj (g⁻¹ * x * g)⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
    intro x
    rw [map_conj_map_conj, map_conj_map_conj]
    congr 1
    group
  constructor
  · rintro ⟨hle, h⟩
    refine ⟨(map_conj_le_map_conj_iff g).mp hle, ?_⟩
    intro y hy
    have hy0 : (E.map (MulAut.conj y⁻¹).toMonoidHom ⊓ H).map
        (MulAut.conj g).toMonoidHom ≠ ⊥ := by
      intro hbot
      exact hy (Subgroup.map_eq_bot_iff_of_injective _
        (MulAut.conj g).injective |>.mp hbot)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, key y] at hy0
    have h3 := h (g * y * g⁻¹) hy0
    obtain ⟨h0, hh0, hh0eq⟩ := Subgroup.mem_map.mp h3
    have : h0 = y := (MulAut.conj g).injective (by simpa using hh0eq)
    simpa [this] using hh0
  · rintro ⟨hle, h⟩
    refine ⟨Subgroup.map_mono hle, ?_⟩
    intro x hx
    have hx' : E.map (MulAut.conj (g⁻¹ * x * g)⁻¹).toMonoidHom ⊓ H ≠ ⊥ := by
      rw [key' x, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at hx
      intro hbot
      exact hx (by rw [hbot, Subgroup.map_bot])
    have h3 := h (g⁻¹ * x * g) hx'
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, h3, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem shapeConj_map_normalizer {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    exact shapeConj_mem_normalizer_map_conj hb
  · intro b' hb'
    refine ⟨g⁻¹ * b' * g, ?_, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have h1 := shapeConj_mem_normalizer_map_conj
      (H := H.map (MulAut.conj g).toMonoidHom) (b := b') (g := g⁻¹) hb'
    rw [shapeConj_map_conj_inv_cancel H g] at h1
    simpa only [inv_inv, SetLike.mem_coe] using h1

theorem shapeConj_ker_comp {U : Type*} [Group U] {G : Type*} [Group G] (f : G →* G)
    (ψ : U →* G) (hf : Function.Injective f) : (f.comp ψ).ker = ψ.ker := by
  ext x
  constructor
  · intro hx
    exact hf (by simpa [MonoidHom.mem_ker] using hx)
  · intro hx
    simpa [MonoidHom.mem_ker] using congrArg f (MonoidHom.mem_ker.mp hx)

theorem shapeConj_ggG0_map_conj {G : Type} [Group G] [Finite G] (p : ℕ) {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (g : G) :
    ggG0 p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom)
      (D.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj g).toMonoidHom) =
      (ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom := by
  unfold ggG0
  simp only [Subgroup.map_sup, Subgroup.map_iSup]
  congr 1
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    have hS : LargeEvenSHat p B (g⁻¹ * y * g)
        (K.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have h1 := shapeConj_largeEvenSHat_map_conj h.1 g⁻¹
      have hy : g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g := by group
      rwa [shapeConj_map_conj_inv_cancel B g, hy] at h1
    have hN : LargeEvenNeighbor p x (g⁻¹ * y * g)
        (K.map (MulAut.conj g⁻¹).toMonoidHom) D J := by
      have h1 := shapeConj_largeEvenNeighbor_map_conj h.2 g⁻¹
      have hx : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      have hy : g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g := by group
      rwa [shapeConj_map_conj_inv_cancel D g, shapeConj_map_conj_inv_cancel J g, hx, hy] at h1
    refine le_iSup_of_le (g⁻¹ * y * g) (le_iSup_of_le (K.map (MulAut.conj g⁻¹).toMonoidHom)
      (le_iSup_of_le ⟨hS, hN⟩ ?_))
    exact le_of_eq (shapeConj_map_conj_inv_cancel' K g).symm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    have hS : LargeEvenSHat p (B.map (MulAut.conj g).toMonoidHom) (g * y * g⁻¹)
        (K.map (MulAut.conj g).toMonoidHom) :=
      shapeConj_largeEvenSHat_map_conj h.1 g
    have hN : LargeEvenNeighbor p (g * x * g⁻¹) (g * y * g⁻¹)
        (K.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
        (J.map (MulAut.conj g).toMonoidHom) :=
      shapeConj_largeEvenNeighbor_map_conj h.2 g
    refine le_iSup_of_le (g * y * g⁻¹) (le_iSup_of_le (K.map (MulAut.conj g).toMonoidHom)
      (le_iSup_of_le ⟨hS, hN⟩ ?_))
    rfl

theorem shapeConj_ggBstar_map_conj {G : Type} [Group G] {p : ℕ} {B Bs : Subgroup G} (g : G)
    (h : GGBstar p B Bs) : GGBstar p (B.map (MulAut.conj g).toMonoidHom)
      (Bs.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hle, hel, hcard, hmem⟩ := h
  refine ⟨Subgroup.map_mono hle, shapeConj_isElemAbelian_map_conj hel g, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  · intro x' hx' hxp
    have hx'' : x' ∈ (Subgroup.centralizer (Bs : Set G)).map
        (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x' * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff] at hx' ⊢
        intro b hb
        have hb' : g * b * g⁻¹ ∈ Bs.map (MulAut.conj g).toMonoidHom := ⟨b, hb, rfl⟩
        have hcomm := hx' _ hb'
        calc b * (g⁻¹ * x' * g) = g⁻¹ * ((g * b * g⁻¹) * x') * g := by group
          _ = g⁻¹ * (x' * (g * b * g⁻¹)) * g := by rw [hcomm]
          _ = (g⁻¹ * x' * g) * b := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    obtain ⟨x, hx, rfl⟩ := hx''
    refine ⟨x, hmem x hx ?_, rfl⟩
    have h2 : (MulAut.conj g) (x ^ p) = 1 := by
      rw [map_pow]
      exact hxp
    exact (MulAut.conj g).injective (by simpa using h2)

theorem shapeConj_ggPsiInnerDiag_map_conj {U : Type*} [Group U] (Δ : UniversalRootDatum U)
    {G : Type*} [Group G] {ψ : U →* G} {c g : G} (h : GGPsiInnerDiag Δ ψ c) :
    GGPsiInnerDiag Δ ((MulAut.conj g).toMonoidHom.comp ψ) (g * c * g⁻¹) := by
  obtain ⟨g₀, hg₀, hroot⟩ := h
  refine ⟨g * g₀ * g⁻¹, ?_, fun γ hγ => ?_⟩
  · rw [MonoidHom.range_comp]
    refine ⟨g₀, hg₀, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · obtain ⟨h, hh, hhroot⟩ := hroot γ hγ
    refine ⟨h, hh, fun z hz => ?_⟩
    have key := hhroot z hz
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at key ⊢
    calc (g * c * g⁻¹ * (g * g₀ * g⁻¹))⁻¹ * (g * ψ z * g⁻¹) * (g * c * g⁻¹ * (g * g₀ * g⁻¹))
        = g * ((c * g₀)⁻¹ * ψ z * (c * g₀)) * g⁻¹ := by group
      _ = g * ψ (h * z * h⁻¹) * g⁻¹ := by rw [key]

theorem shapeConj_ggThmIHyp_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L : Subgroup G} (g : G) (h : GGThmIHyp p B x L) :
    GGThmIHyp p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hS, hT⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, shapeConj_largeEvenSStar_map_conj hS g,
    shapeConj_largeEvenStandardType_map_conj hT g⟩

theorem shapeConj_ggSixHypV2Core_map_conj {G : Type} [Group G] [Finite G]
    {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} (g : G)
    (h : GGSixHypV2Core p B Bs x L D J Δ t n f ψ) :
    GGSixHypV2Core p (B.map (MulAut.conj g).toMonoidHom) (Bs.map (MulAut.conj g).toMonoidHom)
      (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (J.map (MulAut.conj g).toMonoidHom) Δ t n f ((MulAut.conj g).toMonoidHom.comp ψ) := by
  obtain ⟨hBstar, hstdSub, hadm, ⟨hrange, hker⟩, ⟨hperf, hlie⟩, ⟨hBsN, hPsi⟩, hNB, hNBs⟩ := h
  have hgg0 := shapeConj_ggG0_map_conj p (B := B) (x := x) (L := L) (D := D) (J := J) g
  refine ⟨shapeConj_ggBstar_map_conj g hBstar, shapeConj_largeEvenStdSub_map_conj hstdSub g,
    hadm, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange, hgg0]
  · exact shapeConj_ker_comp (MulAut.conj g).toMonoidHom ψ (MulAut.conj g).injective ▸ hker
  · have e := conjEquivMap (ggG0 p B x L D J) g
    have h1 : (commutator ↥(ggG0 p B x L D J)).map e.toMonoidHom =
        commutator ↥((ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom) := by
      rw [show commutator ↥(ggG0 p B x L D J) =
          ⁅(⊤ : Subgroup ↥(ggG0 p B x L D J)), ⊤⁆ from rfl,
        show commutator ↥((ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom) =
          ⁅(⊤ : Subgroup ↥((ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom)), ⊤⁆
          from rfl,
        Subgroup.map_commutator]
      congr 1 <;> exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
    rw [hgg0, ← h1, hperf, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · have e' : ↥(ggG0 p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
          (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
          (J.map (MulAut.conj g).toMonoidHom)) ≃*
        ↥((ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom) :=
      MulEquiv.subgroupCongr (G := G) hgg0
    exact LieModel.quotient_center_of_mulEquiv e'.symm
      (LieModel.quotient_center_of_mulEquiv (conjEquivMap (ggG0 p B x L D J) g) hlie)
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    have h1 := shapeConj_mem_normalizer_map_conj
      (H := ggG0 p B x L D J) (b := b) (g := g) (hBsN hb)
    rwa [← hgg0] at h1
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    exact shapeConj_ggPsiInnerDiag_map_conj Δ (hPsi b hb)
  · have h1 : Subgroup.normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (Subgroup.normalizer (B : Set G)).map (MulAut.conj g).toMonoidHom :=
      (shapeConj_map_normalizer B g).symm
    have h2 : Subgroup.normalizer
        ((ggG0 p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
          (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
          (J.map (MulAut.conj g).toMonoidHom) : Subgroup G) : Set G) =
        (Subgroup.normalizer (ggG0 p B x L D J : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [hgg0, shapeConj_map_normalizer]
    rw [h1, h2]
    exact Subgroup.map_mono hNB
  · have h1 : Subgroup.normalizer ((Bs.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (Subgroup.normalizer (Bs : Set G)).map (MulAut.conj g).toMonoidHom :=
      (shapeConj_map_normalizer Bs g).symm
    have h2 : Subgroup.normalizer
        ((ggG0 p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
          (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
          (J.map (MulAut.conj g).toMonoidHom) : Subgroup G) : Set G) =
        (Subgroup.normalizer (ggG0 p B x L D J : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [hgg0, shapeConj_map_normalizer]
    rw [h1, h2]
    exact Subgroup.map_mono hNBs
theorem shapeConj_ggM_map_conj {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} (g : G) :
    ggM p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom)
      (D.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj g).toMonoidHom) =
      (ggM p B x L D J).map (MulAut.conj g).toMonoidHom := by
  unfold ggM
  rw [shapeConj_ggG0_map_conj p (B := B) (x := x) (L := L) (D := D) (J := J) g]
  exact (shapeConj_map_normalizer (ggG0 p B x L D J) g).symm

end CFSG.StandardType
