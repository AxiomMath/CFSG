module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Common
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row17Model
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4bGlue
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row17M3b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7
  CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam
  CFSG.Quasithin.A312M24
open scoped commutatorElement

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCore_le_Qbar {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (h : MS93.IsC134Case4Corr G₀ R L) :
    ⁅(CFSG.pCore 2 ↥(modO2Image H L)).map (modO2Image H L).subtype, modO2Image H L⁆ ≤
      Stellmacher.PU.L3YC.Qbar H G₀ L := by
  rw [commutator_pCore_map_eq, Stellmacher.PU.L3YC.Qbar_eq_map hLH hLG hGL]
  refine Subgroup.map_mono ?_
  set π := Stellmacher.PU.L3YC.toModO2Image hLH with hπ
  have hπs := Stellmacher.PU.L3YC.toModO2Image_surjective hLH
  have hK := Stellmacher.PU.L3YC.isPGroup_ker_toModO2Image hLH
  calc ⁅CFSG.pCore 2 ↥(modO2Image H L), (⊤ : Subgroup ↥(modO2Image H L))⁆
      ≤ ⁅(CFSG.pCore 2 ↥L).map π, (⊤ : Subgroup ↥(modO2Image H L))⁆ :=
        Subgroup.commutator_mono (Stellmacher.PU.L3YC.pCore_le_map π hπs hK) le_rfl
    _ = (⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆).map π := by
        rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπs]
    _ ≤ ((c134Q G₀ L).subgroupOf L).map π :=
        Subgroup.map_mono (Stellmacher.PU.L3YC.commutator_pCore_le_subgroupOf hLG hGL h)

section Embed


theorem extraspecial_quotient_of_embed {X : Type} [Group X] {Lb K : Subgroup X} (hLbK : Lb ≤ K)
    (ψ : ↥K ≃* ↥J) {B : Subgroup ↥J} (hB : B = (Lb.subgroupOf K).map (ψ : ↥K →* ↥J))
    (hBle : B ≤ Hj)
    (hext : IsExt ↥((fHj.comp (Subgroup.inclusion hBle)).range)
      (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y)) :
    ∃ (X' : Type) (_ : Group X') (_ : Finite X') (φ : ↥Lb →* X'), Function.Surjective φ ∧
      IsPGroup 2 φ.ker ∧ CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 X') ∧
        Nat.card (CFSG.pCore 2 X') = 2 ^ 7 := by
  have hθk := isPGroup_ker_theta hBle
  generalize fHj.comp (Subgroup.inclusion hBle) = θ at hext hθk
  obtain ⟨hVe, hV7⟩ := pCore_of_isExt_extraspecial hext
  obtain ⟨φ, hφs, hφk⟩ := exists_surj_ker_pGroup_of_embed hLbK (ψ : ↥K →* ↥J) ψ.injective hB θ hθk
  refine ⟨↥θ.range, inferInstance, inferInstance, φ, hφs, hφk, ?_, ?_⟩
  · exact hVe
  · exact hV7

end Embed

theorem row17_false_of_m3 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    (hS : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)))
    {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hrow : IsSporadic .J4 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁))
    (hM3 : ∀ B : Subgroup J, ⁅B, B⁆ = B → P0 ≤ Subgroup.normalizer (B : Set J) →
      B ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) → IsPSL 3 2 1 (ModO2 B) →
      ∃ ω : J, Stellmacher.PU.L3YC.M24.Row14Conc B ω) : False := by
  classical
  set H : Subgroup G := Subgroup.centralizer ({c₀} : Set G) with hHdef
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ H := by
    intro l hl
    rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  let mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L₁ with hKdef
  set Lb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L with hLbdef
  have hKn : K.Normal := Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbK : Lb ≤ K := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hperfb : ⁅Lb, Lb⁆ = Lb := by
    have h1 : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLH, hperf]
    rw [hLbdef]
    unfold modO2Image
    rw [← Subgroup.map_commutator, h1]
  set Sb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((Sgp153 T V₁).subgroupOf H).map mk with hSbdef
  have hSb : IsSylowTwoOf Sb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS) mk
      (QuotientGroup.mk'_surjective _)
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    Row18.bar_le_normalizer hSL
  have hS₀ : IsSylowTwoOf (Sb ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hSb le_top (by rw [Subgroup.normalizer_eq_top (H := K)])
  have h3 : IsPSL 3 2 1 (ModO2 Lb) := CD.L3YC.isPSL_modO2_modO2Image hLH hq
  obtain ⟨e⟩ := hrow
  have hS' : IsSylowTwoOf ((Sb ⊓ K).subgroupOf K) ⊤ := isSylowTwoOf_top_subgroupOf hS₀
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.J4Loc.sylow_transport (Γ := J)
    CFSG.Quasithin.J4Loc.isSylowTwoOf_P0 (e.trans (seedEquiv j4Facts.mat)) hS'
  set Lk : Subgroup ↥K := Lb.subgroupOf K with hLk
  set B : Subgroup J := Lk.map (ψ : ↥K →* ↥J) with hBdef
  have hmapLk : Lk.map K.subtype = Lb := Subgroup.map_subgroupOf_eq_of_le hLbK
  have hLkperf : ⁅Lk, Lk⁆ = Lk := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hmapLk, hperfb]
  have hBperf : ⁅B, B⁆ = B := by rw [hBdef, ← Subgroup.map_commutator, hLkperf]
  have hSk : (Sb ⊓ K).subgroupOf K ≤ Subgroup.normalizer (Lk : Set ↥K) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hsb : (s : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Sb :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)).1
    have := Subgroup.mem_normalizer_iff.mp (hSbL hsb) (y : ↥H ⧸ CFSG.pCore 2 ↥H)
    simpa [hLk, Subgroup.mem_subgroupOf] using this
  have hNB : P0 ≤ Subgroup.normalizer (B : Set J) := by
    rw [← hψ]
    exact (Subgroup.map_mono hSk).trans (Subgroup.le_normalizer_map (ψ : ↥K →* ↥J))
  have hPSLB : IsPSL 3 2 1 (ModO2 B) := by
    obtain ⟨e1⟩ := nonempty_modO2_equiv_of_eq hmapLk
    have h1 : IsPSL 3 2 1 (ModO2 (Lk.map K.subtype)) := IsPSL.of_mulEquiv e1.symm h3
    exact isPSL_modO2_map (ψ : ↥K →* ↥J) ψ.injective Lk
      (isPSL_modO2_of_map K.subtype K.subtype_injective Lk h1)
  have hLG : L ≤ L ⊔ Sgp153 T V₁ := le_sup_left
  have hGL : L ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := CD.L3YC.sup_le_normalizer hSL
  rcases row17_J hM3 hBperf hNB hPSLB with ⟨ω, hω⟩ | ⟨hBle, hext⟩
  ·
    let ι₁ : J →* (↥H ⧸ CFSG.pCore 2 ↥H) := K.subtype.comp ψ.symm.toMonoidHom
    have hι₁ : Function.Injective ι₁ := K.subtype_injective.comp ψ.symm.injective
    have hmap : B.map ι₁ = Lb := by
      rw [hBdef, Subgroup.map_map]
      have : ι₁.comp (ψ : ↥K →* ↥J) = K.subtype := by ext x; simp [ι₁]
      rw [this, hmapLk]
    have hωc := Row17Conc.map ι₁ hι₁ hω
    rw [hmap] at hωc
    obtain ⟨hωN, hω3, hωq⟩ := hωc
    obtain ⟨b, hb, hbq⟩ := corN1 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hc₀ hc₀1 rfl
      hS (m := 1) (by simpa using hω3) hωN
    obtain ⟨q, hq', hne⟩ := hωq b hb
    exact hne (hbq q (commutator_pCore_le_Qbar hLH hLG hGL h4 hq'))
  ·
    obtain ⟨X', _, _, φ, hφs, hφk, hVe, hV7⟩ :=
      extraspecial_quotient_of_embed hLbK ψ hBdef hBle hext
    exact Stellmacher.PU.L3YC.classII_false hLG hGL hq hperf h4
      (φ.comp (Stellmacher.PU.L3YC.toModO2Image hLH))
      (hφs.comp (Stellmacher.PU.L3YC.toModO2Image_surjective hLH))
      (CFSG.Quasithin.J4Fam.isPGroup_ker_comp _ _
        (Stellmacher.PU.L3YC.isPGroup_ker_toModO2Image hLH) hφk) hVe hV7

theorem row17_false [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    (hS : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)))
    {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hrow : IsSporadic .J4 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)) : False :=
  row17_false_of_m3 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hc₀ hc₀1 hS hLL₁ hN hrow
    fun _ hBp hBN hBM hBq => CFSG.Quasithin.Stellmacher.CD.L3YC.R17.m3_row14conc hBp hBN hBM hBq

end Stellmacher.L3YC

end CFSG.Quasithin
