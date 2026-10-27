module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Common
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Glue
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4bGlue

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem row14_false [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
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
    (hrow : IsExt ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
        (fun V _ => IsE2 6 V) (fun Y' _ => IsPSL 3 2 1 Y') ∧
      IsSporadic .M24 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)) : False := by
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
  obtain ⟨ω, -, hωN, hω3, hωq, hC⟩ :=
    Stellmacher.PU.L3YC.M24.row14_M24 hrow.2 hLbK hS₀ (inf_le_left.trans hSbL) hperfb hrow.1
  have hQ := Stellmacher.PU.L3YC.Qbar_eq_pCore hLH le_sup_left (CD.L3YC.sup_le_normalizer hSL) hq
    hperf h4 hC
  obtain ⟨b, hb, hbq⟩ := corN1 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hc₀ hc₀1 rfl hS
    (m := 1) (by simpa using hω3) hωN
  obtain ⟨q, hq', hne⟩ := hωq b hb
  exact hne (hbq q (hQ ▸ hq'))

end Stellmacher.L3YC

end CFSG.Quasithin
