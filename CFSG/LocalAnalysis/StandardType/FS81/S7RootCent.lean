module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.E7RecogL3
import CFSG.LocalAnalysis.StandardType.FS81.S7CharTwoModData
import CFSG.LocalAnalysis.StandardType.FS81.S7DataMap
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.StandardType.FS81.S7E7RadicalCent
import CFSG.LocalAnalysis.StandardType.FS81.S7E7RecogSup
import CFSG.LocalAnalysis.StandardType.FS81.S7HighRadicalComm
import CFSG.LocalAnalysis.StandardType.FS81.S7MemSupConj
import CFSG.LocalAnalysis.StandardType.FS81.S7ModuleFaithful
import CFSG.LocalAnalysis.StandardType.FS81.S7ModuleTrivial
import CFSG.LocalAnalysis.StandardType.FS81.S7PCoreCentEmb
import CFSG.LocalAnalysis.StandardType.FS81.S7RootEmbE7
import CFSG.LocalAnalysis.StandardType.FS81.S7RootEmbTwD7
import CFSG.LocalAnalysis.StandardType.FS81.S7RootSL2
import CFSG.LocalAnalysis.StandardType.FS81.S7SylowCentralMap

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)
local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)

private theorem map_conj_eq_of_mem_normalizer {M : Type} [Group M] {H : Subgroup M} {c : M}
    (hc : c ∈ Subgroup.normalizer (H : Set M)) : H.map (MulAut.conj c).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hc

private theorem pinnedElt_highRoot_E7_mem_highRadical :
    s₇ ∈ Q₇ := by
  have hθ : highRoot .E7 ∈ parabolicRadicalRoots .E7 (EPilot.perpNodes .E7) :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).2
      ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)

section E7Model


private theorem e7_data_model_highRoot (r : ↥(adjointGroup .E7 (ZMod 2)))
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hr3 : orderOf r = 3) :
    ∃ (b : ↥(adjointGroup .E7 (ZMod 2))) (P J D : Subgroup ↥(adjointGroup .E7 (ZMod 2)))
      (g : ↥(adjointGroup .E7 (ZMod 2))),
      g * r * g⁻¹ = b ∧
      E7LeviData (⊤ : Subgroup ↥(adjointGroup .E7 (ZMod 2))) s₇ b P J D ∧
      E7ModuleData Qθ tθ (e7Incl s₇) Dθ (P.map e7Incl) := by
  obtain ⟨hC, hLQ, -, -⟩ := KGExc.centralizer_decomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl))
    E7Pilot.isQuasisimple_perpLevi_E7 E7Pilot.center_perpLevi_E7_eq_bot
  have hQ2 : IsPGroup 2 Q₇ :=
    (EPilot.isTwoRadicalDecomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl)) one_ne_zero).1
  obtain ⟨-, D, hJD, hDJ, hDsl⟩ := e7ModelL3_holds
  obtain ⟨g, hg⟩ := e7ModelConj_holds
  have hrJ : r ∈ e7JTheta := Subgroup.mem_subgroupOf.2 hr
  have hbJ : g * r * g⁻¹ ∈ e7JThetaD6 := by
    rw [← hg]
    exact Subgroup.mem_map.2 ⟨r, hrJ, by simp [MulAut.conj_apply]⟩
  have hb3 : orderOf (g * r * g⁻¹) = 3 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective r
    simpa [MulAut.conj_apply, hr3] using this
  have hQC : Q₇ ≤ Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [hC]
    exact le_sup_left
  have hJC : EPilot.perpLevi .E7 (ZMod 2) ≤
      Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [hC]
    exact le_sup_right
  refine ⟨g * r * g⁻¹, Q₇, EPilot.perpLevi .E7 (ZMod 2), D, g, rfl, ?_, ?_⟩
  · refine ⟨pinnedElt_highRoot_E7_mem_highRadical, le_top, hQ2,
      commutator_highRadical_le_zpowers (τ := .E7) (K := ZMod 2) (Or.inl rfl) (Nat.card_zmod 2),
      fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hQC hx),
      fun x _ hx => mem_zpowers_of_centralizes_highRadical_E7 x hx, le_top,
      fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hJC hx), hDJ, hDJ.trans hLQ, hDsl,
      hJD hbJ, hb3⟩
  · refine ⟨pinnedElt_highRoot_mem_highRadical,
      commutator_highRadical_le_zpowers (τ := .E8) (K := GF₂) (Or.inr rfl)
        natCard_galoisField_two_one,
      highRadical_E7_trivial_on_modW, ?_⟩
    intro x hx hxσ hxW
    exact mem_map_highRadical_E7_of_trivial_on_modW x hx hxσ hxW

theorem exists_e7_data_model (s r : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2)
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hr3 : orderOf r = 3) :
    ∃ (b : ↥(adjointGroup .E7 (ZMod 2))) (P J D : Subgroup ↥(adjointGroup .E7 (ZMod 2)))
      (g : ↥(adjointGroup .E7 (ZMod 2))),
      g * r * g⁻¹ = b ∧
      E7LeviData (⊤ : Subgroup ↥(adjointGroup .E7 (ZMod 2))) s b P J D ∧
      E7ModuleData Qθ tθ (e7Incl s) Dθ (P.map e7Incl) := by
  obtain ⟨h, -, hhs⟩ := exists_conj_pinnedElt_of_mem_highRootSL2 s hs hs2
  obtain ⟨b₀, P₀, J₀, D₀, g₀, hg₀, hlev₀, hmod₀⟩ := e7_data_model_highRoot r hr hr3
  have hφs : (MulAut.conj h).toMonoidHom s₇ = s := by simpa [MulAut.conj_apply] using hhs
  have hlev := E7LeviData.map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective hlev₀
  have hsurj : Function.Surjective (MulAut.conj h).toMonoidHom := (MulAut.conj h).surjective
  rw [Subgroup.map_top_of_surjective _ hsurj, hφs] at hlev
  have hcD : e7Incl h ∈ Dθ := by
    rw [← range_e7Incl]
    exact ⟨h, rfl⟩
  obtain ⟨hC, hLQ, -, -, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := GF₂)
  have hcQ : e7Incl h ∈ Subgroup.normalizer (Qθ : Set ↥(adjointGroup .E8 GF₂)) := hLQ hcD
  have hcC : e7Incl h ∈ Subgroup.centralizer ({tθ} : Set ↥(adjointGroup .E8 GF₂)) := by
    rw [hC]
    exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) hcD
  have hmod := E7ModuleData.map (MulAut.conj (e7Incl h)).toMonoidHom
    (MulAut.conj (e7Incl h)).injective hmod₀
  rw [map_conj_eq_of_mem_normalizer hcQ, map_conj_eq_of_mem_normalizer
    (Subgroup.le_normalizer hcD)] at hmod
  have ht : (MulAut.conj (e7Incl h)).toMonoidHom tθ = tθ := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hcC
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hσ : (MulAut.conj (e7Incl h)).toMonoidHom (e7Incl s₇) = e7Incl s := by
    rw [← hφs]
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hP : ((P₀.map e7Incl).map (MulAut.conj (e7Incl h)).toMonoidHom) =
      (P₀.map (MulAut.conj h).toMonoidHom).map e7Incl := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [ht, hσ, hP] at hmod
  refine ⟨(MulAut.conj h).toMonoidHom b₀, P₀.map (MulAut.conj h).toMonoidHom,
    J₀.map (MulAut.conj h).toMonoidHom, D₀.map (MulAut.conj h).toMonoidHom, h * g₀, ?_, hlev,
    hmod⟩
  rw [← hg₀]
  show h * g₀ * r * (h * g₀)⁻¹ = h * (g₀ * r * g₀⁻¹) * h⁻¹
  group

theorem map_perpLevi_le_centralizer {G : Type} [Group G] (ι : adjointGroup .E8 GF₂ →* G) :
    (Dθ).map ι ≤ Subgroup.centralizer ({ι tθ} : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subgroup.centralizer ({tθ} : Set ↥(adjointGroup .E8 GF₂)) := by
    rw [(centralizer_pinnedElt_highRoot_E8 (K := GF₂)).1]
    exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx' tθ rfl]

theorem charTwoMod_of_embedding {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} {b : G} (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι)
    (hrange : ι.range = Y) (hb : ι sθ = b) (hCb : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    [(((Qθ).map ι).subgroupOf (Subgroup.centralizer ({ι tθ} : Set G))).Normal]
    (hU : IsPGroup 2 ((Qθ).map ι)) (hUH : (Qθ).map ι ≤ Subgroup.centralizer ({ι tθ} : Set G))
    (hφH : ∀ x, ι (e7Incl x) ∈ Subgroup.centralizer ({ι tθ} : Set G))
    (s : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2) :
    CharTwoMod (Subgroup.centralizer ({ι tθ} : Set G)) ((Qθ).map ι) ⟨ι (e7Incl s), hφH s⟩ := by
  obtain ⟨r, hr, hr3⟩ := exists_mem_highRootSL2_orderOf_three
  obtain ⟨b', P, J, D, g, hgb, hlev, hmod⟩ := exists_e7_data_model s r hs hs2 hr hr3
  obtain ⟨-, -, hdisj, -, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := GF₂)
  have hLU : ∀ x ∈ (Dθ).map ι, x ∈ (Qθ).map ι → x = 1 := by
    rintro _ ⟨d, hd, rfl⟩ ⟨q, hq, hqd⟩
    have h1 : d = 1 := (Subgroup.disjoint_def.mp hdisj) (hι hqd ▸ hq) hd
    rw [h1, map_one]
  have ht₀H : ∀ h ∈ Subgroup.centralizer ({ι tθ} : Set G), h * ι tθ = ι tθ * h := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp hh (ι tθ) rfl).symm
  have hL : (⊤ : Subgroup ↥(adjointGroup .E7 (ZMod 2))).map (ι.comp e7Incl) = (Dθ).map ι := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, range_e7Incl]
  have hlev' := E7LeviData.map (ι.comp e7Incl) (hι.comp e7Incl_injective) hlev
  rw [hL] at hlev'
  have hmod' := E7ModuleData.map ι hι hmod
  simp only [Subgroup.map_map] at hmod'
  have hmem : ∀ x ∈ Subgroup.centralizer ({ι tθ} : Set G),
      x * (ι.comp e7Incl) b' * x⁻¹ ∈ (Dθ).map ι ⊔ (Qθ).map ι → x ∈ (Dθ).map ι ⊔ (Qθ).map ι := by
    intro x hx hxb
    refine mem_sup_of_conj_mem_embedding ι hι hrange hb hCb hfus (z := b') ?_ hx hxb
    obtain ⟨m, hm⟩ := exists_conj_rootThree_e7Incl r hr hr3
    refine ⟨m * (e7Incl g)⁻¹, ?_⟩
    subst hgb
    rw [map_mul, map_mul, map_inv]
    calc m * (e7Incl g)⁻¹ * (e7Incl g * e7Incl r * (e7Incl g)⁻¹) * (m * (e7Incl g)⁻¹)⁻¹
        = m * e7Incl r * m⁻¹ := by group
      _ = sθ := hm
  exact charTwoMod_of_data hUH hU (map_perpLevi_le_centralizer ι) hLU ht₀H hlev' hmod' hmem

end E7Model

section Row


theorem exists_rootEmbedding {G : Type} [Group G] [Finite G] {r : Row}
    (hr : r = Row.E7 ∨ r = Row.twD7) {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)}
    {Y : Subgroup G} (h : RootSetting r b₀ K E B Y) :
    ∃ ι : adjointGroup .E8 GF₂ →* G, Function.Injective ι ∧ ι.range = Y ∧
      ι sθ = rowRootElt r B b₀ ∧ s79A r B ≤ (Dθ).map ι := by
  rcases hr with rfl | rfl
  · exact exists_rootEmbedding_E7 h
  · exact exists_rootEmbedding_twD7 h

end Row

section Assembly


theorem centralizer_le_of_embedding (hRec : E7RootRecog)
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} {b : G}
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) (hrange : ι.range = Y)
    (hb : ι sθ = b) (hCb : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    (hU : pCoreOf 2 (Subgroup.centralizer ({ι tθ} : Set G)) = (Qθ).map ι) :
    Subgroup.centralizer ({ι tθ} : Set G) ≤ Y := by
  obtain ⟨r, hr, hr3⟩ := exists_mem_highRootSL2_orderOf_three
  obtain ⟨-, -, hdisj, hQ2, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := GF₂)
  have hDH := map_perpLevi_le_centralizer ι
  have hUH : (Qθ).map ι ≤ Subgroup.centralizer ({ι tθ} : Set G) := by
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hN : (((Qθ).map ι).subgroupOf (Subgroup.centralizer ({ι tθ} : Set G))).Normal := by
    rw [← hU]
    have hpc : (pCoreOf 2 (Subgroup.centralizer ({ι tθ} : Set G))).subgroupOf
        (Subgroup.centralizer ({ι tθ} : Set G)) =
        pCore 2 (Subgroup.centralizer ({ι tθ} : Set G)) :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    rw [hpc]
    infer_instance
  have hmemD : ∀ x, e7Incl x ∈ Dθ := fun x => by
    rw [← range_e7Incl]
    exact ⟨x, rfl⟩
  have hφH : ∀ x, ι (e7Incl x) ∈ Subgroup.centralizer ({ι tθ} : Set G) := fun x =>
    hDH ⟨e7Incl x, hmemD x, rfl⟩
  have hφN : ∀ x, (ι.comp e7Incl) x ∈ (Qθ).map ι → x = 1 := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hx
    have h1 : q = e7Incl x := hι hqx
    have h3 : e7Incl x = 1 := (Subgroup.disjoint_def.mp hdisj) (h1 ▸ hq) (hmemD x)
    exact e7Incl_injective (h3.trans (map_one e7Incl).symm)
  have hrangeφ : (ι.comp e7Incl).range = (Dθ).map ι := by
    rw [MonoidHom.range_comp, range_e7Incl]
  have hmem : ∀ g ∈ Subgroup.centralizer ({ι tθ} : Set G),
      g * (ι.comp e7Incl) r * g⁻¹ ∈ (ι.comp e7Incl).range ⊔ (Qθ).map ι →
      g ∈ (ι.comp e7Incl).range ⊔ (Qθ).map ι := by
    intro g hg hgr
    rw [hrangeφ] at hgr ⊢
    exact mem_sup_of_conj_mem_embedding ι hι hrange hb hCb hfus
      (exists_conj_rootThree_e7Incl r hr hr3) hg hgr
  have hchar : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) → orderOf s = 2 →
      CharTwoMod (Subgroup.centralizer ({ι tθ} : Set G)) ((Qθ).map ι)
        ⟨(ι.comp e7Incl) s, hφH s⟩ := fun s hs hs2 =>
    charTwoMod_of_embedding ι hι hrange hb hCb hfus ((isPGroup_map_iff ι hι 2 Qθ).2 hQ2) hUH hφH
      s hs hs2
  refine (le_sup_of_e7RootRecog hRec _ ((Qθ).map ι) hUH (ι.comp e7Incl) hφH hφN r hr hr3 hmem
    hchar).trans (sup_le ?_ ?_)
  · rw [hrangeφ, ← hrange]
    exact Subgroup.map_le_range ι _
  · rw [← hrange]
    exact Subgroup.map_le_range ι _

theorem e8RootCentAt_of_recog (hRec : E7RootRecog) {r : Row}
    (hr : r = Row.E7 ∨ r = Row.twD7) : E8RootCentAt r := by
  intro G _ _ b₀ K E B Y h hC _ hCb hfusb
  obtain ⟨ι, hι, hrange, hb, hA⟩ := exists_rootEmbedding hr h
  have hU := pCoreOf_centralizer_eq_of_embedding hr h hC ι hι hrange hA
  have hY := centralizer_le_of_embedding hRec ι hι hrange hb hCb hfusb hU
  obtain ⟨S, hS, htS, ht2, htc⟩ := exists_sylow_central_map ι hι
  exact ⟨S, ι tθ, by rw [← hrange]; exact hS, htS, ht2, htc, hY⟩

theorem e8RootCentAt_E7_of_recog (hRec : E7RootRecog) :
    E8RootCentAt Row.E7 :=
  e8RootCentAt_of_recog hRec (Or.inl rfl)

theorem e8RootCentAt_twD7_of_recog (hRec : E7RootRecog) :
    E8RootCentAt Row.twD7 :=
  e8RootCentAt_of_recog hRec (Or.inr rfl)

end Assembly

end CFSG.StandardType.FrameRoute.FS81

end
