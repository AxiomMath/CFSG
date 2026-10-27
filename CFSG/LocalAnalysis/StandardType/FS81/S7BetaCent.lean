module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7BetaCentGrp
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.RootE8A
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaACent
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaDataEmb
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaEllConj
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaEllMem
import CFSG.LocalAnalysis.StandardType.FS81.S7CentRootThree
import CFSG.LocalAnalysis.StandardType.FS81.S7Coprime
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.StandardType.FS81.S7E7RecogSup
import CFSG.LocalAnalysis.StandardType.FS81.S7RootEmbTwD7

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

section Assembly

theorem exists_betaEmbedding {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G} (h : RootSetting Row.twD7 b₀ K E B Y) :
    ∃ ι : adjointGroup .E8 GF₂ →* G, Function.Injective ι ∧ ι.range = Y ∧
      ι sθ = b₀ * B.b 1 ∧ s79A Row.twD7 B ≤ (Dθ).map ι ∧
      (∀ x : ↥(adjointGroup .E7 (ZMod 2)),
        (x : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) →
        ∀ a ∈ s79A Row.twD7 B, a * ι (e7Incl x) = ι (e7Incl x) * a) ∧
      ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
        (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) ∧ orderOf r = 3 ∧
        (b₀ * B.b 1) * ι (e7Incl r) = b₀⁻¹ := by
  obtain ⟨ι₀, hι₀, hrange₀, hβ₀, hA₀⟩ := exists_rootEmbedding_twD7 h
  have hβ₀' : ι₀ sθ = b₀ * B.b 1 := hβ₀
  have hℓ₀ := b₀_mul_inv_b₁_mem_map_perpLevi h ι₀ hι₀ hrange₀ hβ₀'
  obtain ⟨g, hgD, r, hr, hr3, hgr⟩ := exists_mem_perpLevi_conj_e7Incl_eq h ι₀ hι₀ hrange₀ hβ₀' hℓ₀
  have hcinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  have hι : Function.Injective (ι₀.comp (MulAut.conj g).toMonoidHom) := hι₀.comp hcinj
  have hrange : (ι₀.comp (MulAut.conj g).toMonoidHom).range = Y := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hcsurj, ← MonoidHom.range_eq_map,
      hrange₀]
  have hgs : (MulAut.conj g).toMonoidHom sθ = sθ := by
    have hcent := Subgroup.mem_centralizer_singleton_iff.1
      (perpLevi_le_centralizer_rootThree (K := GF₂) hgD)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact hcent
  have hβ : (ι₀.comp (MulAut.conj g).toMonoidHom) sθ = b₀ * B.b 1 := by
    rw [MonoidHom.comp_apply, hgs]
    exact hβ₀'
  have hDg : (Dθ).map (MulAut.conj g).toMonoidHom = Dθ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgD)
  have hA : s79A Row.twD7 B ≤ (Dθ).map (ι₀.comp (MulAut.conj g).toMonoidHom) := by
    rw [← Subgroup.map_map, hDg]
    exact hA₀
  have hℓ : (ι₀.comp (MulAut.conj g).toMonoidHom) (e7Incl r) = b₀ * (B.b 1)⁻¹ := by
    rw [MonoidHom.comp_apply]
    simpa [MulAut.conj_apply] using hgr
  have hAc := s79A_centralizes_map_e7Incl_highRootSL2 h (ι₀.comp (MulAut.conj g).toMonoidHom) hι
    hrange hβ hA hr hr3 hℓ
  refine ⟨ι₀.comp (MulAut.conj g).toMonoidHom, hι, hrange, hβ, hA, hAc, r, hr, hr3, ?_⟩
  rw [hℓ]
  have hcomm : B.b 1 * b₀ = b₀ * B.b 1 := by
    rw [← h.adapted.2.1]
    exact (B.comm 0 1).symm.eq
  have hb₀ : b₀ * b₀ * b₀ = 1 := by
    have h3 : b₀ ^ 3 = 1 := by
      have := pow_orderOf_eq_one (B.b 0)
      rwa [B.ord 0, h.adapted.2.1] at this
    rw [← pow_three']
    exact h3
  have h1 : b₀ * B.b 1 * (b₀ * (B.b 1)⁻¹) = b₀ * b₀ := by
    calc b₀ * B.b 1 * (b₀ * (B.b 1)⁻¹) = b₀ * (B.b 1 * b₀) * (B.b 1)⁻¹ := by group
      _ = b₀ * (b₀ * B.b 1) * (B.b 1)⁻¹ := by rw [hcomm]
      _ = b₀ * b₀ := by group
  rw [h1]
  exact eq_inv_of_mul_eq_one_left hb₀

theorem centralizer_le_of_betaEmbedding (hRec : E7RootRecog) {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y) (hC : Subgroup.centralizer ({b₀} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹)
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) (hrange : ι.range = Y)
    (hβ : ι sθ = b₀ * B.b 1) (hA : s79A Row.twD7 B ≤ (Dθ).map ι)
    (hAc : ∀ x : ↥(adjointGroup .E7 (ZMod 2)),
      (x : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) →
      ∀ a ∈ s79A Row.twD7 B, a * ι (e7Incl x) = ι (e7Incl x) * a)
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hr3 : orderOf r = 3)
    (hℓ : (b₀ * B.b 1) * ι (e7Incl r) = b₀⁻¹) :
    Subgroup.centralizer ({b₀ * B.b 1} : Set G) ≤ Y := by
  have hc := map_perpLevi_centralizes_disjoint ι hι
  have hmemD : ∀ x, e7Incl x ∈ Dθ := fun x => by
    rw [← range_e7Incl]
    exact ⟨x, rfl⟩
  have hmemL : ∀ x, ι (e7Incl x) ∈ (Dθ).map ι := fun x => ⟨e7Incl x, hmemD x, rfl⟩
  have hNH : Subgroup.zpowers (b₀ * B.b 1) ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]
  have hφH : ∀ x, ι (e7Incl x) ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G) := fun x => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg, ← hβ]
    exact (hc.1 _ (hmemL x)).symm
  have hφN : ∀ x, (ι.comp e7Incl) x ∈ Subgroup.zpowers (b₀ * B.b 1) → x = 1 := by
    intro x hx
    rw [← hβ] at hx
    have h1 : ι (e7Incl x) = 1 := hc.2 _ (hmemL x) hx
    have h2 : e7Incl x = 1 := hι (h1.trans (map_one ι).symm)
    exact e7Incl_injective (h2.trans (map_one e7Incl).symm)
  have hrangeφ : (ι.comp e7Incl).range = (Dθ).map ι := by
    rw [MonoidHom.range_comp, range_e7Incl]
  have hβY : b₀ * B.b 1 ∈ Y := by
    rw [← hβ, ← hrange]
    exact ⟨sθ, rfl⟩
  have hLY : (Dθ).map ι ≤ Y := by
    rw [← hrange]
    exact Subgroup.map_le_range ι _
  have hYc : ∀ y ∈ Y, y * (b₀ * B.b 1) = (b₀ * B.b 1) * y →
      y ∈ (Dθ).map ι ⊔ Subgroup.zpowers (b₀ * B.b 1) := by
    intro y hy hyc
    rw [← hβ] at hyc ⊢
    rw [sup_comm]
    have hyr : y ∈ ι.range := by
      rw [hrange]
      exact hy
    exact mem_sup_map_of_centralizes_rootThree ι hι hyr hyc
  have hmem : ∀ g ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G),
      g * (ι.comp e7Incl) r * g⁻¹ ∈ (ι.comp e7Incl).range ⊔ Subgroup.zpowers (b₀ * B.b 1) →
      g ∈ (ι.comp e7Incl).range ⊔ Subgroup.zpowers (b₀ * B.b 1) := by
    intro g hg hgr
    have hgβ : g * (b₀ * B.b 1) = (b₀ * B.b 1) * g :=
      (Subgroup.mem_centralizer_iff.mp hg (b₀ * B.b 1) rfl).symm
    rw [hrangeφ] at hgr ⊢
    exact mem_sup_of_conj_of_betaData hC hfus hβY hLY hYc hℓ hgβ hgr
  have hchar : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) → orderOf s = 2 →
      CharTwoMod (Subgroup.centralizer ({b₀ * B.b 1} : Set G)) (Subgroup.zpowers (b₀ * B.b 1))
        ⟨(ι.comp e7Incl) s, hφH s⟩ := fun s hs hs2 =>
    charTwoMod_of_betaData (betaData_of_embedding h hC ι hι hrange hβ hA hAc s hs hs2) (hφH s)
  refine (le_sup_of_e7RootRecog hRec (Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (Subgroup.zpowers (b₀ * B.b 1)) hNH (ι.comp e7Incl) hφH hφN r hr hr3 hmem hchar).trans
    (sup_le ?_ ?_)
  · rw [hrangeφ]
    exact hLY
  · exact Subgroup.zpowers_le.mpr hβY

theorem twD7BetaCentAt_of_recog (hRec : E7RootRecog) : TwD7BetaCentAt := by
  intro G _ _ b₀ K E B Y h hC hfus
  obtain ⟨ι, hι, hrange, hβ, hA, hAc, r, hr, hr3, hℓ⟩ := exists_betaEmbedding h
  exact centralizer_le_of_betaEmbedding hRec h hC hfus ι hι hrange hβ hA hAc hr hr3 hℓ

end Assembly

end CFSG.StandardType.FrameRoute.FS81

end
