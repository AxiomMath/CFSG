module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.FS81.S7PCoreCentE7
import CFSG.LocalAnalysis.StandardType.FS81.S7PCoreConjE8
import CFSG.LocalAnalysis.StandardType.FS81.S7CentRootThree
import CFSG.LocalAnalysis.StandardType.FS81.S7PCoreCentEmb
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.GroupTheory.OppositeRadicals
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.LocalAnalysis.StandardType.FS81.RootE8A
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)

private theorem pCoreOf_centralizer_inf_range_map {H G : Type} [Group H] [Group G]
    (φ : H →* G) (hφ : Function.Injective φ) (s : H) :
    pCoreOf 2 (φ.range ⊓ Subgroup.centralizer ({φ s} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({s} : Set H))).map φ := by
  rw [inf_comm, centralizer_singleton_inf_range_eq_map φ hφ s]
  exact CFSG.GroupTheory.pCoreOf_map_of_injective 2 φ hφ _

private theorem pCoreOf_centralizer_conj {G : Type*} [Group G] (g u : G) :
    pCoreOf 2 (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({u} : Set G))).map
        (MulAut.conj g).toMonoidHom := by
  have h : (MulAut.conj g).toMonoidHom '' ({u} : Set G) = {g * u * g⁻¹} := by
    simp [Set.image_singleton, MulAut.conj_apply]
  rw [← h, ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv (MulAut.conj g) ({u} : Set G)]
  exact CFSG.GroupTheory.map_pCoreOf_mulEquiv 2 (MulAut.conj g)
    (Subgroup.centralizer ({u} : Set G))

section Assembly


theorem betaData_of_embedding {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G} (h : RootSetting Row.twD7 b₀ K E B Y)
    (hC : Subgroup.centralizer ({b₀} : Set G) ≤ Y) (ι : adjointGroup .E8 GF₂ →* G)
    (hι : Function.Injective ι) (hrange : ι.range = Y) (hβ : ι sθ = b₀ * B.b 1)
    (hA : s79A Row.twD7 B ≤ (Dθ).map ι)
    (hAc : ∀ x : ↥(adjointGroup .E7 (ZMod 2)),
      (x : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) →
      ∀ a ∈ s79A Row.twD7 B, a * ι (e7Incl x) = ι (e7Incl x) * a)
    (s : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2) :
    BetaData Y ((Dθ).map ι) (s79A Row.twD7 B) b₀ (b₀ * B.b 1) (ι (e7Incl s)) := by
  let φ : ↥(adjointGroup .E7 (ZMod 2)) →* G := ι.comp e7Incl
  have hφinj : Function.Injective φ := hι.comp e7Incl_injective
  have hmemD : ∀ x, e7Incl x ∈ Dθ := fun x => by
    rw [← range_e7Incl]
    exact ⟨x, rfl⟩
  have hrangeφ : φ.range = (Dθ).map ι := by
    rw [MonoidHom.range_comp, range_e7Incl]
  obtain ⟨m, hm1, hm2⟩ := exists_conj_pinnedElt_e7Incl s hs hs2
  have hR7 := pCoreOf_centralizer_eq_of_embedding (Or.inr rfl) h hC ι hι hrange hA
  let cm : ↥(adjointGroup .E8 GF₂) →* ↥(adjointGroup .E8 GF₂) :=
    (MulAut.conj m).toMonoidHom
  let cg : G →* G := (MulAut.conj (ι m)).toMonoidHom
  have hcomp : cg.comp ι = ι.comp cm := by
    ext x
    show (MulAut.conj (ι m)).toMonoidHom (ι x) = ι ((MulAut.conj m).toMonoidHom x)
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hσeq : ι m * ι tθ * (ι m)⁻¹ = ι (e7Incl s) := by
    simpa only [map_mul, map_inv] using congrArg ι hm1
  have hQ : pCoreOf 2 (Subgroup.centralizer ({ι (e7Incl s)} : Set G)) =
      ((Qθ).map cm).map ι := by
    rw [← hσeq, pCoreOf_centralizer_conj (ι m) (ι tθ), hR7, Subgroup.map_map, hcomp,
      ← Subgroup.map_map]
  have hP : pCoreOf 2 ((Dθ).map ι ⊓ Subgroup.centralizer ({ι (e7Incl s)} : Set G)) =
      ((pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))))).map
        e7Incl).map ι := by
    have hL : (Dθ).map ι ⊓ Subgroup.centralizer ({ι (e7Incl s)} : Set G) =
        φ.range ⊓ Subgroup.centralizer ({φ s} : Set G) := by
      rw [← hrangeφ]
      rfl
    rw [hL, pCoreOf_centralizer_inf_range_map φ hφinj s, Subgroup.map_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hβ, orderOf_injective ι hι sθ]
    exact orderOf_rootThree (K := GF₂) (isRoot_highRoot .E8)
  · rw [← hβ, ← hrange]
    exact ⟨sθ, rfl⟩
  · rw [← hrange]
    exact Subgroup.map_le_range ι _
  · intro x hx
    rw [← hβ]
    exact (map_perpLevi_centralizes_disjoint ι hι).1 x hx
  · intro x hx hz
    rw [← hβ] at hz
    exact (map_perpLevi_centralizes_disjoint ι hι).2 x hx hz
  · intro y hy hyc
    have hyr : y ∈ ι.range := by rw [hrange]; exact hy
    have hyc' : y * ι sθ = ι sθ * y := by rw [hβ]; exact hyc
    have h := mem_sup_map_of_centralizes_rootThree ι hι hyr hyc'
    rwa [hβ] at h
  · exact hA
  · exact isElemAbelian_s79A B
  · exact card_s79A (by decide) B
  · exact hC
  · intro F hF h9
    exact h.exists_conj_mem_of_le_s79A (by decide) (e8AutAt_twD7 G b₀ K E B Y h) hF h9
  · exact ⟨e7Incl s, hmemD s, rfl⟩
  · rw [orderOf_injective ι hι (e7Incl s),
      orderOf_injective e7Incl e7Incl_injective s, hs2]
  · intro a ha
    exact hAc s hs a ha
  · intro x hx hxc
    have hx' : x ∈ φ.range := by rwa [hrangeφ]
    obtain ⟨x₀, rfl⟩ := hx'
    rw [← hrangeφ] at hxc
    change φ x₀ ∈ Subgroup.zpowers (φ s)
    have hx0 : x₀ ∈ Subgroup.zpowers s := by
      apply mem_zpowers_of_centralizes_pCoreOf_e7 s hs hs2
      intro y hy
      have hmem : φ y ∈ pCoreOf 2 (φ.range ⊓ Subgroup.centralizer ({φ s} : Set G)) := by
        rw [pCoreOf_centralizer_inf_range_map φ hφinj s]
        exact ⟨y, hy, rfl⟩
      have h2 : φ (x₀ * y) = φ (y * x₀) := by
        rw [map_mul, map_mul]
        exact hxc (φ y) hmem
      exact hφinj h2
    rw [← MonoidHom.map_zpowers φ s]
    exact ⟨x₀, hx0, rfl⟩
  · rw [hP, hQ]
    exact Subgroup.map_mono (f := ι) hm2
  · rw [hQ]
    exact (Subgroup.map_le_range ι ((Qθ).map cm)).trans hrange.le

end Assembly

end CFSG.StandardType.FrameRoute.FS81

end
