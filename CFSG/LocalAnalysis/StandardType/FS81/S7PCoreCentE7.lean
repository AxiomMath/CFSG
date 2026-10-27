module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7E7RadicalCent
import CFSG.LocalAnalysis.StandardType.FS81.S7RootSL2
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "s7" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q7" => EPilot.highRadical Tag.E7 (ZMod 2)

section E7Model


theorem mem_zpowers_of_centralizes_pCoreOf_e7 (s : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2)
    {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2)))),
      x * y = y * x) : x ∈ Subgroup.zpowers s := by
  obtain ⟨h, -, hconj⟩ := exists_conj_pinnedElt_of_mem_highRootSL2 s hs hs2
  obtain ⟨hQ2, hsup, -, hnorm⟩ :=
    EPilot.isTwoRadicalDecomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl)) one_ne_zero
  have hQ_le_C : Q7 ≤ Subgroup.centralizer
      ({s7} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hsup]
    exact le_sup_left
  have hC_le_norm : Subgroup.centralizer ({s7} : Set ↥(adjointGroup .E7 (ZMod 2))) ≤
      Subgroup.normalizer (Q7 : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer hnorm
  let ch : ↥(adjointGroup .E7 (ZMod 2)) →* ↥(adjointGroup .E7 (ZMod 2)) :=
    (MulAut.conj h).toMonoidHom
  have hch_s7 : ch s7 = s := by
    have : ch s7 = h * s7 * h⁻¹ := by simp [ch]
    rw [this]
    exact hconj
  have hN2 : IsPGroup 2 ((Q7).map ch) := hQ2.map ch
  have hN_le_C : (Q7).map ch ≤
      Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyC : y ∈ Subgroup.centralizer ({s7} : Set ↥(adjointGroup .E7 (ZMod 2))) := hQ_le_C hy
    rw [Subgroup.mem_centralizer_iff] at hyC
    have hycomm : s7 * y = y * s7 := hyC s7 (Set.mem_singleton s7)
    calc s * ch y = ch s7 * ch y := by rw [hch_s7]
      _ = ch (s7 * y) := by rw [map_mul]
      _ = ch (y * s7) := by rw [hycomm]
      _ = ch y * ch s7 := by rw [map_mul]
      _ = ch y * s := by rw [hch_s7]
  have hconjmem : ∀ g ∈ Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))),
      ∀ z ∈ (Q7).map ch, g * z * g⁻¹ ∈ (Q7).map ch := by
    intro g hg z hz
    rw [Subgroup.mem_map] at hz ⊢
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨(h⁻¹ * g * h) * y * (h⁻¹ * g * h)⁻¹, ?_, ?_⟩
    · have hgC : s * g = g * s :=
        (Subgroup.mem_centralizer_iff.mp hg) s (Set.mem_singleton s)
      have haC : h⁻¹ * g * h ∈
          Subgroup.centralizer ({s7} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have hs7 : s7 = h⁻¹ * s * h := by
          calc s7 = h⁻¹ * (h * s7 * h⁻¹) * h := by group
            _ = h⁻¹ * s * h := by rw [hconj]
        rw [hs7]
        calc (h⁻¹ * s * h) * (h⁻¹ * g * h) = h⁻¹ * (s * g) * h := by group
          _ = h⁻¹ * (g * s) * h := by rw [hgC]
          _ = (h⁻¹ * g * h) * (h⁻¹ * s * h) := by group
      have haN : h⁻¹ * g * h ∈ Subgroup.normalizer (Q7 : Set ↥(adjointGroup .E7 (ZMod 2))) :=
        hC_le_norm haC
      exact (Subgroup.mem_normalizer_iff.mp haN y).mp hy
    · have hch_a : ch (h⁻¹ * g * h) = g := by
        have : ch (h⁻¹ * g * h) = h * (h⁻¹ * g * h) * h⁻¹ := by simp [ch]
        rw [this]
        group
      calc ch ((h⁻¹ * g * h) * y * (h⁻¹ * g * h)⁻¹)
          = ch (h⁻¹ * g * h) * ch y * (ch (h⁻¹ * g * h))⁻¹ := by
            simp only [map_mul, map_inv]
        _ = g * ch y * g⁻¹ := by rw [hch_a]
  have hC_norm_N : Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))) ≤
      Subgroup.normalizer ((Q7).map ch : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hconjmem g hg z
    · intro hz
      have hginv : g⁻¹ ∈ Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))) :=
        inv_mem hg
      have hthis := hconjmem g⁻¹ hginv (g * z * g⁻¹) hz
      rwa [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z from by group] at hthis
  have hN_le_P : (Q7).map ch ≤
      pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2)))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN_le_C hC_norm_N hN2
  have hz : h⁻¹ * x * h ∈ Subgroup.zpowers s7 := by
    refine mem_zpowers_of_centralizes_highRadical_E7 (h⁻¹ * x * h) (fun y hy => ?_)
    have hcyP : ch y ∈
        pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2)))) :=
      hN_le_P (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    have hxy : x * ch y = ch y * x := hx (ch y) hcyP
    have hcy : ch y = h * y * h⁻¹ := by simp [ch]
    calc (h⁻¹ * x * h) * y
        = h⁻¹ * (x * ch y) * h := by rw [hcy]; group
      _ = h⁻¹ * (ch y * x) * h := by rw [hxy]
      _ = y * (h⁻¹ * x * h) := by rw [hcy]; group
  have hxN : x ∈ (Subgroup.zpowers s7).map ch :=
    Subgroup.mem_map.mpr ⟨h⁻¹ * x * h, hz, by
      have : ch (h⁻¹ * x * h) = h * (h⁻¹ * x * h) * h⁻¹ := by simp [ch]
      rw [this]; group⟩
  rwa [MonoidHom.map_zpowers, hch_s7] at hxN

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
