module

public import CFSG.LocalAnalysis.SteinbergSFRankOneSelector
public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup TorusLayer CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "𝐑" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐒𝐛" => S.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐚" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F) t

namespace AxisData

theorem stdLinearData (h : AxisData F K n S J Y V U t hk) : StdLinearData (F ⧸ 𝐑) 𝐒𝐛 n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, -, -, -, -, hstd, hnn, -⟩ := h.layer
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [h.card_K]; positivity)
  have := Fintype.ofFinite K
  exact ⟨h.two_le, hstd, hnn, K, inferInstance, inferInstance,
    by rw [← Nat.card_eq_fintype_card, h.card_K], ⟨e.symm⟩⟩

theorem card_sylow_eq_two (h : AxisData F K n S J Y V U t hk) :
    ∀ P : Sylow 2 (centralizer (𝐒𝐛 : Set (F ⧸ 𝐑))), Nat.card P = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, ha, -, -, -, -, -, -, -, -, ⟨Q, hQ⟩, -⟩ := h.layer
  have hQc : Nat.card Q = 2 := by
    rw [← card_map_of_injective (centralizer (𝐒𝐛 : Set (F ⧸ 𝐑))).subtype_injective, hQ,
      Nat.card_zpowers, ha]
  intro P
  rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity Q, hQc]

theorem a_mem_centralizer (h : AxisData F K n S J Y V U t hk) :
    𝐚 ∈ centralizer (𝐒𝐛 : Set (F ⧸ 𝐑)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hSa, -⟩ := h.layer
  rw [mem_centralizer_iff]
  intro s hs
  exact mem_centralizer_singleton_iff.1 (hSa hs)

theorem map_V_le (h : AxisData F K n S J Y V U t hk) : V.map θ ≤ 𝐃 :=
  h.map_Y ▸ map_mono h.V_le

theorem a_mem_normalizer_map_V (h : AxisData F K n S J Y V U t hk) :
    𝐚 ∈ normalizer ((V.map θ : Subgroup (F ⧸ 𝐑)) : Set (F ⧸ 𝐑)) :=
  le_normalizer_map θ (mem_map_of_mem θ h.t_mem)

theorem map_V_inf_le (h : AxisData F K n S J Y V U t hk)
    (hVC : V ⊓ centralizer ({t} : Set F) ≤ U) :
    V.map θ ⊓ centralizer ({𝐚} : Set (F ⧸ 𝐑)) ≤ 𝐒𝐛 := by
  rintro _ ⟨⟨v, hv, rfl⟩, hva⟩
  have hva' : θ v * 𝐚 = 𝐚 * θ v := mem_centralizer_singleton_iff.1 hva
  have htv : t⁻¹ * v * t ∈ V := by
    have h1 := (mem_normalizer_iff.1 (inv_mem h.t_mem) v).1 hv
    rwa [inv_inv] at h1
  have hc : v⁻¹ * (t⁻¹ * v * t) ∈ V := mul_mem (inv_mem hv) htv
  have hθ : θ (v⁻¹ * (t⁻¹ * v * t)) = θ 1 := by
    rw [map_one, map_mul, map_inv, map_mul, map_mul, map_inv]
    calc (θ v)⁻¹ * ((θ t)⁻¹ * θ v * θ t) = (θ v)⁻¹ * ((θ t)⁻¹ * (θ v * θ t)) := by group
      _ = (θ v)⁻¹ * ((θ t)⁻¹ * (θ t * θ v)) := by rw [hva']
      _ = 1 := by group
  have h1 : v⁻¹ * (t⁻¹ * v * t) = 1 := h.injOn_V hc (one_mem V) hθ
  have hvt : v * t = t * v := by
    have h2 : t⁻¹ * v * t = v := by
      calc t⁻¹ * v * t = v * (v⁻¹ * (t⁻¹ * v * t)) := by group
        _ = v := by rw [h1, mul_one]
    calc v * t = t * (t⁻¹ * v * t) := by group
      _ = t * v := by rw [h2]
  have hvU : v ∈ U := hVC (mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 hvt⟩)
  exact mem_map_of_mem θ (h.U_le_S hvU)

theorem card_map_V (h : AxisData F K n S J Y V U t hk) : Nat.card (V.map θ) = Nat.card V :=
  card_map_of_injOn θ h.injOn_V

theorem models (hSel : FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D)
    (h : AxisData F K n S J Y V U t hk) (hVC : V ⊓ centralizer ({t} : Set F) ≤ U) :
    ((2 ^ n) ^ 3 ≤ Nat.card V → IsSimpleGroup 𝐃 ∧
        (StatedClassicalModel 𝐃 .PSL 3 2 n ∨ StatedClassicalModel 𝐃 .PSU 3 2 n)) ∧
      ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ x ∈ V, x * x = 1) → Nat.card V = (2 ^ n) ^ 2 →
        IsSimpleGroup 𝐃 → StatedClassicalModel 𝐃 .PSL 2 2 (2 * n)) := by
  obtain ⟨hKX, -, -, -, -, -, -, -, -, ha, -, -, -, -, -, -, -, -, -, hO, -⟩ := h.layer
  obtain ⟨-, h1, h2⟩ := RankOneSelector.rankOne_layer_select hSel hKX hO h.stdLinearData
    h.card_sylow_eq_two ha h.a_mem_centralizer h.map_V_le (h.V_pgroup.map θ)
    h.a_mem_normalizer_map_V (h.map_V_inf_le hVC)
  refine ⟨fun h3 => h1 (by rw [h.card_map_V]; exact h3), fun hc hs h2' hDs => h2 ?_ ?_
    (by rw [h.card_map_V, h2']) hDs⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hs x hx, map_one]

end AxisData

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
