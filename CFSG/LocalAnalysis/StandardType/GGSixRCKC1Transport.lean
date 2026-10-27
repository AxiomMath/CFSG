module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpSurvivor

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.StandardType

theorem fourAt_map_mulEquiv
    {X : Type} {U : Type} [Group X] [Group U] {J V : Subgroup X} {r : X}
    (e : ↥J ≃* U) (hrJ : r ∈ J) (h : FourAt J V r) :
    FourAt (⊤ : Subgroup U) ((V.subgroupOf J).map e.toMonoidHom) (e ⟨r, hrJ⟩) := by
  obtain ⟨hrV, hVJ, hVab, hVcard, hr1, hconj⟩ := h
  refine ⟨Subgroup.mem_map_of_mem e.toMonoidHom hrV, le_top, ?_, ?_, ?_, ?_⟩
  · exact (hVab.subgroupOf J).map e.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVJ).toEquiv]
    exact hVcard
  · intro h1
    have hrJ1 : (⟨r, hrJ⟩ : J) = 1 := by
      apply e.injective
      simpa only [map_one] using h1
    exact hr1 (congrArg Subtype.val hrJ1)
  · intro v hv hv1
    obtain ⟨vJ, hvJ, rfl⟩ := Subgroup.mem_map.mp hv
    have hv1' : (vJ : X) ≠ 1 := by
      intro h1
      apply hv1
      rw [show vJ = 1 from Subtype.ext h1, map_one]
    obtain ⟨j, hjJ, hvj⟩ := hconj vJ hvJ hv1'
    refine ⟨e ⟨j, hjJ⟩, Subgroup.mem_top _, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hvj)

theorem coreCommAt_map_mulEquiv
    {X : Type} {U : Type} [Group X] [Group U] {J V : Subgroup X} {r : X}
    (e : ↥J ≃* U) (hrJ : r ∈ J) (h : CoreCommAt J V r) :
    CoreCommAt (⊤ : Subgroup U) ((V.subgroupOf J).map e.toMonoidHom) (e ⟨r, hrJ⟩) := by
  intro v hv y hy
  rw [top_inf_eq] at hy
  obtain ⟨vJ, hvJ, rfl⟩ := Subgroup.mem_map.mp hv
  rw [← CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv e hrJ] at hy
  obtain ⟨yJ, hyJ, rfl⟩ := Subgroup.mem_map.mp hy
  have hy : (yJ : X) ∈ pCoreOf 2 (J ⊓ Subgroup.centralizer ({r} : Set X)) := hyJ
  have hcomm := h vJ hvJ yJ hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_zpow]
  exact congrArg e (Subtype.ext hk)

theorem k2At_of_mulEquiv
    {X : Type} {U : Type*} [Group X] [Group U] {K V : Subgroup X} {r : X}
    (e : ↥K ≃* U) (hrK : r ∈ K) (hVK : V ≤ K)
    (h : pCoreOf 2 (Subgroup.centralizer ({e ⟨r, hrK⟩} : Set U)) ≤
      Subgroup.normalizer ((V.subgroupOf K).map e.toMonoidHom : Set U)) : K2At K V r := by
  intro y hy
  have hyK : y ∈ K := (GGRootNorm.pCoreOf_le _ hy).1
  have heY : e ⟨y, hyK⟩ ∈ pCoreOf 2
      (Subgroup.centralizer ({e ⟨r, hrK⟩} : Set U)) := by
    rw [← CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv e hrK]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, hy, rfl⟩
  have hyN : (⟨y, hyK⟩ : K) ∈ Subgroup.normalizer (V.subgroupOf K : Set K) := by
    have hN := h heY
    rw [GGRootNorm.normalizer_map_mulEquiv e, Subgroup.mem_map_equiv] at hN
    simpa using hN
  exact (GGRootNorm.mem_normalizer_subgroupOf_iff hVK ⟨y, hyK⟩).mp hyN

theorem k2At_of_pure_sp_model
    {X : Type} [Group X] {K V : Subgroup X} {r : X} {m : ℕ}
    (hm : 3 ≤ m) (e : ↥K ≃* CFSG.Open.StatedSp m (GaloisField 2 1))
    (hrK : r ∈ K) (hrV : r ∈ V) (hr1 : r ≠ 1) (hVK : V ≤ K)
    (hVab : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (hpure : ∀ v ∈ (V.subgroupOf K).map e.toMonoidHom, v ≠ 1 →
      ∃ x y : Fin m ⊕ Fin m → GaloisField 2 1,
        CFSG.StandardType.RCKK1IIISp.spB m x y = 0 ∧
          CFSG.StandardType.RCKK1IIISp.SpSiegel x y v) : K2At K V r := by
  have hrne : e ⟨r, hrK⟩ ≠ 1 := by
    intro h1
    have hrK1 : (⟨r, hrK⟩ : K) = 1 := by
      apply e.injective
      simpa only [map_one] using h1
    exact hr1 (congrArg Subtype.val hrK1)
  have hVab' : IsElemAbelian 2 ((V.subgroupOf K).map e.toMonoidHom) :=
    (hVab.subgroupOf K).map e.toMonoidHom
  have hcard : Nat.card ((V.subgroupOf K).map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
    exact hVcard
  exact k2At_of_mulEquiv e hrK hVK
    (k2At_of_pure_shortRoot_fourGroup hm
      (Subgroup.mem_map_of_mem e.toMonoidHom hrV) hrne hVab' hcard hpure)

end CFSG.StandardType.RCKC1
