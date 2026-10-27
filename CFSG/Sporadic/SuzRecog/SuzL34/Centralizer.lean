module

public import CFSG.Sporadic.SuzRecog.SuzL34.CITConfig
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Recognition.L34CIT.InnerAut

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} (D : LocalData G z)

noncomputable abbrev RG : Subgroup G :=
  centralizer (D.AG : Set G) ⊓ centralizer ({D.t0} : Set G)

private theorem TG_inf_centralizer_T0G_eq_pull_c0Tabs :
    D.TG ⊓ centralizer (D.T0G : Set G) = D.pull (tabSubgroup c0Tabs) := by
  have hV0 : tabSubgroup v0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_v0Tabs]
    exact inf_le_right
  have hT0 : tabSubgroup t0Tabs ≤ invE 1 := D.tabSubgroup_t0Tabs_le.trans hV0
  have hab : D.pull (tabSubgroup v0Tabs) ⊓
      centralizer (D.pull (tabSubgroup t0Tabs) : Set G) ≤
        centralizer ({z} : Set G) :=
    inf_le_left.trans (D.pull_le_centralizer _)
  calc D.TG ⊓ centralizer (D.T0G : Set G)
      = D.pull (tabSubgroup v0Tabs) ⊓
          centralizer (D.pull (tabSubgroup t0Tabs) : Set G) := by rw [TG, T0G]
    _ = (D.pull (tabSubgroup v0Tabs) ⊓
          centralizer (D.pull (tabSubgroup t0Tabs) : Set G)) ⊓
            centralizer ({z} : Set G) := (inf_eq_left.mpr hab).symm
    _ = D.pull (tabSubgroup v0Tabs) ⊓
          (centralizer (D.pull (tabSubgroup t0Tabs) : Set G) ⊓
            centralizer ({z} : Set G)) := inf_assoc _ _ _
    _ = D.pull (tabSubgroup v0Tabs) ⊓ D.pull (centralizer (tabSubgroup t0Tabs)) := by
          rw [D.pull_centralizer hT0]
    _ = D.pull (tabSubgroup v0Tabs ⊓ centralizer (tabSubgroup t0Tabs)) :=
          (D.pull_inf _ _).symm
    _ = D.pull (tabSubgroup c0Tabs) := by
          rw [D.tabSubgroup_c0Tabs, inf_comm]

private theorem isElemAbelian_tabSubgroup_c0Tabs (hF7 : F7Prop) :
    IsElemAbelian 2 (tabSubgroup c0Tabs) := by
  obtain ⟨-, hcomm, hsq, -⟩ := hF7
  refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)),
    fun x hx => ?_⟩
  rw [pow_two]
  exact hsq x hx

private theorem isElemAbelian_pull_c0Tabs (hF7 : F7Prop) :
    IsElemAbelian 2 (D.pull (tabSubgroup c0Tabs)) := by
  have hV0 : tabSubgroup v0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_v0Tabs]
    exact inf_le_right
  have hc0 : tabSubgroup c0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_c0Tabs]
    exact inf_le_right.trans hV0
  exact (D.isElemAbelian_pull_iff hc0).mpr (isElemAbelian_tabSubgroup_c0Tabs hF7)

theorem card_TG_inf_centralizer_T0G (hF7 : F7Prop) :
    Nat.card ↥(D.TG ⊓ centralizer (D.T0G : Set G)) = 16 := by
  have hc0 : tabSubgroup c0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_c0Tabs]
    exact inf_le_right.trans (by
      rw [D.tabSubgroup_v0Tabs]
      exact inf_le_right)
  rw [TG_inf_centralizer_T0G_eq_pull_c0Tabs D, D.card_pull hc0]
  obtain ⟨hC0, -⟩ := hF7
  exact hC0

theorem mul_self_eq_one_of_mem_TG_inf (hF7 : F7Prop) {x : G}
    (hx : x ∈ D.TG ⊓ centralizer (D.T0G : Set G)) : x * x = 1 := by
  rw [TG_inf_centralizer_T0G_eq_pull_c0Tabs D] at hx
  exact IsElemAbelian.mul_self_eq_one (isElemAbelian_pull_c0Tabs D hF7) hx

theorem card_centralizer_AG_le (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF7 : F7Prop) (hF8 : F8Prop) :
    Nat.card (centralizer (D.AG : Set G)) ≤ 192 := by
  have hV0 : tabSubgroup v0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_v0Tabs]
    exact inf_le_right
  have hT0 : tabSubgroup t0Tabs ≤ invE 1 := D.tabSubgroup_t0Tabs_le.trans hV0
  have hct0 : tabSubgroup ct0Tabs ≤ invE 1 := by
    rw [D.tabSubgroup_ct0Tabs]
    exact inf_le_right
  have hEq : D.pull (tabSubgroup ct0Tabs) =
      centralizer (D.T0G : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [D.tabSubgroup_ct0Tabs, D.pull_inf_invE, D.pull_centralizer hT0]
  have hcard : Nat.card ↥(centralizer (D.T0G : Set G) ⊓
      centralizer ({z} : Set G)) = 192 := by
    rw [← hEq, D.card_pull hct0]
    obtain ⟨-, -, -, -, hct0card⟩ := hF7
    exact hct0card
  have hT0A : D.T0G ≤ D.AG := T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8
  have hzA : z ∈ D.AG := z_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8
  have hle : centralizer (D.AG : Set G) ≤
      centralizer (D.T0G : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf (Subgroup.centralizer_le hT0A)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzA))
  exact (Subgroup.card_le_of_le hle).trans (le_of_eq hcard)

theorem RG_le_TG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop)
    (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) : D.RG ≤ D.TG := by
  rw [TG_eq]
  intro r hr
  obtain ⟨hrA, hrt0⟩ := Subgroup.mem_inf.mp hr
  refine Subgroup.mem_inf.mpr ⟨hrt0, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hrA z
    (z_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)).symm

theorem RG_le_centralizer_T0G (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) :
    D.RG ≤ centralizer (D.T0G : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).1 a
    (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 ha)

theorem RG_inf_AG (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop)
    (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    D.RG ⊓ D.AG = ⊥ := by
  obtain ⟨C, -, -, -⟩ :=
    exists_config D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  have hcenter : Subgroup.center ↥D.AG = ⊥ := C.center_eq_bot C.card_eq
  rw [eq_bot_iff_forall]
  intro g hg
  obtain ⟨hgR, hgA⟩ := Subgroup.mem_inf.mp hg
  have hgc : (⟨g, hgA⟩ : ↥D.AG) ∈ Subgroup.center ↥D.AG := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hcomm : (a : G) * g = g * (a : G) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hgR).1 (a : G) a.2
    exact Subtype.ext hcomm
  rw [hcenter] at hgc
  have hg1 : (⟨g, hgA⟩ : ↥D.AG) = 1 := Subgroup.mem_bot.mp hgc
  exact congrArg Subtype.val hg1

theorem exists_mem_RG_mul (hF1 : F1Prop)
    (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop)
    (hF6 : F6Prop) (hF6b : F6bProp) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop)
    {x : G} (hx : x ∈ D.TG ⊓ centralizer (D.T0G : Set G)) :
    ∃ r ∈ D.RG, ∃ y ∈ D.L ⊓ D.M2G, x = r * y := by
  obtain ⟨C, hCT, hCL, hCM⟩ :=
    exists_config D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxD0 : x ∈ centralizer ({D.t0} : Set G) := D.TG_le_centralizer hxT
  have hxn0 : x ∈ normalizer (centralizer ({D.t0} : Set G) : Set G) :=
    Subgroup.le_normalizer (H := centralizer ({D.t0} : Set G)) hxD0
  have hxn : x ∈ normalizer (D.AG : Set G) :=
    CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure _ hxn0
  have hxCT : ∀ t ∈ C.T, x * (t : G) = (t : G) * x := by
    intro t ht
    have ht0 : (t : G) ∈ D.T0G := by
      have ht' : (t : ↥D.AG) ∈ (D.T0G.subgroupOf D.AG : Subgroup ↥D.AG) := by
        rw [← hCT]
        exact ht
      exact Subgroup.mem_subgroupOf.mp ht'
    exact (Subgroup.mem_centralizer_iff.mp hxC (t : G) ht0).symm
  obtain ⟨y, hyZ, hconj⟩ := C.exists_mem_Z_conj_eq hxn hxCT
  have hyLM : (y : G) ∈ D.L ⊓ D.M2G := by
    have hy := hyZ
    rw [Subgroup.mem_inf] at hy
    rw [hCL, hCM] at hy
    exact Subgroup.mem_inf.mpr (by simpa only [Subgroup.mem_subgroupOf] using hy)
  have hyA : (y : G) ∈ D.AG := y.2
  have hy0 : (y : G) ∈ centralizer ({D.t0} : Set G) := D.AG_le_centralizer hyA
  have hxy : x * (y : G) = (y : G) * x := by
    have h := hconj y
    have h' : x * (y : G) * x⁻¹ = (y : G) := by
      simpa using h
    calc x * (y : G) = (x * (y : G) * x⁻¹) * x := by group
      _ = (y : G) * x := by rw [h']
  refine ⟨(y : G)⁻¹ * x, ?_, (y : G), hyLM, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := hconj ⟨a, ha⟩
      have hkey : (y : G)⁻¹ * x * a * ((y : G)⁻¹ * x)⁻¹ = a := by
        calc (y : G)⁻¹ * x * a * ((y : G)⁻¹ * x)⁻¹
            = (y : G)⁻¹ * (x * a * x⁻¹) * (y : G) := by group
          _ = (y : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * (y : G) := by rw [h]
          _ = a := by group
      exact ((mul_inv_eq_iff_eq_mul (a := (y : G)⁻¹ * x * a) (b := (y : G)⁻¹ * x)
        (c := a)).mp hkey).symm
    · exact Subgroup.mul_mem (H := centralizer ({D.t0} : Set G))
        (Subgroup.inv_mem (H := centralizer ({D.t0} : Set G)) hy0) hxD0
  · calc x = (y : G)⁻¹ * ((y : G) * x) := by group
      _ = (y : G)⁻¹ * (x * (y : G)) := by rw [← hxy]
      _ = ((y : G)⁻¹ * x) * (y : G) := by group

theorem card_RG (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop)
    (hF6b : F6bProp) (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    Nat.card D.RG = 4 := by
  let f : ↥D.RG × ↥(D.L ⊓ D.M2G) → ↥(D.TG ⊓ centralizer (D.T0G : Set G)) :=
    fun p => ⟨p.1 * p.2, by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact D.TG.mul_mem
          (RG_le_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 p.1.2)
          ((L_le_T0G D hF5).trans (T0G_le_TG D) (Subgroup.mem_inf.mp p.2.2).1)
      · exact Subgroup.mul_mem (H := centralizer (D.T0G : Set G))
          (RG_le_centralizer_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 p.1.2)
          (inf_M2G_le_centralizer D hF5 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have hpq' : (p.1 : G) * p.2 = (q.1 : G) * q.2 := congrArg Subtype.val hpq
      have h1 : (q.1 : G)⁻¹ * p.1 ∈ D.RG :=
        D.RG.mul_mem (D.RG.inv_mem q.1.2) p.1.2
      have h2 : (q.1 : G)⁻¹ * p.1 ∈ D.AG := by
        have hq : (q.2 : G) ∈ D.L := (Subgroup.mem_inf.mp q.2.2).1
        have hp : (p.2 : G) ∈ D.L := (Subgroup.mem_inf.mp p.2.2).1
        have hL : (q.2 : G) * (p.2 : G)⁻¹ ∈ D.L := D.L.mul_mem hq (D.L.inv_mem hp)
        have hA : (q.2 : G) * (p.2 : G)⁻¹ ∈ D.AG :=
          (L_le_T0G D hF5).trans
            (T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8) hL
        have heq : (q.1 : G)⁻¹ * p.1 = (q.2 : G) * (p.2 : G)⁻¹ := by
          calc (q.1 : G)⁻¹ * p.1
              = (q.1 : G)⁻¹ * ((p.1 : G) * p.2) * (p.2 : G)⁻¹ := by group
            _ = (q.1 : G)⁻¹ * ((q.1 : G) * q.2) * (p.2 : G)⁻¹ := by rw [hpq']
            _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
        rwa [heq]
      have hbot : (q.1 : G)⁻¹ * p.1 ∈ D.RG ⊓ D.AG := ⟨h1, h2⟩
      rw [RG_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11] at hbot
      have hq1p1 : (q.1 : G)⁻¹ * p.1 = 1 := Subgroup.mem_bot.mp hbot
      have hp1 : p.1 = q.1 := by
        apply Subtype.ext
        calc (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * p.1) := by group
          _ = (q.1 : G) * 1 := by rw [hq1p1]
          _ = (q.1 : G) := by group
      have hp2 : p.2 = q.2 := by
        apply Subtype.ext
        have h := hpq'
        rw [congrArg Subtype.val hp1] at h
        exact mul_left_cancel h
      exact Prod.ext hp1 hp2
    · intro x
      obtain ⟨r, hr, y, hy, hxy⟩ :=
        exists_mem_RG_mul D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11 x.2
      refine ⟨(⟨r, hr⟩, ⟨y, hy⟩), ?_⟩
      apply Subtype.ext
      exact hxy.symm
  have hcard : Nat.card ↥D.RG * Nat.card ↥(D.L ⊓ D.M2G) =
      Nat.card ↥(D.TG ⊓ centralizer (D.T0G : Set G)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Equiv.ofBijective f hf)
  rw [card_TG_inf_centralizer_T0G D hF7] at hcard
  rw [show Nat.card ↥(D.L ⊓ D.M2G) = 4 from card_inf_M2G D hF5] at hcard
  omega

theorem isElemAbelian_RG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF7 : F7Prop) (hF8 : F8Prop) :
    IsElemAbelian 2 D.RG := by
  have hEA : IsElemAbelian 2 (D.TG ⊓ centralizer (D.T0G : Set G)) := by
    rw [TG_inf_centralizer_T0G_eq_pull_c0Tabs D]
    exact isElemAbelian_pull_c0Tabs D hF7
  exact hEA.mono (le_inf
    (RG_le_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
    (RG_le_centralizer_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8))

theorem not_isConj_of_mem_RG (hF1 : F1Prop)
    (hF1M : F1MProp) (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop)
    (hF6 : F6Prop) (hF6b : F6bProp) (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop)
    (hF11 : F11Prop) {r : G} (hr : r ∈ D.RG) (hr1 : r ≠ 1) : ¬ IsConj r z := by
  intro hconj
  have hrT : r ∈ D.TG := RG_le_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hr
  have hrC : r ∈ centralizer (D.T0G : Set G) :=
    RG_le_centralizer_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hr
  have hr2 : r * r = 1 := mul_self_eq_one_of_mem_TG_inf D hF7 ⟨hrT, hrC⟩
  have hrT0 : r ∈ D.T0G := mem_T0G_of_isConj D hF4 r hrT hr2 hr1 hconj
  have hrA : r ∈ D.AG := T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hrT0
  have hbot : r ∈ D.RG ⊓ D.AG := ⟨hr, hrA⟩
  rw [RG_inf_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11] at hbot
  exact hr1 (Subgroup.mem_bot.mp hbot)

end CFSG.Sporadic.SuzRecog.SuzL34.LocalData
