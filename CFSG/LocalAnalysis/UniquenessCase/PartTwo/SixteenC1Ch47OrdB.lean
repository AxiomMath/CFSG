module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_comm_mem_pCoreOf_of_conj_le_M {D : Data G} {V : Subgroup G} (hV : InCalV D.M V)
    {z : G} (hz : z ∈ V) (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z)) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) (hVh : conjSubgroup V h ≤ D.M) {w : G} (hwV : w ∈ V)
    (hw : w ∉ pCoreOf 2 (centralizer ({z} : Set G))) :
    ⁅w, h⁻¹ * w * h⁆ ∈ pCoreOf 2 (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let Q := pCoreOf 2 H
  let U := uOne V z
  have hUleV : U ≤ V := inf_le_left
  have hUleQ : U ≤ Q := inf_le_right
  have hcardU : Nat.card ↥V = 2 * Nat.card ↥U := hcard
  have hwH : w ∈ H := by
    change w ∈ centralizer ({z} : Set G)
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hz)
      ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.2.2.2.1) hwV)
  set x : G := h⁻¹ * w * h with hx
  have hxH : x ∈ H := by
    rw [hx]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hwH) hh
  have hxVh : x ∈ conjSubgroup V h := by
    rw [hx, mem_conjSubgroup_iff]
    have hchain : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    rwa [hchain]
  have hxN : x ∈ normalizer (V : Set G) := hV.2.2.1 (hVh hxVh)
  have hxwxV : x * w * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN w).1 hwV
  have hw_notU : w ∉ U := fun hwu => hw (hUleQ hwu)
  have hxwx_notU : x * w * x⁻¹ ∉ U := by
    intro hxwxU
    have hxwxQ : x * w * x⁻¹ ∈ Q := hUleQ hxwxU
    have hQx : conjSubgroup Q x = Q := s16c1_conjSubgroup_pCoreOf_self H hxH
    have hwQ : w ∈ conjSubgroup Q x := mem_conjSubgroup_iff.mpr hxwxQ
    rw [hQx] at hwQ
    exact hw hwQ
  have hrel : U.relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card (H := U) (K := V)
    rw [inf_eq_left.2 hUleV, hcardU] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hindex : (U.subgroupOf V).index = 2 := hrel
  have ha_not : (⟨w, hwV⟩ : ↥V)⁻¹ ∉ U.subgroupOf V := by
    intro ha
    have h1 : w⁻¹ ∈ U := by
      simpa using (Subgroup.mem_subgroupOf (H := U) (K := V)).mp ha
    exact hw_notU (by simpa using U.inv_mem h1)
  have hb_not : (⟨x * w * x⁻¹, hxwxV⟩ : ↥V) ∉ U.subgroupOf V := by
    intro hb
    exact hxwx_notU (by
      simpa using (Subgroup.mem_subgroupOf (H := U) (K := V)).mp hb)
  have hab : (⟨w, hwV⟩ : ↥V)⁻¹ * ⟨x * w * x⁻¹, hxwxV⟩ ∈ U.subgroupOf V := by
    rw [Subgroup.mul_mem_iff_of_index_two hindex]
    exact ⟨fun ha => absurd ha ha_not, fun hb => absurd hb hb_not⟩
  have hmemU : w⁻¹ * (x * w * x⁻¹) ∈ U := by
    simpa using (Subgroup.mem_subgroupOf (H := U) (K := V)).mp hab
  have hw2 : w ^ 2 = 1 := hV.2.2.2.2 w hwV
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw2)
  have hcomm : ⁅w, x⁆ = w⁻¹ * (x * w * x⁻¹) := by
    rw [commutatorElement_def, hw_inv]
    group
  rw [hcomm]
  exact hUleQ hmemU

theorem s16c1_not_le_of_noncomm {D : Data G} {V : Subgroup G} (hV : InCalV D.M V) {z : G}
    (hz : z ∈ V) (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z)) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) {w : G} (hwV : w ∈ V)
    (hw : w ∉ pCoreOf 2 (centralizer ({z} : Set G)))
    (hnc : ⁅w, h⁻¹ * w * h⁆ ∉ pCoreOf 2 (centralizer ({z} : Set G))) :
    ¬ conjSubgroup V h ≤ D.M ∧ ¬ V ≤ conjSubgroup D.M h := by
  let H := centralizer ({z} : Set G)
  let Q := pCoreOf 2 H
  constructor
  · intro hle
    exact hnc (s16c1_comm_mem_pCoreOf_of_conj_le_M hV hz hcard hh hle hwV hw)
  · intro hle
    have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
    have hVh_inv : conjSubgroup V h⁻¹ ≤ D.M := by
      calc conjSubgroup V h⁻¹
          ≤ conjSubgroup (conjSubgroup D.M h) h⁻¹ := E3.conjSubgroup_mono_left h⁻¹ hle
        _ = conjSubgroup D.M (h * h⁻¹) := conjSubgroup_conjSubgroup D.M h h⁻¹
        _ = conjSubgroup D.M 1 := by rw [mul_inv_cancel]
        _ = D.M := conjSubgroup_one D.M
    have ht : ⁅w, h * w * h⁻¹⁆ ∈ Q := by
      simpa using
        s16c1_comm_mem_pCoreOf_of_conj_le_M hV hz hcard hh_inv hVh_inv hwV hw
    have hQh : conjSubgroup Q h⁻¹ = Q := s16c1_conjSubgroup_pCoreOf_self H hh_inv
    have hconj : h⁻¹ * ⁅w, h * w * h⁻¹⁆ * h ∈ Q := by
      have hmem : ⁅w, h * w * h⁻¹⁆ ∈ conjSubgroup Q h⁻¹ := by rwa [hQh]
      have := mem_conjSubgroup_iff.mp hmem
      simpa using this
    have heq : h⁻¹ * ⁅w, h * w * h⁻¹⁆ * h = ⁅w, h⁻¹ * w * h⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq] at hconj
    exact hnc (by simpa using Q.inv_mem hconj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
