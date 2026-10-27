module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec3Two
import CFSG.RankThree.GF2n.Stroth78.Sec3Three
public import CFSG.RankThree.GF2n.Stroth78.Sec3One

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem pair_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3) :
    CFSG.Blueprint.Fischer.Pair ↥(Xsub S a) (Subtype.val ⁻¹' Eset S a) := by
  obtain ⟨hne, hroot, -, hclass⟩ := stroth78_31 S h h217
  obtain ⟨α₀, hα₀⟩ := hne
  refine ⟨inferInstance, ⟨⟨α₀, subset_Xsub S a hα₀⟩, ?_⟩, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨c, hc, hcx⟩ := (hclass α₀ hα₀ (x : Hbar z)).1 hx
      exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hcx.symm⟩
    · intro hconj
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      have hc' : (x : Hbar z) = (c : Hbar z) * α₀ * (c : Hbar z)⁻¹ := by
        simpa using (congrArg Subtype.val hc).symm
      exact (hclass α₀ hα₀ (x : Hbar z)).2 ⟨c, c.2, hc'⟩
  · intro e he
    rw [← Subgroup.orderOf_coe]
    exact hroot.1 (e : Hbar z) he
  · intro e he f hf
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    have hle := h3 (e : Hbar z) he (f : Hbar z) hf
    have hpos := orderOf_pos ((e : Hbar z) * (f : Hbar z))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · exact Subgroup.closure_closure_coe_preimage

theorem twoCore_Xsub (S : Setting z E F) {a : G} :
    ∀ N : Subgroup ↥(Xsub S a), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hNn hNp
  haveI : N.Normal := hNn
  have hP2 : IsPGroup 2 (N.map (Xsub S a).subtype) := hNp.map _
  have hPY : N.map (Xsub S a).subtype ≤ Xsub S a := Subgroup.map_subtype_le _
  have hnorm : Xsub S a ≤
      Subgroup.normalizer (N.map (Xsub S a).subtype : Set (Hbar z)) := by
    simpa [Subgroup.normalizer_eq_top N, Subgroup.map_top, Subgroup.range_subtype]
      using Subgroup.le_normalizer_map (H := N) (Xsub S a).subtype
  have hbot := eq_bot_of_le_normalizer_of_isPGroup_two S (Xsub_normal S a) hPY hP2 hnorm
  exact (Subgroup.map_eq_bot_iff_of_injective N (Xsub S a).subtype_injective).1 hbot

theorem threeCore_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    ∀ N : Subgroup ↥(Xsub S a), N.Normal → IsPGroup 3 N →
      N ≤ Subgroup.center ↥(Xsub S a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro N hNn hNp
  haveI : N.Normal := hNn
  let P : Subgroup (Hbar z) := N.map (Xsub S a).subtype
  have hP2 : IsPGroup 3 P := hNp.map _
  have hPY : P ≤ Xsub S a := Subgroup.map_subtype_le _
  have hnorm : Xsub S a ≤ Subgroup.normalizer (P : Set (Hbar z)) := by
    change Xsub S a ≤ Subgroup.normalizer (N.map (Xsub S a).subtype : Set (Hbar z))
    simpa [Subgroup.normalizer_eq_top N, Subgroup.map_top, Subgroup.range_subtype]
      using Subgroup.le_normalizer_map (H := N) (Xsub S a).subtype
  have hPcore : P ≤ pCoreOf 3 (Xsub S a) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 3) hPY hnorm hP2
  have hle : P ≤ centerIn (Xsub S a) :=
    hPcore.trans ((stroth78_32 S h h217).1 3 Nat.prime_three (by norm_num))
  rw [centerIn_eq_map_center] at hle
  exact (Subgroup.map_le_map_iff_of_injective (Xsub S a).subtype_injective).1 hle

theorem hyp_stroth78_36 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) :
    CFSG.Fischer.Classification.Hyp
      ↥(CFSG.GroupTheory.ThreeTranspositions.threeResidualQuot
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (CFSG.GroupTheory.ThreeTranspositions.threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) :=
  CFSG.GroupTheory.ThreeTranspositions.hyp_threeResidualQuot
    (pair_Xsub S h h217 h3) (twoCore_Xsub S) (threeCore_Xsub S h h217)
    (Tset_subset_Eset S a hα)

theorem stroth78_36 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hF : CFSG.Fischer.Classification.Statement)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) :
    CFSG.Fischer.Classification.Conclusion
      ↥(CFSG.GroupTheory.ThreeTranspositions.threeResidualQuot
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (CFSG.GroupTheory.ThreeTranspositions.threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) :=
  CFSG.GroupTheory.ThreeTranspositions.conclusion_threeResidualQuot hF
    (pair_Xsub S h h217 h3) (twoCore_Xsub S) (threeCore_Xsub S h h217)
    (Tset_subset_Eset S a hα)

end CFSG.RankThree.GF2n.Stroth78
