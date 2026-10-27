module

public import CFSG.RankThree.GF2n.Stroth78.Sec4FiveStepA
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six

import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec3Six
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjModel
import CFSG.Fischer.Classification.Symmetric.LocalData
import CFSG.Fischer.Classification.Symmetric.Inner

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification
open Sec4Five (derivedSeries_two_le_ker_rhoW_of_actL)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4OneW

theorem exists_mem_Rbar_isConj (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
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
    ∃ α₀ : Hbar z, ∃ hα₀ : α₀ ∈ Rbar S a, α₀ ≠ 1 ∧
      IsConj (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))
        (alphaInX S h hα₀) := by
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀E : α₀ ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1')
  obtain ⟨-, ⟨e, hE⟩, -, -, -⟩ := pair_Xsub S h h217 h3
  have hd : (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ∈
      (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := Tset_subset_Eset S a hα
  have hd₀E : alphaInX S h hα₀R ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := hα₀E
  rw [hE] at hd hd₀E
  exact ⟨α₀, hα₀R, hα₀1', (isConj_comm.1 hd).trans hd₀E⟩

theorem false_of_pair_facts_of_inner (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hT : TripleProperty (threeResidualClass (alphaInX S h hα)))
    (hna : NonabelianCommutator ↥(threeResidualQuot (alphaInX S h hα)))
    (hloc : ∀ e ∈ threeResidualClass (alphaInX S h hα),
      IsSimpleGroup (commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e)) ∧
        ∃ x y : commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e),
          x * y ≠ y * x)
    (hinn : ∀ l : ↥(Lbar S a), ∃ x, actL S h hα l = MulAut.conj x) : False := by
  obtain ⟨hLS, hLna⟩ := hloc (alphaBar S h hα) (alphaBar_mem S h hα)
  by_cases hex : ∃ l : ↥(Lbar S a), ∃ x, actL S h hα l = MulAut.conj x ∧ x ≠ 1 ∧
      x ≠ alphaBar S h hα
  · obtain ⟨l, x, hlx, hx1, hxα⟩ := hex
    exact false_of_stroth78_43_data_of_ker S h h217 h3 hα hα1
      (derivedSeries_two_le_ker_rhoW_of_actL S h h217 h3 hα hα1 hna hT hLS hLna l hlx hx1
        hxα) hT hna hloc
  · push Not at hex
    have hsub : ((actL S h hα).range : Set (MulAut _)) ⊆
        ({1, MulAut.conj (alphaBar S h hα)} : Set (MulAut _)) := by
      rintro _ ⟨l, rfl⟩
      obtain ⟨x, hx⟩ := hinn l
      by_cases hx1 : x = 1
      · left
        rw [hx, hx1, map_one]
      · right
        rw [hx, hex l x hx hx1]
        rfl
    have h1 : Nat.card ((actL S h hα).range : Set (MulAut _)) ≤
        Nat.card ({1, MulAut.conj (alphaBar S h hα)} : Set (MulAut _)) :=
      Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card ({1, MulAut.conj (alphaBar S h hα)} : Set (MulAut _)) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc ({1, MulAut.conj (alphaBar S h hα)} : Set (MulAut _)).ncard
          ≤ ({MulAut.conj (alphaBar S h hα)} : Set (MulAut _)).ncard + 1 :=
            Set.ncard_insert_le _ _
        _ = 1 + 1 := by rw [Set.ncard_singleton]
        _ = 2 := rfl
    have h3' : Nat.card (actL S h hα).range ≤ 2 := le_trans (le_of_eq rfl) (h1.trans h2)
    have h4 := card_Lbar_le_two_mul_card_range_actL S h h217 h3 hα hα1
    exact false_of_card_Lbar_le_four S h (by omega)

end Sec4OneW

open Sec4OneW in
theorem stroth78_41 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 7 ≤ m)
    (φ : ↥(threeResidualQuot
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) ≃* Equiv.Perm (Fin m))
    (hφ : ∀ g, g ∈ threeResidualClass
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ↔ (φ g).IsSwap) :
    False := by
  obtain ⟨α₀, hα₀, hα₀1, hc⟩ := exists_mem_Rbar_isConj S h h217 h3 hα
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_threeResidualQuot_of_isConj hc φ hφ
  obtain ⟨hT, hna, hloc⟩ := SymPair.sym_pair_facts hm φ₀ hφ₀
  refine false_of_pair_facts_of_inner S h h217 h3 hα₀ hα₀1 hT hna hloc fun l => ?_
  refine SymPair.exists_eq_conj_of_mulEquiv_perm (by omega) φ₀ hφ₀ _ fun e =>
    ⟨fun he => actL_mem_threeResidualClass S h hα₀ l he, fun he => ?_⟩
  have := actL_mem_threeResidualClass S h hα₀ l⁻¹ he
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

end CFSG.RankThree.GF2n.Stroth78
