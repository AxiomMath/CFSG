module

public import CFSG.RankThree.GF2n.Stroth78.Sec4FiveStepA
public import CFSG.Fischer.Classification.Orthogonal2.Inner
public import CFSG.RankThree.GF2n.Stroth78.Sec4FiveBase

import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

open Sec4Five

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem stroth78_45 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 3 ≤ m)
    {Qf : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Qf x y = 0) → x = 0)
    (hO : fischerLinearModel
      (threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x, Qf (A *ᵥ x) = Qf x)
      (fischerTransvections (QuadraticMap.polar Qf) fun v => Qf v = 1)) :
    False := by
  obtain ⟨α₀, hα₀, hα₀1, hO₀⟩ := exists_mem_Rbar_fischerLinearModel S h h217 h3 hα hO
  have hH := hyp_Wbar S h h217 h3 hα₀ hα₀1
  obtain ⟨hT, hna, hloc⟩ := CFSG.Fischer.Classification.Orth2.orth_pair_facts hH hm hnd hO₀
  obtain ⟨hLS, hLna⟩ := hloc (alphaBar S h hα₀) (alphaBar_mem S h hα₀)
  have hinn : ∀ l : ↥(Lbar S a), ∃ x, actL S h hα₀ l = MulAut.conj x := by
    intro l
    refine CFSG.Fischer.Classification.Orth2.exists_eq_conj_of_fischerLinearModel
      hH.pair.2.2.2.2 hm hnd hO₀ _ fun e =>
        ⟨fun he => actL_mem_threeResidualClass S h hα₀ l he, fun he => ?_⟩
    have := actL_mem_threeResidualClass S h hα₀ l⁻¹ he
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
  by_cases hex : ∃ l : ↥(Lbar S a), ∃ x, actL S h hα₀ l = MulAut.conj x ∧ x ≠ 1 ∧
      x ≠ alphaBar S h hα₀
  · obtain ⟨l, x, hlx, hx1, hxα⟩ := hex
    exact false_of_stroth78_43_data_of_ker S h h217 h3 hα₀ hα₀1
      (derivedSeries_two_le_ker_rhoW_of_actL S h h217 h3 hα₀ hα₀1 hna hT hLS hLna l hlx hx1
        hxα) hT hna hloc
  · push Not at hex
    have hsub : ((actL S h hα₀).range : Set (MulAut _)) ⊆
        ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) := by
      rintro _ ⟨l, rfl⟩
      obtain ⟨x, hx⟩ := hinn l
      by_cases hx1 : x = 1
      · left
        rw [hx, hx1, map_one]
      · right
        rw [hx, hex l x hx hx1]
        rfl
    have h1 : Nat.card ((actL S h hα₀).range : Set (MulAut _)) ≤
        Nat.card ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) :=
      Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)).ncard
          ≤ ({MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)).ncard + 1 :=
            Set.ncard_insert_le _ _
        _ = 1 + 1 := by rw [Set.ncard_singleton]
        _ = 2 := rfl
    have h3' : Nat.card (actL S h hα₀).range ≤ 2 := le_trans (le_of_eq rfl) (h1.trans h2)
    have h4 := card_Lbar_le_two_mul_card_range_actL S h h217 h3 hα₀ hα₀1
    exact false_of_card_Lbar_le_four S h (by omega)

end CFSG.RankThree.GF2n.Stroth78
