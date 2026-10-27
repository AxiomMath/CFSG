module

public import CFSG.Monster.B.Geometry.Census
public import CFSG.Monster.B.Geometry.F4Weyl

public section

namespace CFSG.Monster.B.Geometry

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

@[expose] def f4q (i : Fin Tag.F4.rank) : ℕ := if (i : ℕ) < 2 then 2 else 4

@[expose] def f4WeightSumOff (m : ℕ) : ℕ :=
  ((List.range 1152).map fun k =>
    if (f4Word k).all (fun l => (l : ℕ) != m) then wordWeight f4q (f4Word k) else 0).sum

theorem f4WeightSum_eq : f4WeightSumOff 4 = 371231385525 := by decide +kernel

theorem f4WeightSumOff_eq :
    f4WeightSumOff 0 = 93555 ∧ f4WeightSumOff 1 = 315 ∧ f4WeightSumOff 2 = 105 ∧
      f4WeightSumOff 3 = 16065 := by decide +kernel

theorem sum_range_eq_list (f : ℕ → ℕ) (n : ℕ) :
    ∑ k : Fin n, f k = ((List.range n).map f).sum := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range,
    Multiset.map_coe, Multiset.sum_coe]

section Building

variable {C : Type*} {δ : C → C → WeylGroup .F4}
  (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
  (hpanel : ∀ i x, (panel (coxeterSystem .F4) δ i x).encard = f4q i + 1)
include hδ hpanel

theorem finsum_weylWeight_off (m : ℕ) :
    ∑ᶠ w ∈ ((coxeterSystem .F4).parabolic {i | (i : ℕ) ≠ m} : Set (WeylGroup .F4)),
      weylWeight (coxeterSystem .F4) f4q w = f4WeightSumOff m := by
  classical
  rw [finsum_mem_def, sum_f4, f4WeightSumOff, ← sum_range_eq_list]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hred := isReduced_f4Word k.2
  rw [Set.indicator_apply]
  have hmem : f4Elem k ∈ ((coxeterSystem .F4).parabolic {i | (i : ℕ) ≠ m} : Set _) ↔
      (f4Word k).all (fun l => (l : ℕ) != m) = true := by
    rw [SetLike.mem_coe, f4Elem, mem_parabolic_iff_of_isReduced _ hred]
    simp [List.all_eq_true]
  by_cases h : (f4Word k).all (fun l => (l : ℕ) != m) = true
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h, f4Elem, weylWeight_wordProd hδ hpanel hred]
  · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]

theorem finsum_weylWeight_f4 :
    ∑ᶠ w, weylWeight (coxeterSystem .F4) f4q w = 371231385525 := by
  have h := finsum_weylWeight_off hδ hpanel 4
  have huniv : {i : Fin Tag.F4.rank | (i : ℕ) ≠ 4} = Set.univ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have := i.2
    change (i : ℕ) < 4 at this
    omega
  rw [huniv, CoxeterSystem.parabolic_univ, Subgroup.coe_top, finsum_mem_univ,
    f4WeightSum_eq] at h
  exact h

end Building

theorem F4_two_four_building_census
    {C : Type*} {δ : C → C → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hpanel : ∀ (i : Fin Tag.F4.rank) (x : C),
      (panel (coxeterSystem .F4) δ i x).encard = if (i : ℕ) < 2 then 3 else 5) :
    Nat.card C = 371231385525 ∧
    (∀ x : C, (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 0} x).ncard = 93555) ∧
    (∀ x : C, (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 1} x).ncard = 315) ∧
    (∀ x : C, (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 2} x).ncard = 105) ∧
    (∀ x : C, (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 3} x).ncard = 16065) ∧
    (Set.range (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 0})).ncard = 3968055 ∧
    (Set.range (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 1})).ncard = 1178512335 ∧
    (Set.range (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 2})).ncard = 3535537005 ∧
    (Set.range (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ 3})).ncard = 23108085 ∧
    ∀ (H : Type*) [Group H] [MulAction H C] [MulAction.IsPretransitive H C] (a : C),
      Nat.card (MulAction.stabilizer H a) = 824633720832 →
        Nat.card H = 306129918735099415756800 := by
  have hq : ∀ i x, (panel (coxeterSystem .F4) δ i x).encard = f4q i + 1 := by
    intro i x
    rw [hpanel i x, f4q]
    split_ifs <;> rfl
  have htot := finsum_weylWeight_f4 hδ hq
  obtain ⟨-, hcard⟩ := card_eq_finsum_weylWeight hδ hq
  obtain ⟨h0, h1, h2, h3⟩ := f4WeightSumOff_eq
  have hres : ∀ m x, (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ m} x).ncard =
      f4WeightSumOff m := fun m x => by
    rw [ncard_residue_eq_finsum hδ hq, finsum_weylWeight_off hδ hq]
  have hnum : ∀ m, (Set.range (residue (coxeterSystem .F4) δ {i | (i : ℕ) ≠ m})).ncard =
      371231385525 / f4WeightSumOff m := fun m => by
    rw [ncard_range_residue_eq_div hδ hq, finsum_weylWeight_off hδ hq, htot]
  refine ⟨by rw [hcard, htot], fun x => by rw [hres, h0], fun x => by rw [hres, h1],
    fun x => by rw [hres, h2], fun x => by rw [hres, h3], by rw [hnum, h0],
    by rw [hnum, h1], by rw [hnum, h2], by rw [hnum, h3], ?_⟩
  intro H _ _ _ a ha
  rw [card_eq_card_stabilizer_mul hδ hq a, ha, htot]

end CFSG.Monster.B.Geometry
