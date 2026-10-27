module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.Quasithin.Fan86

namespace P72

open Subgroup

variable {G : Type*} [Group G]

theorem closure_insert_le {T : Subgroup G} [Finite T] {y : G} (hy : y * y = 1)
    (hc : ∀ t ∈ T, y * t = t * y) :
    Finite ↥(closure (insert y (T : Set G))) ∧
      Nat.card ↥(closure (insert y (T : Set G))) ≤ 2 * Nat.card T := by
  have hcomm : ∀ a : G, y * a ∈ T → y * a = a * y := by
    intro a ha
    have h1 := hc _ ha
    have h2 : y * (y * a) = a := by rw [← mul_assoc, hy, one_mul]
    rw [h2] at h1
    calc y * a = y * a * (y * y) := by rw [hy, mul_one]
      _ = (y * a * y) * y := by rw [mul_assoc (y * a) y y]
      _ = a * y := by rw [← h1]
  have hP : ∀ g ∈ closure (insert y (T : Set G)), g ∈ T ∨ y * g ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | hg
      · right
        rw [hy]
        exact T.one_mem
      · exact Or.inl hg
    | one => exact Or.inl T.one_mem
    | mul a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (T.mul_mem ha hb)
      · right
        rw [← mul_assoc, hc a ha, mul_assoc]
        exact T.mul_mem ha hb
      · right
        rw [← mul_assoc]
        exact T.mul_mem ha hb
      · left
        have e : (y * a) * (y * b) = a * b :=
          calc (y * a) * (y * b) = y * (a * y) * b := by simp only [mul_assoc]
            _ = y * (y * a) * b := by rw [← hcomm a ha]
            _ = a * b := by rw [← mul_assoc y y a, hy, one_mul]
        rw [← e]
        exact T.mul_mem ha hb
    | inv a _ ha =>
      rcases ha with ha | ha
      · exact Or.inl (T.inv_mem ha)
      · right
        have e : y * a⁻¹ = (y * a)⁻¹ := by
          rw [hcomm a ha, mul_inv_rev, inv_eq_of_mul_eq_one_right hy]
        rw [e]
        exact T.inv_mem ha
  have hsub : (closure (insert y (T : Set G)) : Set G) ⊆
      (T : Set G) ∪ (fun t => y * t) '' (T : Set G) := by
    intro g hg
    rcases hP g hg with h | h
    · exact Or.inl h
    · right
      refine ⟨y * g, h, ?_⟩
      show y * (y * g) = g
      rw [← mul_assoc, hy, one_mul]
  have hfinT : (T : Set G).Finite := Set.toFinite _
  have hfinU : ((T : Set G) ∪ (fun t => y * t) '' (T : Set G)).Finite :=
    hfinT.union (hfinT.image _)
  refine ⟨(hfinU.subset hsub).to_subtype, ?_⟩
  have hn : Nat.card ↥(closure (insert y (T : Set G))) =
      (closure (insert y (T : Set G)) : Set G).ncard := Nat.card_coe_set_eq _
  have hT : Nat.card ↥T = (T : Set G).ncard := Nat.card_coe_set_eq _
  rw [hn, hT]
  calc (closure (insert y (T : Set G)) : Set G).ncard
      ≤ ((T : Set G) ∪ (fun t => y * t) '' (T : Set G)).ncard := Set.ncard_le_ncard hsub hfinU
    _ ≤ (T : Set G).ncard + ((fun t => y * t) '' (T : Set G)).ncard := Set.ncard_union_le _ _
    _ ≤ (T : Set G).ncard + (T : Set G).ncard :=
        Nat.add_le_add_left (Set.ncard_image_le hfinT) _
    _ = 2 * (T : Set G).ncard := by omega

theorem card_closure_le (S : Finset G) (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hi : ∀ x ∈ S, x * x = 1) :
    Finite ↥(closure (S : Set G)) ∧ Nat.card ↥(closure (S : Set G)) ≤ 2 ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Subgroup.closure_empty, Finset.card_empty, pow_zero]
    refine ⟨inferInstance, ?_⟩
    simp
  | insert y S hy ih =>
    have hc' : ∀ x ∈ S, ∀ z ∈ S, x * z = z * x := fun x hx z hz =>
      hc x (Finset.mem_insert_of_mem hx) z (Finset.mem_insert_of_mem hz)
    have hi' : ∀ x ∈ S, x * x = 1 := fun x hx => hi x (Finset.mem_insert_of_mem hx)
    obtain ⟨hfin, hcard⟩ := ih hc' hi'
    have hyc : ∀ t ∈ closure (S : Set G), y * t = t * y := by
      intro t ht
      have hle : closure (S : Set G) ≤ Subgroup.centralizer {y} := (Subgroup.closure_le _).2 (by
        intro s hs
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hc y (Finset.mem_insert_self _ _) s (Finset.mem_insert_of_mem hs))
      exact Subgroup.mem_centralizer_iff.1 (hle ht) y rfl
    obtain ⟨hf2, hc2⟩ := closure_insert_le (T := closure (S : Set G))
      (hi y (Finset.mem_insert_self y S)) hyc
    have hle : closure ((insert y S : Finset G) : Set G) ≤
        closure (insert y ((closure (S : Set G) : Subgroup G) : Set G)) :=
      closure_mono (by
        rw [Finset.coe_insert]
        exact Set.insert_subset_insert subset_closure)
    refine ⟨Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle), ?_⟩
    calc Nat.card ↥(closure ((insert y S : Finset G) : Set G))
        ≤ Nat.card ↥(closure (insert y ((closure (S : Set G) : Subgroup G) : Set G))) :=
          Subgroup.card_le_of_le hle
      _ ≤ 2 * Nat.card ↥(closure (S : Set G)) := hc2
      _ ≤ 2 * 2 ^ S.card := Nat.mul_le_mul_left 2 hcard
      _ = 2 ^ (insert y S).card := by rw [Finset.card_insert_of_notMem hy, pow_succ']

end P72

end CFSG.Quasithin.Fan86
