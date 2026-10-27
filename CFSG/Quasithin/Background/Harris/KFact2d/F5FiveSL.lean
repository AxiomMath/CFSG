module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open Matrix
open scoped MatrixGroups

theorem card_center_sl2_five_le : Nat.card (Subgroup.center SL(2, ZMod 5)) ≤ 2 := by
  have hinj : Function.Injective (fun A : Subgroup.center SL(2, ZMod 5) =>
      (⟨(A.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0, by
        obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp A.2
        have h00 := congrFun (congrFun hA 0) 0
        simp at h00
        rw [← h00]
        have : ∀ r : ZMod 5, r ^ 2 = 1 → r ^ 2 = 1 := fun r h => h
        simpa using this r (by simpa using hr)⟩ : { r : ZMod 5 // r ^ 2 = 1 })) := by
    intro A B hAB
    have h00 : (A.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = (B.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 :=
      congrArg Subtype.val hAB
    obtain ⟨r, -, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp A.2
    obtain ⟨s, -, hB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp B.2
    have hr : r = (A.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 := by
      have := congrFun (congrFun hA 0) 0
      simpa using this
    have hs : s = (B.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 := by
      have := congrFun (congrFun hB 0) 0
      simpa using this
    have hrs : r = s := by rw [hr, hs, h00]
    apply Subtype.ext
    apply Subtype.ext
    rw [← hA, ← hB, hrs]
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card { r : ZMod 5 // r ^ 2 = 1 } = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  omega

theorem card_sl2_five : Nat.card SL(2, ZMod 5) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.card_SL_field (𝔽 := ZMod 5) 2
  rw [← Nat.card_eq_fintype_card] at h
  simpa [ZMod.card, Fin.prod_univ_two] using h

theorem card_normal_sl2_five_le (N : Subgroup SL(2, ZMod 5)) [N.Normal] (hN : Nat.card N ≤ 48) :
    Nat.card N ≤ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h4 : ∃ s : Finset (ZMod 5), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod 5)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨s, hs⟩
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 5) (n := 2) le_rfl
    (Or.inr h4)).2.1
  let mk := QuotientGroup.mk' (Subgroup.center SL(2, ZMod 5))
  have : (N.map mk).Normal := Subgroup.Normal.map inferInstance mk (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map mk) with h | h
  · have hle : N ≤ Subgroup.center SL(2, ZMod 5) := by
      intro x hx
      have hm : mk x ∈ N.map mk := ⟨x, hx, rfl⟩
      rw [h] at hm
      simpa [mk, QuotientGroup.eq_one_iff] using hm
    exact (Subgroup.card_le_of_le hle).trans card_center_sl2_five_le
  · exfalso
    have hsurj : Function.Surjective (fun q : N × Subgroup.center SL(2, ZMod 5) => (q.1 : SL(2, ZMod 5)) * q.2) := by
      intro s
      have hm : mk s ∈ N.map mk := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hns⟩ := hm
      have hc : (n⁻¹ * s) ∈ Subgroup.center SL(2, ZMod 5) := by
        have : mk (n⁻¹ * s) = 1 := by
          rw [map_mul, map_inv, hns, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      exact ⟨(⟨n, hn⟩, ⟨_, hc⟩), by simp⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, card_sl2_five] at h1
    have h2 := card_center_sl2_five_le
    nlinarith

theorem sl2_five_hom_trivial {H : Type*} [Group H] [Group.IsSolvable H]
    (f : SL(2, ZMod 5) →* H) : f = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h4 : ∃ s : Finset (ZMod 5), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod 5)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨s, hs⟩
  have hperf : commutator SL(2, ZMod 5) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect h4).commutator_eq_top
  have hds : ∀ n, derivedSeries SL(2, ZMod 5) n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero _
    | succ n ih => rw [derivedSeries_succ, ih]; exact hperf
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := H)
  ext x
  have h1 := map_derivedSeries_le_derivedSeries f n
  have hx : f x ∈ (derivedSeries SL(2, ZMod 5) n).map f := ⟨x, by rw [hds n]; exact Subgroup.mem_top _, rfl⟩
  have := h1 hx
  rw [hn] at this
  simpa using this

end CFSG.Quasithin.Background.Harris.KFact2d
