module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

open MvPolynomial

theorem quadMap_sum {A K : Type*} [AddCommGroup A] [AddCommGroup K] {d : ℕ} (q : A → K)
    (β : A →+ A →+ K) (hq : ∀ x y, q (x + y) = q x + q y + β x y) (hq0 : q 0 = 0)
    (y : Fin d → A) (s : Finset (Fin d)) :
    q (∑ i ∈ s, y i) = ∑ i ∈ s, q (y i) + ∑ i ∈ s, ∑ k ∈ s, if i < k then β (y i) (y k) else 0 := by
  induction s using Finset.induction_on_min with
  | empty => simp [hq0]
  | insert m s hlt ih =>
    have hm : m ∉ s := fun h => lt_irrefl _ (hlt m h)
    rw [Finset.sum_insert hm, hq, ih, Finset.sum_insert hm, Finset.sum_insert hm]
    have h1 : ∑ k ∈ insert m s, (if m < k then β (y m) (y k) else 0) = ∑ k ∈ s, β (y m) (y k) := by
      rw [Finset.sum_insert hm, if_neg (lt_irrefl _)]
      rw [zero_add]
      exact Finset.sum_congr rfl fun k hk => if_pos (hlt k hk)
    have h2 : ∀ i ∈ s, ∑ k ∈ insert m s, (if i < k then β (y i) (y k) else 0) =
        ∑ k ∈ s, if i < k then β (y i) (y k) else 0 := by
      intro i hi
      rw [Finset.sum_insert hm, if_neg (not_lt.mpr (le_of_lt (hlt i hi))), zero_add]
    rw [h1, Finset.sum_congr rfl h2, map_sum]
    abel

theorem card_le_sq_of_anisotropic {A K : Type} [AddCommGroup A] [Finite A] [Field K] [Finite K]
    [CharP K 2] (hA : ∀ x : A, x + x = 0) (q : A → K) (β : A →+ A →+ K)
    (hq : ∀ x y, q (x + y) = q x + q y + β x y) (hani : ∀ x, q x = 0 → x = 0) :
    Nat.card A ≤ Nat.card K ^ 2 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype K := Fintype.ofFinite K
  letI : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (n := 2) fun x => by rw [two_nsmul]; exact hA x
  letI : Module (ZMod 2) K :=
    AddCommGroup.zmodModule (n := 2) fun x => by rw [two_nsmul]; exact CharTwo.add_self_eq_zero x
  have hq0 : q 0 = 0 := by simpa using hq 0 0
  let bA := Module.finBasis (ZMod 2) A
  let bK := Module.finBasis (ZMod 2) K
  have hAc : Nat.card A = 2 ^ Module.finrank (ZMod 2) A := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
    simpa using this
  have hKc : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    simpa using this
  by_contra hcon
  push Not at hcon
  rw [hAc, hKc, ← pow_mul] at hcon
  have h2m : 2 * Module.finrank (ZMod 2) K < Module.finrank (ZMod 2) A := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcon
    omega
  set d := Module.finrank (ZMod 2) A with hd
  set m := Module.finrank (ZMod 2) K with hm
  let a : Fin d → A := fun i => bA i
  let c : Fin m → K →+ ZMod 2 := fun j => (bK.coord j).toAddMonoidHom
  let P : Fin m → MvPolynomial (Fin d) (ZMod 2) := fun j =>
    ∑ i, C (c j (q (a i))) * X i +
      ∑ i, ∑ k, if i < k then C (c j (β (a i) (a k))) * (X i * X k) else 0
  have hdeg : ∀ j, (P j).totalDegree ≤ 2 := by
    intro j
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_C, totalDegree_X]
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k _ => ?_)
      split_ifs
      · refine (totalDegree_mul _ _).trans ?_
        refine (add_le_add (totalDegree_C _).le (totalDegree_mul _ _)).trans ?_
        simp [totalDegree_X]
      · simp
  have hsum : (∑ j, (P j).totalDegree) < Fintype.card (Fin d) := by
    calc ∑ j, (P j).totalDegree ≤ ∑ _j : Fin m, 2 := Finset.sum_le_sum fun j _ => hdeg j
      _ = 2 * m := by simp [mul_comm]
      _ < d := h2m
      _ = Fintype.card (Fin d) := (Fintype.card_fin d).symm
  have hdvd := char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod 2) (σ := Fin d) 2
    (f := P) hsum
  have hqz : ∀ (z : ZMod 2) (u : A) (j : Fin m), c j (q (z • u)) = z * c j (q u) := by
    intro z u j
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
    · simp [hq0]
    · simp
  have hβz : ∀ (z w : ZMod 2) (u v : A) (j : Fin m),
      c j (β (z • u) (w • v)) = z * w * c j (β u v) := by
    intro z w u v j
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl <;>
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) w with rfl | rfl <;> simp
  have hev : ∀ (x : Fin d → ZMod 2) (j : Fin m),
      c j (q (bA.equivFun.symm x)) = eval x (P j) := by
    intro x j
    have hsymm : bA.equivFun.symm x = ∑ i, x i • a i := by
      simp [a, Module.Basis.equivFun_symm_apply]
    have hP : eval x (P j) = ∑ i, c j (q (a i)) * x i +
        ∑ i, ∑ k, if i < k then c j (β (a i) (a k)) * (x i * x k) else 0 := by
      simp only [P, map_add, map_sum, eval_mul, eval_C, eval_X, apply_ite (eval x), map_zero]
    have hL : c j (q (bA.equivFun.symm x)) = ∑ i, x i * c j (q (a i)) +
        ∑ i, ∑ k, if i < k then x i * x k * c j (β (a i) (a k)) else 0 := by
      rw [hsymm, quadMap_sum q β hq hq0 (fun i => x i • a i) Finset.univ, map_add, map_sum,
        map_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => hqz _ _ _
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hik : i < k
        · simp only [hik, if_true, hβz]
        · simp only [hik, if_false, map_zero]
    rw [hL, hP]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      split_ifs
      · ring
      · rfl
  have hex : ∃ x : Fin d → ZMod 2, x ≠ 0 ∧ ∀ j, eval x (P j) = 0 := by
    by_contra hno
    push Not at hno
    have h1 : Nat.card {x : Fin d → ZMod 2 // ∀ j, eval x (P j) = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_⟩, ⟨⟨0, fun j => ?_⟩⟩⟩
      · have hx0 : x = 0 := by
          by_contra hne
          obtain ⟨j, hj⟩ := hno x (by simpa using hne)
          exact hj (hx j)
        have hy0 : y = 0 := by
          by_contra hne
          obtain ⟨j, hj⟩ := hno y (by simpa using hne)
          exact hj (hy j)
        subst hx0; subst hy0; rfl
      · have := hev 0 j
        rw [← this]
        simp [show bA.equivFun.symm 0 = 0 from map_zero _, hq0]
    have h2 : 2 ∣ Nat.card {x : Fin d → ZMod 2 // ∀ j, eval x (P j) = 0} := by
      rw [Nat.card_eq_fintype_card]
      convert hdvd
    rw [h1] at h2
    omega
  obtain ⟨x, hx0, hxz⟩ := hex
  have hu0 : bA.equivFun.symm x ≠ 0 := fun h =>
    hx0 ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hqu : q (bA.equivFun.symm x) = 0 := by
    refine bK.ext_elem fun j => ?_
    have := hev x j
    rw [hxz j] at this
    simpa [c] using this
  exact hu0 (hani _ hqu)

end CFSG.RankThree.GF2n.Stroth80
