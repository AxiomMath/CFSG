module

public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Finset MvPolynomial

theorem quadratic_map_sum_eq {W ι : Type*} [AddCommGroup W] [Module (ZMod 2) W] [LinearOrder ι]
    (Q : W → ZMod 2) (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hQ0 : Q 0 = 0)
    (hQ : ∀ a c, Q (a + c) = Q a + Q c + B a c) (v : ι → W) (s : Finset ι) :
    Q (∑ j ∈ s, v j) = ∑ j ∈ s, Q (v j) + ∑ j ∈ s, ∑ k ∈ s.filter (· < j), B (v k) (v j) := by
  have hsymm : ∀ a c, B a c = B c a := by
    intro a c
    have h1 := hQ a c
    have h2 := hQ c a
    rw [add_comm c a] at h2
    linear_combination h1.symm.trans h2
  induction s using Finset.induction_on_max with
  | empty => simp [hQ0]
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hFa : (insert a s).filter (· < a) = s := by
      rw [Finset.filter_insert, if_neg (lt_irrefl a), Finset.filter_true_of_mem hlt]
    have hFj : ∀ j ∈ s, (insert a s).filter (· < j) = s.filter (· < j) := by
      intro j hj
      rw [Finset.filter_insert, if_neg (not_lt.mpr (hlt j hj).le)]
    have hinner : ∑ j ∈ s, ∑ k ∈ (insert a s).filter (· < j), B (v k) (v j) =
        ∑ j ∈ s, ∑ k ∈ s.filter (· < j), B (v k) (v j) :=
      Finset.sum_congr rfl fun j hj => by rw [hFj j hj]
    have hcross : ∑ j ∈ s, B (v a) (v j) = ∑ k ∈ s, B (v k) (v a) :=
      Finset.sum_congr rfl fun j _ => hsymm _ _
    simp only [Finset.sum_insert ha, hQ, ih, hFa, hinner, map_sum, hcross]
    abel

theorem exists_poly_of_quadratic {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {e : ℕ}
    (b : Module.Basis (Fin e) (ZMod 2) W) (Q : W → ZMod 2) (hQ0 : Q 0 = 0)
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hQ : ∀ a c, Q (a + c) = Q a + Q c + B a c) :
    ∃ P : MvPolynomial (Fin e) (ZMod 2),
      (∀ x : Fin e → ZMod 2, eval x P = Q (∑ j, x j • b j)) ∧ P.totalDegree ≤ 2 := by
  have hsc : ∀ (c : ZMod 2) (v : W), Q (c • v) = c * Q v := by
    intro c v
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl <;> simp [hQ0]
  refine ⟨∑ j, C (Q (b j)) * X j +
    ∑ j, ∑ k ∈ (univ : Finset (Fin e)).filter (· < j), C (B (b k) (b j)) * X k * X j,
    fun x => ?_, ?_⟩
  · have key : Q (∑ j, x j • b j) = ∑ j, Q (x j • b j) +
        ∑ j, ∑ k ∈ (univ : Finset (Fin e)).filter (· < j), B (x k • b k) (x j • b j) :=
      quadratic_map_sum_eq Q B hQ0 hQ (fun j => x j • b j) univ
    rw [key]
    simp only [map_add, map_sum, map_mul, eval_C, eval_X]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by rw [hsc]; ring
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  · have hdeg1 : ∀ (c : ZMod 2) (j : Fin e),
        (C c * X j : MvPolynomial (Fin e) (ZMod 2)).totalDegree ≤ 2 := by
      intro c j
      refine (totalDegree_mul _ _).trans ?_
      simp
    have hdeg2 : ∀ (c : ZMod 2) (j k : Fin e),
        (C c * X k * X j : MvPolynomial (Fin e) (ZMod 2)).totalDegree ≤ 2 := by
      intro c j k
      refine (totalDegree_mul _ _).trans ?_
      have h1 : (C c * X k : MvPolynomial (Fin e) (ZMod 2)).totalDegree ≤ 1 := by
        refine (totalDegree_mul _ _).trans ?_
        simp
      simp only [totalDegree_X]
      omega
    have hsum2 : ∀ (s : Finset (Fin e)) (g : Fin e → MvPolynomial (Fin e) (ZMod 2)),
        (∀ j, (g j).totalDegree ≤ 2) → (∑ j ∈ s, g j).totalDegree ≤ 2 :=
      fun s g hg => (totalDegree_finsetSum s g).trans (Finset.sup_le fun j _ => hg j)
    refine (totalDegree_add _ _).trans (max_le (hsum2 _ _ fun j => hdeg1 _ _) ?_)
    exact hsum2 _ _ fun j => hsum2 _ _ fun k => hdeg2 _ _ _

theorem exists_nonzero_common_zero_of_basis {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {e f : ℕ} (b : Module.Basis (Fin e) (ZMod 2) W) (hdim : 2 * f < e) (Q : Fin f → W → ZMod 2)
    (hQ0 : ∀ i, Q i 0 = 0)
    (hQ : ∀ i, ∃ B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2, ∀ a c, Q i (a + c) = Q i a + Q i c + B a c) :
    ∃ w : W, w ≠ 0 ∧ ∀ i, Q i w = 0 := by
  choose B hB using hQ
  have hP : ∀ i, ∃ P : MvPolynomial (Fin e) (ZMod 2),
      (∀ x : Fin e → ZMod 2, eval x P = Q i (∑ j, x j • b j)) ∧ P.totalDegree ≤ 2 :=
    fun i => exists_poly_of_quadratic b (Q i) (hQ0 i) (B i) (hB i)
  choose P hPeval hPdeg using hP
  have hsum : ∑ i ∈ (univ : Finset (Fin f)), (P i).totalDegree < Fintype.card (Fin e) := by
    rw [Fintype.card_fin]
    calc ∑ i ∈ (univ : Finset (Fin f)), (P i).totalDegree ≤ ∑ _i : Fin f, 2 :=
          Finset.sum_le_sum fun i _ => hPdeg i
      _ = 2 * f := by simp [mul_comm]
      _ < e := hdim
  have hCW : 2 ∣ Fintype.card
      {x : Fin e → ZMod 2 // ∀ i ∈ (univ : Finset (Fin f)), eval x (P i) = 0} := by
    convert char_dvd_card_solutions_of_sum_lt (K := ZMod 2) 2 hsum
  have h0 : ∀ i ∈ (univ : Finset (Fin f)), eval (0 : Fin e → ZMod 2) (P i) = 0 := by
    intro i _
    rw [hPeval i]
    simp [hQ0 i]
  have hpos : 0 < Fintype.card
      {x : Fin e → ZMod 2 // ∀ i ∈ (univ : Finset (Fin f)), eval x (P i) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hcard : 1 < Fintype.card
      {x : Fin e → ZMod 2 // ∀ i ∈ (univ : Finset (Fin f)), eval x (P i) = 0} := by
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, h0⟩
  have hy0 : (y : Fin e → ZMod 2) ≠ 0 := fun h => hy (Subtype.ext h)
  have hrepr := b.repr_sum_self (y : Fin e → ZMod 2)
  refine ⟨∑ j, (y : Fin e → ZMod 2) j • b j, ?_, fun i => ?_⟩
  · intro hw
    apply hy0
    rw [hw, map_zero] at hrepr
    exact hrepr.symm
  · rw [← hPeval i (y : Fin e → ZMod 2)]
    exact y.2 i (Finset.mem_univ i)

theorem exists_nonzero_zero_of_quadratic {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {f : ℕ} (hdim : 2 * f < Module.finrank (ZMod 2) W)
    (Q : Fin f → W → ZMod 2) (hQ0 : ∀ i, Q i 0 = 0)
    (hQ : ∀ i, ∃ B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2,
      ∀ a b, Q i (a + b) = Q i a + Q i b + B a b) :
    ∃ w : W, w ≠ 0 ∧ ∀ i, Q i w = 0 :=
  exists_nonzero_common_zero_of_basis (Module.finBasis (ZMod 2) W) hdim Q hQ0 hQ

end CFSG.RankThree.GF2n.Stroth80
