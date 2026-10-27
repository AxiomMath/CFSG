module

public import CFSG.RankThree.GroupTheory.SteinbergCELinearDefiningWitness
public import CFSG.RankThree.GroupTheory.SteinbergCESymplecticDefiningWitness
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial

theorem half_sq_of_even {a : ℕ} : (2 * a) ^ 2 / 4 = a ^ 2 := by
  rw [show (2 * a) ^ 2 = 4 * a ^ 2 by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem linear_defining_prime_actual_component_parameter_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {n f : ℕ}
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n p f) :
    n = 2 ∨ (n = 3 ∧ 1 ≤ f ∧ f ≤ 3) ∨ (n = 4 ∧ f = 1) := by
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  obtain ⟨⟨-, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hmod
  have e' : (L ⧸ Subgroup.center L) ≃* LinearFlag.projectiveSL n k :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k)
  obtain ⟨φ, hφ, hker⟩ := CFSG.RankThree.CentralLift.exists_top_cover e'
  have hw : ∀ m : ℕ, Even m → 2 ≤ m → m < n →
      f * (m ^ 2 / 4 + (n - m) ^ 2 / 4) ≤ 3 := fun m hm hm2 hmn => by
    obtain ⟨u, -, -, V, -, -, -, hV⟩ :=
      CFSG.RankThree.GroupTheory.linear_defining_prime_central_cover_two_local_rank_witness
        (G := L) ⊤ hp hp3 hk φ hφ hker hm hm2 hmn
    omega
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ (5 ≤ n ∧ n % 2 = 1) ∨ (6 ≤ n ∧ n % 2 = 0) by omega) with
    h | h | h | ⟨h5, hodd⟩ | ⟨h6, heven⟩
  · exact Or.inl h
  · subst h
    have h1 := hw 2 ⟨1, rfl⟩ le_rfl (by norm_num)
    norm_num at h1
    exact Or.inr (Or.inl ⟨rfl, hf, h1⟩)
  · subst h
    have h1 := hw 2 ⟨1, rfl⟩ le_rfl (by norm_num)
    norm_num at h1
    exact Or.inr (Or.inr ⟨rfl, by omega⟩)
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
    have h1 := hw (2 * j) ⟨j, by ring⟩ (by omega) (by omega)
    rw [half_sq_of_even, show 2 * j + 1 - 2 * j = 1 by omega] at h1
    have h2 : 4 ≤ j ^ 2 := by nlinarith
    have : 4 ≤ j ^ 2 + 1 ^ 2 / 4 := by omega
    nlinarith
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 2 := ⟨n / 2 - 1, by omega⟩
    have h1 := hw (2 * j) ⟨j, by ring⟩ (by omega) (by omega)
    rw [half_sq_of_even, show 2 * j + 2 - 2 * j = 2 by omega] at h1
    have h2 : 4 ≤ j ^ 2 := by nlinarith
    have : 5 ≤ j ^ 2 + 2 ^ 2 / 4 := by omega
    nlinarith

theorem symplectic_defining_prime_actual_component_parameter_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {n f : ℕ}
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n p f) : n = 2 ∧ f = 1 := by
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  obtain ⟨⟨-, hf, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hmod
  obtain ⟨φ, hφ, hker⟩ := CFSG.RankThree.CentralLift.exists_top_cover e
  obtain ⟨z, -, -, V, -, -, -, hV⟩ :=
    CFSG.RankThree.GroupTheory.symplectic_defining_prime_central_cover_two_local_rank_witness
      (G := L) ⊤ hp hp3 hn hk φ hφ hker
  have h3 : f * (n * (n - 1) / 2 + 1) ≤ 3 := by omega
  have hn1 : 1 ≤ n * (n - 1) / 2 := by
    have : 2 ≤ n * (n - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hf1 : f = 1 := by
    by_contra hne
    have : 2 ≤ f := by omega
    nlinarith
  subst hf1
  refine ⟨?_, rfl⟩
  by_contra hne
  have h3n : 3 ≤ n := by omega
  have : 3 ≤ n * (n - 1) / 2 := by
    have : 6 ≤ n * (n - 1) := by
      calc 6 = 3 * 2 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul h3n (by omega)
    omega
  omega

end CFSG.RankThree.PartOne
