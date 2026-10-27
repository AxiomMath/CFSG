module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsComm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Symplectic

section Weyl

theorem reflection_five_zero_apply (v : Fin 2 → ℤ) :
    reflection (Unitary.cartan 5) 0 v = ![-v 0 + v 1, v 1] := by
  funext k
  fin_cases k
  · simp [reflection_apply, Unitary.cartan, Symplectic.cartanC, Fin.sum_univ_two,
      show ¬ Even 5 by decide]
    ring
  · simp [reflection_apply, Unitary.cartan, Symplectic.cartanC, Fin.sum_univ_two,
      show ¬ Even 5 by decide]

theorem reflection_five_one_apply (v : Fin 2 → ℤ) :
    reflection (Unitary.cartan 5) 1 v = ![v 0, 2 * v 0 - v 1] := by
  funext k
  fin_cases k
  · simp [reflection_apply, Unitary.cartan, Symplectic.cartanC, Fin.sum_univ_two,
      show ¬ Even 5 by decide]
  · simp [reflection_apply, Unitary.cartan, Symplectic.cartanC, Fin.sum_univ_two,
      show ¬ Even 5 by decide]
    ring

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem conjBy_octGroup_simple_un5 {m : SU (unitaryInvolution F p f) 5} {k : Fin 2}
    (hm : ActsAs (rootDatum hF 5) m
      ((coxeterMatrix (rootDatum hF 5).isFiniteType).toCoxeterSystem.simple k)) {i : ℤ}
    (hi : IsRoot 4 i) :
    conjBy m (un5Oct hF i) =
      (rootDatum hF 5).rootGroup (reflection (Unitary.cartan 5) k (octRootB i)) :=
  map_conj_inv_simple (rootDatum hF 5) hm (octRootB_mem_roots' hi)

theorem un5Action₁ {m : SU (unitaryInvolution F p f) 5}
    (hm : ActsAs (rootDatum hF 5) m
      ((coxeterMatrix (rootDatum hF 5).isFiniteType).toCoxeterSystem.simple (0 : Fin 2))) :
    conjBy m (un5Oct hF 1) = un5Oct hF (-1) ∧ conjBy m (un5Oct hF (-1)) = un5Oct hF 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 4 →
        conjBy m (un5Oct hF i) = un5Oct hF (((4 : ℕ) : ℤ) + 2 - i) ∧
          conjBy m (un5Oct hF (-i)) = un5Oct hF (-(((4 : ℕ) : ℤ) + 2 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (Unitary.cartan 5) 0 (octRootB i) = octRootB j →
      conjBy m (un5Oct hF i) = un5Oct hF j := fun hi hj =>
    (conjBy_octGroup_simple_un5 hF hm hi).trans (congrArg (rootDatum hF 5).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h2 h4 => ?_⟩
  · rw [reflection_five_zero_apply, octRootB_one, octRootB_neg_one]
    simp
  · rw [reflection_five_zero_apply, octRootB_neg_one, octRootB_one]
    simp
  · rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl
    · rw [show ((4 : ℕ) : ℤ) + 2 - 2 = 4 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_zero_apply, octRootB_two, octRootB_four]
        simp
      · rw [reflection_five_zero_apply, octRootB_neg_two, octRootB_neg_four]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 3 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_zero_apply, octRootB_three]
        simp
      · rw [reflection_five_zero_apply, octRootB_neg_three]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 4 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_zero_apply, octRootB_four, octRootB_two]
        simp
      · rw [reflection_five_zero_apply, octRootB_neg_four, octRootB_neg_two]
        simp

theorem un5Action₂ {m : SU (unitaryInvolution F p f) 5}
    (hm : ActsAs (rootDatum hF 5) m
      ((coxeterMatrix (rootDatum hF 5).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (un5Oct hF 4) = un5Oct hF (-4) ∧ conjBy m (un5Oct hF (-4)) = un5Oct hF 4 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy m (un5Oct hF i) = un5Oct hF (4 - i) ∧
        conjBy m (un5Oct hF (-i)) = un5Oct hF (-(4 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (Unitary.cartan 5) 1 (octRootB i) = octRootB j →
      conjBy m (un5Oct hF i) = un5Oct hF j := fun hi hj =>
    (conjBy_octGroup_simple_un5 hF hm hi).trans (congrArg (rootDatum hF 5).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h1 h3 => ?_⟩
  · rw [reflection_five_one_apply, octRootB_four, octRootB_neg_four]
    simp
  · rw [reflection_five_one_apply, octRootB_neg_four, octRootB_four]
    simp
  · rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [show (4 : ℤ) - 1 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_one_apply, octRootB_one, octRootB_three]
        simp
      · rw [reflection_five_one_apply, octRootB_neg_one, octRootB_neg_three]
        simp
    · rw [show (4 : ℤ) - 2 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_one_apply, octRootB_two]
        simp
      · rw [reflection_five_one_apply, octRootB_neg_two]
        simp
    · rw [show (4 : ℤ) - 3 = 1 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_five_one_apply, octRootB_three, octRootB_one]
        simp
      · rw [reflection_five_one_apply, octRootB_neg_three, octRootB_neg_one]
        simp

theorem un5Action₂' {m : SU (unitaryInvolution F p f) 5}
    (hm : ActsAs (rootDatum hF 5) m
      ((coxeterMatrix (rootDatum hF 5).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (un5Oct hF ((4 : ℕ) : ℤ)) = un5Oct hF (-((4 : ℕ) : ℤ)) ∧
      conjBy m (un5Oct hF (-((4 : ℕ) : ℤ))) = un5Oct hF ((4 : ℕ) : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ ((4 : ℕ) : ℤ) - 1 →
        conjBy m (un5Oct hF i) = un5Oct hF (((4 : ℕ) : ℤ) - i) ∧
          conjBy m (un5Oct hF (-i)) = un5Oct hF (-(((4 : ℕ) : ℤ) - i)) := by
  obtain ⟨h1, h2, h3⟩ := un5Action₂ hF hm
  refine ⟨by simpa using h1, by simpa using h2, fun i hi1 hi3 => ?_⟩
  simpa using h3 i hi1 (by omega)

end Weyl

end CFSG.Quasithin.H13.F431.Un
