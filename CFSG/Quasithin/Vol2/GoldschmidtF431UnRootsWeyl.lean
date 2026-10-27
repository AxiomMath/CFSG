module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Symplectic

section Weyl

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem conjBy_octGroup_simple_un {m : SU (unitaryInvolution F p f) 4} {k : Fin 2}
    (hm : ActsAs (rootDatum hF 4) m
      ((coxeterMatrix (rootDatum hF 4).isFiniteType).toCoxeterSystem.simple k)) {i : ℤ}
    (hi : IsRoot 4 i) :
    conjBy m (unOct hF i) =
      (rootDatum hF 4).rootGroup (reflection (cartanC 2) k (octRoot i)) :=
  map_conj_inv_simple (rootDatum hF 4) hm (octRoot_mem_roots' hi)

theorem unAction₁ {m : SU (unitaryInvolution F p f) 4}
    (hm : ActsAs (rootDatum hF 4) m
      ((coxeterMatrix (rootDatum hF 4).isFiniteType).toCoxeterSystem.simple (0 : Fin 2))) :
    conjBy m (unOct hF 1) = unOct hF (-1) ∧ conjBy m (unOct hF (-1)) = unOct hF 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 4 →
        conjBy m (unOct hF i) = unOct hF (((4 : ℕ) : ℤ) + 2 - i) ∧
          conjBy m (unOct hF (-i)) = unOct hF (-(((4 : ℕ) : ℤ) + 2 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (cartanC 2) 0 (octRoot i) = octRoot j →
      conjBy m (unOct hF i) = unOct hF j := fun hi hj =>
    (conjBy_octGroup_simple_un hF hm hi).trans (congrArg (rootDatum hF 4).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h2 h4 => ?_⟩
  · rw [reflection_zero_apply, octRoot_one, octRoot_neg_one]
    simp
  · rw [reflection_zero_apply, octRoot_neg_one, octRoot_one]
    simp
  · rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl
    · rw [show ((4 : ℕ) : ℤ) + 2 - 2 = 4 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_two, octRoot_four]
        simp
      · rw [reflection_zero_apply, octRoot_neg_two, octRoot_neg_four]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 3 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_three]
        simp
      · rw [reflection_zero_apply, octRoot_neg_three]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 4 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_four, octRoot_two]
        simp
      · rw [reflection_zero_apply, octRoot_neg_four, octRoot_neg_two]
        simp

theorem unAction₂ {m : SU (unitaryInvolution F p f) 4}
    (hm : ActsAs (rootDatum hF 4) m
      ((coxeterMatrix (rootDatum hF 4).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (unOct hF 4) = unOct hF (-4) ∧ conjBy m (unOct hF (-4)) = unOct hF 4 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy m (unOct hF i) = unOct hF (4 - i) ∧
        conjBy m (unOct hF (-i)) = unOct hF (-(4 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (cartanC 2) 1 (octRoot i) = octRoot j →
      conjBy m (unOct hF i) = unOct hF j := fun hi hj =>
    (conjBy_octGroup_simple_un hF hm hi).trans (congrArg (rootDatum hF 4).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h1 h3 => ?_⟩
  · rw [reflection_one_apply, octRoot_four, octRoot_neg_four]
    simp
  · rw [reflection_one_apply, octRoot_neg_four, octRoot_four]
    simp
  · rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [show (4 : ℤ) - 1 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_one, octRoot_three]
        simp
      · rw [reflection_one_apply, octRoot_neg_one, octRoot_neg_three]
        simp
    · rw [show (4 : ℤ) - 2 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_two]
        simp
      · rw [reflection_one_apply, octRoot_neg_two]
        simp
    · rw [show (4 : ℤ) - 3 = 1 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_three, octRoot_one]
        simp
      · rw [reflection_one_apply, octRoot_neg_three, octRoot_neg_one]
        simp

theorem unAction₂' {m : SU (unitaryInvolution F p f) 4}
    (hm : ActsAs (rootDatum hF 4) m
      ((coxeterMatrix (rootDatum hF 4).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (unOct hF ((4 : ℕ) : ℤ)) = unOct hF (-((4 : ℕ) : ℤ)) ∧
      conjBy m (unOct hF (-((4 : ℕ) : ℤ))) = unOct hF ((4 : ℕ) : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ ((4 : ℕ) : ℤ) - 1 →
        conjBy m (unOct hF i) = unOct hF (((4 : ℕ) : ℤ) - i) ∧
          conjBy m (unOct hF (-i)) = unOct hF (-(((4 : ℕ) : ℤ) - i)) := by
  obtain ⟨h1, h2, h3⟩ := unAction₂ hF hm
  refine ⟨by simpa using h1, by simpa using h2, fun i hi1 hi3 => ?_⟩
  simpa using h3 i hi1 (by omega)

end Weyl

end CFSG.Quasithin.H13.F431.Un
