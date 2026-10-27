module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusOrbitEps
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFormal
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusSimpleFix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_four_le_rank_of_long_node {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k]
    [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s) {j : Fin (n - 1)} (hj1 : 1 ≤ j.val)
    (hj2 : j.val + 2 ≤ n - 1)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ j) :
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  obtain ⟨u, hinj, horb, hmove⟩ :=
    omq_minus_exists_four_flag (by omega : 3 ≤ n - 1) hj1 hj2 hs hsh
  refine omq_omMinus_rank_of_eps_orbit hn hirr hσ ht hxr ?_ hinj horb hmove
  intro t htne
  have htj : t.val ≠ j.val := fun h => htne (by rw [Fin.ext h]; exact hsep)
  exact omq_minus_simpleFix_flag hj2 htj

theorem omq_omMinus_four_le_rank_of_short_node {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type}
    [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s)
    (hsep : μ ⟨n - 2, by omega⟩ =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨n - 2, by omega⟩)
    (hc : 5 ≤ n ∨ π = 1) :
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  obtain ⟨u, hinj, horb, hmove⟩ :=
    omq_minus_exists_four_cube (by omega : 3 ≤ n - 1) hs hsh
      (by rcases hc with h | h
          · exact Or.inl (by omega)
          · exact Or.inr h)
  refine omq_omMinus_rank_of_eps_orbit hn hirr hσ ht hxr ?_ hinj horb hmove
  intro t htne
  have htl : t.val + 1 < n - 1 := by
    have h1 : t.val ≠ n - 2 := fun h => htne (by
      have : t = ⟨n - 2, by omega⟩ := Fin.ext h
      rw [this]; exact hsep)
    have := t.isLt
    omega
  exact omq_minus_simpleFix_cube htl

theorem omq_omMinus_four_le_rank_of_two_one_one {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type}
    [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s)
    (hA : (∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      π ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (h0 : μ ⟨0, by omega⟩ = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨0, by omega⟩)
    (h2 : μ ⟨n - 2, by omega⟩ =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨n - 2, by omega⟩) :
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  obtain ⟨u, hinj, horb, hmove⟩ := omq_minus_exists_four_two_one_one (by omega : 3 ≤ n - 1) hA
  refine omq_omMinus_rank_of_eps_orbit hn hirr hσ ht hxr ?_ hinj horb hmove
  intro t htne
  have ht1 : 1 ≤ t.val := by
    by_contra h
    have : t = ⟨0, by omega⟩ := Fin.ext (show t.val = 0 by omega)
    exact htne (by rw [this]; exact h0)
  have htl : t.val + 1 < n - 1 := by
    have h1 : t.val ≠ n - 2 := fun h => htne (by
      have : t = ⟨n - 2, by omega⟩ := Fin.ext h
      rw [this]; exact h2)
    have := t.isLt
    omega
  exact omq_minus_simpleFix_two_one_one ht1 htl

theorem omq_omMinus_two_le_rank_of_short_node {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type}
    [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s)
    (hsep : μ ⟨n - 2, by omega⟩ =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨n - 2, by omega⟩) :
    2 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  obtain ⟨u, hinj, horb, hmove⟩ := omq_minus_exists_two_cube (by omega : 3 ≤ n - 1) hs hsh
  refine omq_omMinus_rank_of_eps_orbit hn hirr hσ ht hxr ?_ hinj horb hmove
  intro t htne
  have htl : t.val + 1 < n - 1 := by
    have h1 : t.val ≠ n - 2 := fun h => htne (by
      have : t = ⟨n - 2, by omega⟩ := Fin.ext h
      rw [this]; exact hsep)
    have := t.isLt
    omega
  exact omq_minus_simpleFix_cube htl

end CFSG.LocalAnalysis.WeakClosure81
