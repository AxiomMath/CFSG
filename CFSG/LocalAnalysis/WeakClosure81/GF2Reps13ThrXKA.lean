module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped BigOperators

private theorem w16g_two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0 := by
  intro h
  have h' : ((2 : ℤ) : ZMod 3) = 0 := by rw [← h]; norm_num
  have hdvd : (3 : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 3).mp h'
  norm_num at hdvd

private theorem w16g_add_self_eq_zero {x : ZMod 3} (h : x + x = 0) : x = 0 := by
  have h2 : (2 : ZMod 3) * x = 0 := by rw [two_mul]; exact h
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (mul_eq_zero.mp h2).resolve_left w16g_two_ne_zero_zmod_three

private theorem w16g_sum_two {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ZMod 3)
    {i j : ι} (hij : i ≠ j) (h : ∀ k, k ≠ i → k ≠ j → g k = 0) :
    ∑ k, g k = g i + g j := by
  have h1 : (∑ k, g k) = ∑ k ∈ ({i, j} : Finset ι), g k :=
    (Finset.sum_subset (s₁ := ({i, j} : Finset ι)) (s₂ := Finset.univ)
      (Finset.subset_univ _) (by
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        push Not at hk
        exact h k hk.1 hk.2)).symm
  rw [h1, Finset.sum_pair hij]

theorem w16g_const_of_preserves {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (f c : ι → ZMod 3) (hf : ∀ i, f i ≠ 0)
    (h : ∀ y : ι → ZMod 3, (∑ i, f i * y i) = 0 → (∑ i, f (π i) * (c i * y i)) = 0) :
    ∀ i j, f (π i) * c i * (f i)⁻¹ = f (π j) * c j * (f j)⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have hy : (∑ k, f k * (if k = i then (f i)⁻¹ else if k = j then -((f j)⁻¹) else 0)) = 0 := by
      rw [w16g_sum_two (fun k => f k * (if k = i then (f i)⁻¹ else
        if k = j then -((f j)⁻¹) else 0)) hij]
      · rw [if_neg (Ne.symm hij)]
        simp
        rw [mul_inv_cancel₀ (hf i), mul_inv_cancel₀ (hf j)]
        ring
      · intro k hki hkj
        simp [hki, hkj]
    have hh := h _ hy
    have h2 : (∑ k, f (π k) * (c k * (if k = i then (f i)⁻¹ else
        if k = j then -((f j)⁻¹) else 0))) =
        f (π i) * (c i * (f i)⁻¹) - f (π j) * (c j * (f j)⁻¹) := by
      rw [w16g_sum_two (fun k => f (π k) * (c k * (if k = i then (f i)⁻¹ else
        if k = j then -((f j)⁻¹) else 0))) hij]
      · rw [if_neg (Ne.symm hij)]
        simp
        ring
      · intro k hki hkj
        simp [hki, hkj]
    rw [h2] at hh
    have h3 : f (π i) * (c i * (f i)⁻¹) = f (π j) * (c j * (f j)⁻¹) := sub_eq_zero.mp hh
    simpa only [mul_assoc] using h3

theorem w16g_eps_pair {ι : Type*} [DecidableEq ι] (π : Equiv.Perm ι) (hπ : ∀ i, π (π i) = i)
    (m : ι → ZMod 3) (u u' : ι) (hu : u ≠ u') (hmu : m u ≠ 0) (hmu' : m u' ≠ 0)
    (hsum : m u + m u' = 0) (hzero : ∀ v, v ≠ u → v ≠ u' → m v = 0)
    (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) (hq : ∀ v, ε * m v = - m (π v)) :
    (ε = 1 → π u = u' ∧ π u' = u) ∧ (ε = -1 → π u = u ∧ π u' = u') := by
  have key : ∀ v : ι, m v ≠ 0 → v = u ∨ v = u' := by
    intro v hv
    by_contra hc
    push Not at hc
    exact hv (hzero v hc.1 hc.2)
  have hne : m u ≠ m u' := by
    intro heq
    have h1 : m u + m u = 0 := by
      rw [← heq] at hsum
      exact hsum
    exact hmu (w16g_add_self_eq_zero h1)
  constructor
  · intro he1
    have hqv : ∀ v, m v = - m (π v) := by
      intro v
      have hv := hq v
      rw [he1, one_mul] at hv
      exact hv
    constructor
    · have hm : m (π u) ≠ 0 := by intro h0; exact hmu (by rw [hqv u, h0, neg_zero])
      rcases key (π u) hm with h | h
      · exfalso
        have h1 : m u + m u = 0 := by
          have hh := hqv u
          rw [h] at hh
          exact (eq_neg_iff_add_eq_zero).mp hh
        exact hmu (w16g_add_self_eq_zero h1)
      · exact h
    · have hm : m (π u') ≠ 0 := by intro h0; exact hmu' (by rw [hqv u', h0, neg_zero])
      rcases key (π u') hm with h | h
      · exact h
      · exfalso
        have h1 : m u' + m u' = 0 := by
          have hh := hqv u'
          rw [h] at hh
          exact (eq_neg_iff_add_eq_zero).mp hh
        exact hmu' (w16g_add_self_eq_zero h1)
  · intro he1
    have hqv : ∀ v, m v = m (π v) := by
      intro v
      have hv := hq v
      rw [he1, neg_mul, one_mul, neg_inj] at hv
      exact hv
    constructor
    · have hm : m (π u) ≠ 0 := by intro h0; exact hmu (by rw [hqv u, h0])
      rcases key (π u) hm with h | h
      · exact h
      · exfalso
        have heq : m u = m u' := by rw [← h]; exact hqv u
        exact hne heq
    · have hm : m (π u') ≠ 0 := by intro h0; exact hmu' (by rw [hqv u', h0])
      rcases key (π u') hm with h | h
      · exfalso
        have heq : m u' = m u := by rw [← h]; exact hqv u'
        exact hne heq.symm
      · exact h

end CFSG.LocalAnalysis.WeakClosure81
