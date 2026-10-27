module

public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin

@[expose] def omqEpsLabels (n m : ℕ) (ν : Fin n → ZMod m) : Fin n → ZMod m := fun k =>
  ∑ b, ν b * ((toStdD n (Pi.single k 1) b : ℤ) : ZMod m)

private lemma c2slomqep_sum_single (n m : ℕ) (ν : Fin n → ZMod m) (k : Fin n) :
    ∑ b, ν b * (((Pi.single k (1 : ℤ) : Fin n → ℤ) b : ℤ) : ZMod m) = ν k := by
  rw [Fintype.sum_eq_single k (fun b hbk => by simp [Pi.single_eq_of_ne hbk])]
  simp

private lemma c2slomqep_apply_of_lt (n m : ℕ) (ν : Fin n → ZMod m) {k : Fin n}
    (h : k.val + 1 < n) :
    omqEpsLabels n m ν k = ν k - ν ⟨k.val + 1, h⟩ := by
  simp only [omqEpsLabels, toStdD_single_of_lt n h, Pi.sub_apply, Int.cast_sub, mul_sub,
    Finset.sum_sub_distrib, c2slomqep_sum_single]

private lemma c2slomqep_apply_of_not_lt (n m : ℕ) (ν : Fin n → ZMod m) {k : Fin n}
    (h : ¬ k.val + 1 < n) (hn2 : 2 ≤ n) {p : n - 2 < n} :
    omqEpsLabels n m ν k = ν ⟨n - 2, p⟩ + ν k := by
  have key := toStdD_single_of_not_lt n h hn2
  simp only [omqEpsLabels, key, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib,
    c2slomqep_sum_single]

private lemma c2slomqep_map_sub (n m : ℕ) (ν μ : Fin n → ZMod m) :
    omqEpsLabels n m (ν - μ) = omqEpsLabels n m ν - omqEpsLabels n m μ := by
  funext k
  simp only [omqEpsLabels, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma c2slomqep_eq_zero_of_labels_zero {n : ℕ} (hn : 3 ≤ n) {m : ℕ} (hm : Odd m)
    {ν : Fin n → ZMod m} (h : omqEpsLabels n m ν = 0) : ν = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hn2 : 2 ≤ n := by omega
  have step : ∀ (k : Fin n) (hk : k.val + 1 < n), ν k = ν ⟨k.val + 1, hk⟩ := by
    intro k hk
    have hk0 : omqEpsLabels n m ν k = 0 := by simpa using congrFun h k
    rw [c2slomqep_apply_of_lt n m ν hk] at hk0
    exact sub_eq_zero.mp hk0
  have chain : ∀ d : ℕ, ∀ a : Fin n, a.val = d → ν a = ν 0 := by
    intro d
    induction d with
    | zero =>
      intro a ha
      have : a = 0 := Fin.ext (by simpa using ha)
      rw [this]
    | succ d ih =>
      intro a ha
      have hlt : a.val - 1 < n := by omega
      have hk : (⟨a.val - 1, hlt⟩ : Fin n).val + 1 < n := by simp only; omega
      have hs : ν ⟨a.val - 1, hlt⟩ = ν a := by
        have h1 := step ⟨a.val - 1, hlt⟩ hk
        have he : (⟨(⟨a.val - 1, hlt⟩ : Fin n).val + 1, hk⟩ : Fin n) = a :=
          Fin.ext (by simp only; omega)
        rwa [he] at h1
      exact hs.symm.trans (ih ⟨a.val - 1, hlt⟩ (by simp only; omega))
  have p2 : n - 2 < n := by omega
  have q2 : n - 1 < n := by omega
  have hlast : ν ⟨n - 2, p2⟩ + ν ⟨n - 1, q2⟩ = 0 := by
    have hk : omqEpsLabels n m ν ⟨n - 1, q2⟩ = 0 := by simpa using congrFun h ⟨n - 1, q2⟩
    rw [c2slomqep_apply_of_not_lt n m ν (k := ⟨n - 1, q2⟩) (by simp only; omega) hn2
      (p := p2)] at hk
    exact hk
  have hchain2 : ν 0 = ν ⟨n - 2, p2⟩ := (chain (n - 2) ⟨n - 2, p2⟩ rfl).symm
  have hchain1 : ν 0 = ν ⟨n - 1, q2⟩ := (chain (n - 1) ⟨n - 1, q2⟩ rfl).symm
  have h2 : ν 0 + ν 0 = 0 := by
    nth_rewrite 1 [hchain2]
    nth_rewrite 1 [hchain1]
    exact hlast
  have h0 : ν 0 = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hm).mp h2
  funext a
  rw [chain a.val a rfl, h0, Pi.zero_apply]

theorem omq_labels_bijective {n : ℕ} (hn : 3 ≤ n) {m : ℕ} (hm : Odd m) :
    Function.Bijective (omqEpsLabels n m) := by
  have hm0 : m ≠ 0 := by
    obtain ⟨t, ht⟩ := hm
    omega
  haveI : NeZero m := ⟨hm0⟩
  refine Finite.injective_iff_bijective.mp ?_
  intro ν μ h
  have hzero : omqEpsLabels n m (ν - μ) = 0 := by
    rw [c2slomqep_map_sub, h, sub_self]
  exact sub_eq_zero.mp (c2slomqep_eq_zero_of_labels_zero hn hm hzero)

end CFSG.LocalAnalysis.WeakClosure81
