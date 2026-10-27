module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG

private lemma l04fRE_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact hp2 (by omega)

private lemma l04fRE_A_diag {m : ℕ} (i : Fin m) : CartanMatrix.A m i i = 2 := by
  simp [CartanMatrix.A]

private lemma l04fRE_A_adj {m : ℕ} {i j : Fin m}
    (h : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) : CartanMatrix.A m i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg (by intro hji; have hval : (i : ℕ) = (j : ℕ) := congrArg Fin.val hji; omega),
    if_pos h]

private lemma l04fRE_A_far {m : ℕ} {i j : Fin m}
    (h : (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ)) : CartanMatrix.A m i j = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg (by intro hji; have hval : (i : ℕ) = (j : ℕ) := congrArg Fin.val hji; omega),
    if_neg (by rintro (h1 | h1) <;> omega)]

private lemma l04fRE_pair_diag {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p)) (i : Fin m) :
    a i (u i) = 2 := by
  rw [hpair i i, l04fRE_A_diag i]
  norm_num

private lemma l04fRE_pair_adj {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p)) {i j : Fin m}
    (h : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) : a i (u j) = -1 := by
  rw [hpair i j, l04fRE_A_adj h]
  norm_num

private lemma l04fRE_pair_far {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p)) {i j : Fin m}
    (h : (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ)) : a i (u j) = 0 := by
  rw [hpair i j, l04fRE_A_far h]
  norm_num

private lemma l04fRE_q_sq {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) (i : Fin m) :
    q i * q i = 1 := by
  ext w
  rw [LinearEquiv.mul_apply]
  change q i (q i w) = w
  rw [hq i (q i w), hq i w]
  simp only [map_sub, map_smul, l04fRE_pair_diag hpair i]
  module

private lemma l04fRE_braid {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) {i j : Fin m}
    (hij : (i : ℕ) + 1 = (j : ℕ)) : q i * q j * q i = q j * q i * q j := by
  have haij : a i (u j) = -1 := l04fRE_pair_adj hpair (Or.inl hij)
  have haji : a j (u i) = -1 := l04fRE_pair_adj hpair (Or.inr hij)
  ext w
  simp only [LinearEquiv.mul_apply, hq, map_sub, map_smul, l04fRE_pair_diag hpair i,
    l04fRE_pair_diag hpair j, haij, haji]
  module

private lemma l04fRE_adj_ne {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 3 ≤ m) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) {i j : Fin m}
    (hij : (i : ℕ) + 1 = (j : ℕ)) (heq : q i = q j) : False := by
  have h2ne : (2 : ZMod p) ≠ 0 := l04fRE_two_ne_zero hp2
  by_cases hlt : (i : ℕ) + 2 < m
  · let k : Fin m := ⟨(i : ℕ) + 2, by omega⟩
    have hk : (k : ℕ) = (i : ℕ) + 2 := rfl
    have hik : a i (u k) = 0 := l04fRE_pair_far hpair (Or.inl (by omega))
    have hjk : a j (u k) = -1 := l04fRE_pair_adj hpair (Or.inl (by omega))
    have hval := congrArg (fun f : W ≃ₗ[ZMod p] W => f (u k)) heq
    rw [hq i (u k), hq j (u k), hik, hjk] at hval
    simp only [zero_smul, sub_zero, neg_one_smul, sub_neg_eq_add] at hval
    have huj : u j = 0 := by
      have h' : u k + u j = u k + 0 := by rw [add_zero]; exact hval.symm
      exact add_left_cancel h'
    have hcontra : a j (u j) = 0 := by rw [huj, map_zero]
    rw [l04fRE_pair_diag hpair j] at hcontra
    exact h2ne hcontra
  · have hi1 : 1 ≤ (i : ℕ) := by omega
    let k : Fin m := ⟨(i : ℕ) - 1, by omega⟩
    have hk : (k : ℕ) = (i : ℕ) - 1 := rfl
    have hik : a i (u k) = -1 := l04fRE_pair_adj hpair (Or.inr (by omega))
    have hjk : a j (u k) = 0 := l04fRE_pair_far hpair (Or.inr (by omega))
    have hval := congrArg (fun f : W ≃ₗ[ZMod p] W => f (u k)) heq
    rw [hq i (u k), hq j (u k), hik, hjk] at hval
    simp only [zero_smul, sub_zero, neg_one_smul, sub_neg_eq_add] at hval
    have hui : u i = 0 := by
      have h' : u k + u i = u k + 0 := by rw [add_zero]; exact hval
      exact add_left_cancel h'
    have hcontra : a i (u i) = 0 := by rw [hui, map_zero]
    rw [l04fRE_pair_diag hpair i] at hcontra
    exact h2ne hcontra

private lemma l04fRE_mul_ne_one {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 3 ≤ m) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) {i j : Fin m}
    (hij : (i : ℕ) + 1 = (j : ℕ)) : q i * q j ≠ 1 := by
  intro h
  have hi := l04fRE_q_sq hpair hq i
  have hqij : q i = q j := by
    calc q i = q i * 1 := (mul_one _).symm
      _ = q i * (q i * q j) := by rw [← h]
      _ = (q i * q i) * q j := (mul_assoc _ _ _).symm
      _ = 1 * q j := by rw [hi]
      _ = q j := one_mul _
  exact l04fRE_adj_ne hp2 hm hpair hq hij hqij

private lemma l04fRE_far_comm {p m : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) {i j : Fin m}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) : q i * q j = q j * q i := by
  have haij : a i (u j) = 0 := l04fRE_pair_far hpair (Or.inl hij)
  have haji : a j (u i) = 0 := l04fRE_pair_far hpair (Or.inr (by omega))
  ext w
  simp only [LinearEquiv.mul_apply, hq, map_sub, map_smul, haij, haji]
  module

private lemma l04fRE_far_ne {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) {i j : Fin m}
    (hij : (i : ℕ) + 2 ≤ (j : ℕ)) : q i ≠ q j := by
  intro heq
  have haij : a i (u j) = 0 := l04fRE_pair_far hpair (Or.inl hij)
  have hval := congrArg (fun f : W ≃ₗ[ZMod p] W => f (u j)) heq
  rw [hq i (u j), hq j (u j), haij, l04fRE_pair_diag hpair j] at hval
  simp only [zero_smul, sub_zero] at hval
  have h2 : (2 : ZMod p) • u j = 0 := sub_eq_self.mp hval.symm
  have h4 : (4 : ZMod p) = 0 := by
    have h := congrArg (a j) h2
    rw [map_smul, map_zero] at h
    rw [l04fRE_pair_diag hpair j] at h
    have h' : (2 : ZMod p) * 2 = 0 := by simpa using h
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact h'
  have hp_dvd2 : p ∣ 2 :=
    (Fact.out : p.Prime).dvd_of_dvd_pow (m := 2) (n := 2)
      (by simpa [pow_two] using (ZMod.natCast_eq_zero_iff 4 p).mp h4)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd2)

theorem ggLargeDep_noSym_aug_rel {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 3 ≤ m) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i) :
    (∀ i j : Fin m, (i : ℕ) + 1 = (j : ℕ) → orderOf (q i * q j) = 3) ∧
      ∀ i j : Fin m, (i : ℕ) + 2 ≤ (j : ℕ) → q i * q j = q j * q i ∧ q i ≠ q j := by
  constructor
  · intro i j hij
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ (l04fRE_mul_ne_one hp2 hm hpair hq hij)
    have hbb : q i * q j * q i = q j * q i * q j := l04fRE_braid hpair hq hij
    have hi := l04fRE_q_sq hpair hq i
    have hj := l04fRE_q_sq hpair hq j
    calc (q i * q j) ^ 3
        = (q i * q j * q i) * (q j * q i * q j) := by rw [pow_three]; group
      _ = (q j * q i * q j) * (q j * q i * q j) := by rw [hbb]
      _ = (q j * q i) * (q j * q j) * (q i * q j) := by group
      _ = (q j * q i) * 1 * (q i * q j) := by rw [hj]
      _ = (q j * (q i * q i)) * q j := by group
      _ = (q j * 1) * q j := by rw [hi]
      _ = 1 := by rw [mul_one, hj]
  · intro i j hij
    exact ⟨l04fRE_far_comm hpair hq hij, l04fRE_far_ne hp2 hpair hq hij⟩

end CFSG.StandardType

end
