module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem commSec_elem {G : Type} [Group G] [Finite G] {N Q : Subgroup G} {x : G}
    (hNab : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Q) (hQN : Q ≤ N)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) :
    ∀ y ∈ CommSec N Q x, ∃ n ∈ N, ∃ q ∈ Q, y = ⁅n, x⁆ * q := by
  have K1 : ∀ a b : G,
      ⁅a, x⁆ * ⁅b, x⁆ = ⁅a * b, x⁆ * ⁅x * a * x⁻¹, x * b * x⁻¹ * b⁻¹⁆ := by
    intro a b
    simp only [commutatorElement_def]
    group
  have hinvc : ∀ m : G, ⁅m, x⁆⁻¹ = ⁅m, ⁅m⁻¹, x⁆⁆ * ⁅m⁻¹, x⁆ := by
    intro m
    simp only [commutatorElement_def]
    group
  have idA : ∀ w m z : G, ⁅m, w * z⁆ = ⁅m, w⁆ * (w * ⁅m, z⁆ * w⁻¹) := by
    intro w m z
    simp only [commutatorElement_def]
    group
  have idB : ∀ w m z : G, w * ⁅m, z⁆ * w⁻¹ = ⁅w * m * w⁻¹, w * z * w⁻¹⁆ := by
    intro w m z
    simp only [commutatorElement_def]
    group
  have idC : ∀ w m z : G, z * w * m * (z * w)⁻¹ = z * (w * m * w⁻¹) * z⁻¹ := by
    intro w m z
    group
  have hcomm : ∀ n ∈ N, ⁅n, x⁆ ∈ N := by
    intro n hn
    have e : ⁅n, x⁆ = n * (x * n⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hn (hxN _ (N.inv_mem hn))
  have hpow : ∀ k : ℕ, ∀ n ∈ N, x ^ k * n * (x ^ k)⁻¹ ∈ N := by
    intro k
    induction k with
    | zero =>
      intro n hn
      simpa using hn
    | succ k ih =>
      intro n hn
      rw [pow_succ', idC]
      exact hxN _ (ih n hn)
  have hcpow : ∀ k : ℕ, x ^ k * x * (x ^ k)⁻¹ = x := by
    intro k
    have hc : x ^ k * x = x * x ^ k := (pow_succ x k).symm.trans (pow_succ' x k)
    rw [hc, mul_inv_cancel_right]
  have hone : ∃ n ∈ N, ∃ q ∈ Q, (1 : G) = ⁅n, x⁆ * q :=
    ⟨1, N.one_mem, 1, Q.one_mem, by simp [commutatorElement_def]⟩
  have hmul : ∀ a b : G, (∃ n ∈ N, ∃ q ∈ Q, a = ⁅n, x⁆ * q) →
      (∃ n ∈ N, ∃ q ∈ Q, b = ⁅n, x⁆ * q) → ∃ n ∈ N, ∃ q ∈ Q, a * b = ⁅n, x⁆ * q := by
    rintro a b ⟨n, hn, q, hq, rfl⟩ ⟨n', hn', q', hq', rfl⟩
    have hc : ⁅x * n * x⁻¹, x * n' * x⁻¹ * n'⁻¹⁆ ∈ Q :=
      hNab _ (hxN n hn) _ (N.mul_mem (hxN n' hn') (N.inv_mem hn'))
    have hg : (⁅n', x⁆)⁻¹ * q * ⁅n', x⁆ ∈ Q := by
      have h := hNQ _ (N.inv_mem (hcomm n' hn')) q hq
      rwa [inv_inv] at h
    refine ⟨n * n', N.mul_mem hn hn',
      ⁅x * n * x⁻¹, x * n' * x⁻¹ * n'⁻¹⁆ * ((⁅n', x⁆)⁻¹ * q * ⁅n', x⁆) * q',
      Q.mul_mem (Q.mul_mem hc hg) hq', ?_⟩
    have key : ⁅n, x⁆ * q * (⁅n', x⁆ * q') =
        ⁅n, x⁆ * ⁅n', x⁆ * ((⁅n', x⁆)⁻¹ * q * ⁅n', x⁆) * q' := by
      group
    rw [key, K1 n n']
    simp only [mul_assoc]
  have hinv : ∀ a : G, (∃ n ∈ N, ∃ q ∈ Q, a = ⁅n, x⁆ * q) →
      ∃ n ∈ N, ∃ q ∈ Q, a⁻¹ = ⁅n, x⁆ * q := by
    rintro a ⟨n, hn, q, hq, rfl⟩
    have hv : ⁅n⁻¹, x⁆ ∈ N := hcomm _ (N.inv_mem hn)
    have hqq : q⁻¹ * ⁅n, ⁅n⁻¹, x⁆⁆ ∈ Q := Q.mul_mem (Q.inv_mem hq) (hNab _ hn _ hv)
    have hw : ⁅n⁻¹, x⁆⁻¹ * (q⁻¹ * ⁅n, ⁅n⁻¹, x⁆⁆) * ⁅n⁻¹, x⁆ ∈ Q := by
      have h := hNQ _ (N.inv_mem hv) _ hqq
      rwa [inv_inv] at h
    refine ⟨n⁻¹, N.inv_mem hn, _, hw, ?_⟩
    rw [mul_inv_rev, hinvc n]
    group
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, ∀ y : G, y ∈ Y ↔ ∃ n ∈ N, ∃ q ∈ Q, y = ⁅n, x⁆ * q :=
    ⟨{ carrier := {y : G | ∃ n ∈ N, ∃ q ∈ Q, y = ⁅n, x⁆ * q}
       mul_mem' := fun {a b} ha hb => hmul a b ha hb
       one_mem' := hone
       inv_mem' := fun {a} ha => hinv a ha }, fun _ => Iff.rfl⟩
  have hQY : Q ≤ Y := by
    intro q hq
    exact (hY q).mpr ⟨1, N.one_mem, q, hq, by simp [commutatorElement_def]⟩
  have hcY : ∀ n ∈ N, ⁅n, x⁆ ∈ Y := fun n hn =>
    (hY _).mpr ⟨n, hn, 1, Q.one_mem, (mul_one _).symm⟩
  have hpowY : ∀ k : ℕ, ∀ n ∈ N, ⁅n, x ^ k⁆ ∈ Y := by
    intro k
    induction k with
    | zero =>
      intro n _
      have h1 : ⁅n, x ^ 0⁆ = 1 := by simp [commutatorElement_def]
      rw [h1]
      exact Y.one_mem
    | succ k ih =>
      intro n hn
      rw [pow_succ, idA, idB, hcpow k]
      exact Y.mul_mem (ih n hn) (hcY _ (hpow k n hn))
  have hcommY : ⁅N, Subgroup.zpowers x⁆ ≤ Y := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg₂)
    exact hpowY k g₁ hg₁
  have hsub : CommSec N Q x ≤ Y := sup_le hcommY hQY
  intro y hy
  exact (hY y).mp (hsub hy)

end CFSG.RankThree.GF2n.Stroth80
