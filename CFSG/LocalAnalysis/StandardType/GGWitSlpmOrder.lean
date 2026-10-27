module

public import CFSG.LocalAnalysis.StandardType.GGWitSlpm
import Mathlib.Tactic

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem slpm_order {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (a b : U) (α β : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) (hβ : β b = 2) (hαb : α b = 0)
    (hβa : β a = 1) :
    orderOf (slpmRefl a α hα * slpmRefl b β hβ) = 2 * p := by
  have happ : ∀ (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2) (v : U),
      slpmRefl a α hα v = v - α v • a := by
    intro a α hα v
    change ((LinearMap.id : U →ₗ[ZMod p] U) - α.smulRight a) v = v - α v • a
    simp [LinearMap.sub_apply, LinearMap.smulRight_apply]
  have hr : ∀ v, slpmRefl a α hα v = v - α v • a := fun v => happ a α hα v
  have hs : ∀ v, slpmRefl b β hβ v = v - β v • b := fun v => happ b β hβ v
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (Nat.Prime.ne_one (Fact.out))
    · exact hp2 h1
  have ha_ne : a ≠ 0 := by
    intro h
    have h' := hα
    rw [h, map_zero] at h'
    exact h2 h'.symm
  let ρ : U ≃ₗ[ZMod p] U := slpmRefl a α hα * slpmRefl b β hβ
  have hρ : ∀ v, ρ v = v - α v • a - β v • b := by
    intro v
    have hαs : α ((slpmRefl b β hβ) v) = α v := by
      rw [hs v, map_sub α v (β v • b), map_smul α (β v) b, hαb, smul_zero]
      abel
    calc ρ v = (slpmRefl a α hα) ((slpmRefl b β hβ) v) := by
            rw [show ρ = slpmRefl a α hα * slpmRefl b β hβ from rfl, LinearEquiv.mul_apply]
      _ = (slpmRefl b β hβ) v - α ((slpmRefl b β hβ) v) • a := hr _
      _ = (v - β v • b) - α v • a := by rw [hαs, hs v]
      _ = v - α v • a - β v • b := by abel
  have hρa : ρ a = -a - b := by
    rw [hρ a, hα, hβa, two_smul (ZMod p) a, one_smul]
    abel
  have hρb : ρ b = -b := by
    rw [hρ b, hαb, hβ, zero_smul, two_smul (ZMod p) b]
    abel
  have hρ2 : ∀ v, ρ (ρ v) = v + α v • b := by
    intro v
    calc ρ (ρ v) = ρ (v - α v • a - β v • b) := by rw [hρ v]
      _ = ρ v - (α v) • ρ a - (β v) • ρ b := by
            rw [map_sub ρ (v - α v • a) (β v • b), map_sub ρ v (α v • a),
              map_smul ρ (α v) a, map_smul ρ (β v) b]
      _ = (v - α v • a - β v • b) - (α v) • (-a - b) - (β v) • (-b) := by
            rw [hρa, hρb, hρ v]
      _ = v + α v • b := by
            simp only [smul_neg, smul_add, sub_eq_add_neg]
            abel
  have hpow2 : ∀ k : ℕ, ∀ v : U, ((ρ ^ 2) ^ k) v = v + k • (α v • b) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        have hαk : α (v + k • (α v • b)) = α v := by
          rw [map_add α v (k • (α v • b)), map_nsmul α k (α v • b),
            map_smul α (α v) b, hαb, smul_zero, smul_zero, add_zero]
        calc ((ρ ^ 2) ^ (k + 1)) v
            = (ρ ^ 2) (((ρ ^ 2) ^ k) v) := by
              rw [pow_succ', LinearEquiv.mul_apply]
          _ = (ρ ^ 2) (v + k • (α v • b)) := by rw [ih]
          _ = ρ (ρ (v + k • (α v • b))) := by rw [pow_two, LinearEquiv.mul_apply]
          _ = (v + k • (α v • b)) + α (v + k • (α v • b)) • b := hρ2 _
          _ = (v + k • (α v • b)) + α v • b := by rw [hαk]
          _ = v + (k + 1) • (α v • b) := by rw [succ_nsmul (α v • b) k]; abel
  have hnat : ∀ x : U, p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self p, zero_smul]
  have hpow_2p : ρ ^ (2 * p) = 1 := by
    rw [pow_mul]
    ext v
    rw [hpow2 p v, hnat, add_zero]
    rfl
  have hρ_ab : ∀ k : ℕ, ρ (a + k • b) = -(a + (k + 1) • b) := by
    intro k
    rw [map_add ρ a (k • b), map_nsmul ρ k b, hρa, hρb, smul_neg, succ_nsmul b k]
    abel
  have hcoef : ∀ k : ℕ, (-1 : ZMod p) ^ (k + 1) = - ((-1 : ZMod p) ^ k) := by
    intro k
    rw [pow_succ]
    exact mul_neg_one ((-1 : ZMod p) ^ k)
  have hpow_b : ∀ k : ℕ, (ρ ^ k) b = (-1 : ZMod p) ^ k • b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul ρ ((-1 : ZMod p) ^ k) b, hρb,
          smul_neg, ← neg_smul, hcoef k]
        rfl
  have hpow_a : ∀ k : ℕ, (ρ ^ k) a = (-1 : ZMod p) ^ k • (a + k • b) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul ρ ((-1 : ZMod p) ^ k) (a + k • b),
          hρ_ab, smul_neg, ← neg_smul, hcoef k]
        rfl
  have hneg1 : (-1 : ZMod p) ^ p = -1 :=
    Odd.neg_one_pow (Nat.Prime.odd_of_ne_two (Fact.out) hp2)
  have hpa : (ρ ^ p) a = -a := by
    rw [hpow_a p, hneg1, hnat, add_zero]
    exact neg_one_smul (ZMod p) a
  have hpne : ρ ^ p ≠ 1 := by
    intro h
    have h1 : -a = a := by
      have h' := congrArg (fun (f : U ≃ₗ[ZMod p] U) => f a) h
      rw [hpa] at h'
      simpa using h'
    have h2a : (2 : ZMod p) • a = 0 := by
      rw [two_smul (ZMod p) a]
      nth_rewrite 2 [← h1]
      exact add_neg_cancel a
    exact ha_ne ((smul_eq_zero.mp h2a).resolve_left h2)
  have h2ne : ρ ^ 2 ≠ 1 := by
    intro h
    have h1 : a + (2 : ZMod p) • b = a := by
      have h' := congrArg (fun (f : U ≃ₗ[ZMod p] U) => f a) h
      have hρ2a : (ρ ^ 2) a = a + (2 : ZMod p) • b := by
        rw [pow_two, LinearEquiv.mul_apply, hρ2 a, hα]
      rw [hρ2a] at h'
      simpa using h'
    have hb0 : (2 : ZMod p) • b = 0 :=
      add_left_cancel (show a + (2 : ZMod p) • b = a + 0 by simpa using h1)
    have hb_ne : b ≠ 0 := by
      intro hb
      have hβ' := hβ
      rw [hb, map_zero] at hβ'
      exact h2 hβ'.symm
    exact hb_ne ((smul_eq_zero.mp hb0).resolve_left h2)
  have hd : ∀ q : ℕ, Nat.Prime q → q ∣ 2 * p → ρ ^ (2 * p / q) ≠ 1 := by
    intro q hq hqdiv
    have hqcase : q = 2 ∨ q = p := by
      rcases (Nat.Prime.dvd_mul hq).mp hqdiv with h | h
      · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
        · exact absurd h1 hq.ne_one
        · exact Or.inl h1
      · rcases (Nat.dvd_prime (Fact.out)).mp h with h1 | h1
        · exact absurd h1 hq.ne_one
        · exact Or.inr h1
    rcases hqcase with rfl | rfl
    · rw [Nat.mul_div_cancel_left p (by norm_num : 0 < 2)]
      exact hpne
    · rw [Nat.mul_div_cancel 2 (Nat.Prime.pos (Fact.out))]
      exact h2ne
  show orderOf ρ = 2 * p
  exact orderOf_eq_of_pow_and_pow_div_prime (n := 2 * p)
    (Nat.mul_pos (by norm_num) (Nat.Prime.pos (Fact.out))) hpow_2p hd

end CFSG.StandardType.ZS

end
