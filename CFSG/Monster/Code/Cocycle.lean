module

public import CFSG.Monster.Code.Loop
import Mathlib.Tactic.LinearCombination
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.Monster.Code

open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

theorem supp_inter (d e : Fin 24 → ZMod 2) : supp d ∩ supp e = supp (d * e) := by
  ext i
  simp only [supp, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply]
  exact (mul_ne_zero_iff).symm

theorem card_supp (d : Fin 24 → ZMod 2) : (supp d).card = hammingNorm d := rfl

theorem A_eq_sum (d e f : Fin 24 → ZMod 2) : A d e f = ∑ i, d i * e i * f i := by
  rw [A, supp_inter, supp_inter, card_supp, ← sum_eq_hammingNorm]
  rfl

theorem K_eq (d e : Fin 24 → ZMod 2) : K d e = ((hammingNorm (d * e) / 2 : ℕ) : ZMod 2) := by
  rw [K, supp_inter, card_supp]

theorem K_comm (d e : Fin 24 → ZMod 2) : K d e = K e d := by
  rw [K, K, Finset.inter_comm]

theorem A_comm₁₂ (d e f : Fin 24 → ZMod 2) : A d e f = A e d f := by
  simp only [A_eq_sum, mul_comm (d _)]

theorem A_comm₂₃ (d e f : Fin 24 → ZMod 2) : A d e f = A d f e := by
  simp only [A_eq_sum, mul_assoc, mul_comm (e _)]

theorem A_add_right (d e f f' : Fin 24 → ZMod 2) : A d e (f + f') = A d e f + A d e f' := by
  simp only [A_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem A_sum_left {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (y z : Fin 24 → ZMod 2) : A (∑ i, c i • b i) y z = ∑ i, c i * A (b i) y z := by
  simp only [A_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem A_sum_mid {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (x z : Fin 24 → ZMod 2) : A x (∑ i, c i • b i) z = ∑ i, c i * A x (b i) z := by
  rw [A_comm₁₂, A_sum_left]
  exact Finset.sum_congr rfl fun i _ => by rw [A_comm₁₂]

theorem A_sum_right {ι : Type*} [Fintype ι] (c : ι → ZMod 2) (b : ι → Fin 24 → ZMod 2)
    (x y : Fin 24 → ZMod 2) : A x y (∑ i, c i • b i) = ∑ i, c i * A x y (b i) := by
  rw [A_comm₂₃, A_sum_mid]
  exact Finset.sum_congr rfl fun i _ => by rw [A_comm₂₃]

private theorem val_add_add : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by
  decide

theorem hammingNorm_add_add (x y : Fin 24 → ZMod 2) :
    hammingNorm (x + y) + 2 * hammingNorm (x * y) = hammingNorm x + hammingNorm y := by
  simp only [hammingNorm_eq_sum_val, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.mul_apply, val_add_add]

theorem two_dvd_hammingNorm_mul {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) :
    2 ∣ hammingNorm (d * e) := by
  have h := dotProduct_eq_zero hd he
  rw [dotProduct_eq_hammingNorm] at h
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

private theorem key_cast : ∀ a b c k : ZMod 2, c + k = a + b → c = a + b + k := by decide

theorem P_add {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) :
    P (d + e) = P d + P e + K d e := by
  have h := hammingNorm_add_add d e
  have h1 := four_dvd_wt hd
  have h2 := four_dvd_wt he
  have h3 := four_dvd_wt (C.add_mem hd he)
  have h4 := two_dvd_hammingNorm_mul hd he
  have hn : hammingNorm (d + e) / 4 + hammingNorm (d * e) / 2 =
      hammingNorm d / 4 + hammingNorm e / 4 := by omega
  rw [P, P, P, K_eq]
  apply key_cast
  exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hn

private theorem mul_self' (f : Fin 24 → ZMod 2) : f * f = f := by
  funext i
  simp only [Pi.mul_apply]
  rcases zmod2_cases (f i) with h | h <;> rw [h] <;> rfl

theorem K_add_left {d e f : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) (hf : f ∈ C) :
    K (d + e) f = K d f + K e f + A d e f := by
  have h := hammingNorm_add_add (d * f) (e * f)
  have hde : d * f + e * f = (d + e) * f := (add_mul d e f).symm
  have hdef : d * f * (e * f) = d * e * f := by
    funext i
    simp only [Pi.mul_apply]
    generalize d i = a, e i = b, f i = c
    revert a b c; decide
  rw [hde, hdef] at h
  have h1 := two_dvd_hammingNorm_mul hd hf
  have h2 := two_dvd_hammingNorm_mul he hf
  have h3 := two_dvd_hammingNorm_mul (C.add_mem hd he) hf
  have hn : hammingNorm ((d + e) * f) / 2 + hammingNorm (d * e * f) =
      hammingNorm (d * f) / 2 + hammingNorm (e * f) / 2 := by omega
  rw [K_eq, K_eq, K_eq, A, supp_inter, supp_inter, card_supp]
  apply key_cast
  exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 2) hn

theorem K_self {d : Fin 24 → ZMod 2} (hd : d ∈ C) : K d d = 0 := by
  rw [K_eq, mul_self']
  obtain ⟨m, hm⟩ := four_dvd_wt hd
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat, two_eq_zero', zero_mul]

theorem A_self_left {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d d e = 0 := by
  calc A d d e = ∑ i, d i * e i := by
        rw [A_eq_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← Pi.mul_apply d d i, mul_self']
    _ = d ⬝ᵥ e := rfl
    _ = 0 := dotProduct_eq_zero hd he

theorem A_self_mid {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d e d = 0 := by
  rw [A_comm₂₃, A_self_left hd he]

theorem A_self_right {d e : Fin 24 → ZMod 2} (hd : d ∈ C) (he : e ∈ C) : A d e e = 0 := by
  rw [A_comm₁₂, A_comm₂₃, A_self_left he hd]

@[expose] def lt01 (i j : Fin 12) : ZMod 2 := if i < j then 1 else 0

@[expose] def Ab (i j k : Fin 12) : ZMod 2 := A (B i) (B j) (B k)

theorem θc_eq (μ ν : Fin 12 → ZMod 2) : θc μ ν =
    ∑ i, ∑ j, μ i * ν j * β i j + ∑ i, ∑ j, ∑ k, lt01 i j * μ i * μ j * ν k * Ab i j k := by
  rw [θc]
  refine congrArg (HAdd.hAdd _) (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_)
  simp only [lt01, Ab]
  split_ifs <;> ring

theorem θc_add_right (μ ν ν' : Fin 12 → ZMod 2) : θc μ (ν + ν') = θc μ ν + θc μ ν' := by
  simp only [θc_eq, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem θc_smul_right (μ ν : Fin 12 → ZMod 2) (c : ZMod 2) : θc μ (c • ν) = c * θc μ ν := by
  simp only [θc_eq, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring)

theorem θc_zero_left (ν : Fin 12 → ZMod 2) : θc 0 ν = 0 := by
  simp [θc_eq]

theorem θc_zero_right (μ : Fin 12 → ZMod 2) : θc μ 0 = 0 := by
  simp [θc_eq]

theorem Ab_comm (i j k : Fin 12) : Ab i j k = Ab j i k := A_comm₁₂ _ _ _

theorem Ab_self (i k : Fin 12) : Ab i i k = 0 := A_self_left (B_mem_C i) (B_mem_C k)

private theorem lt01_add_mul (i j k : Fin 12) : (lt01 i j + lt01 j i) * Ab i j k = Ab i j k := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [lt01, h, not_lt_of_gt h]
  · simp [Ab_self]
  · simp [lt01, h, not_lt_of_gt h]

@[expose] def Atri (μ μ' ν : Fin 12 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, ∑ k, μ i * μ' j * ν k * Ab i j k

theorem θc_add_left (μ μ' ν : Fin 12 → ZMod 2) :
    θc (μ + μ') ν = θc μ ν + θc μ' ν + Atri μ μ' ν := by
  have hpol : Atri μ μ' ν = ∑ i, ∑ j, ∑ k, lt01 i j * μ i * μ' j * ν k * Ab i j k +
      ∑ i, ∑ j, ∑ k, lt01 i j * μ' i * μ j * ν k * Ab i j k := by
    rw [Finset.sum_comm (f := fun i j => ∑ k, lt01 i j * μ' i * μ j * ν k * Ab i j k),
      ← Finset.sum_add_distrib, Atri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Ab_comm j i k]
    linear_combination (μ i * μ' j * ν k) * (lt01_add_mul i j k).symm
  rw [hpol]
  simp only [θc_eq, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem θc_single (i j : Fin 12) : θc (Pi.single i 1) (Pi.single j 1) = β i j := by
  simp [θc_eq, Pi.single_apply, ite_mul, mul_ite, lt01, Finset.sum_ite_eq']

theorem repr_apply (d : C) (i : Fin 12) : basisC.repr d i = ψ d i := by
  have h : basisC.equivFun.symm (ψ d) = d := by
    apply Subtype.ext
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    simp only [Submodule.coe_smul, basisC_apply]
    exact (eq_comb_of_mem_C d.2).symm
  have h' := congrArg (fun x => basisC.equivFun x i) h
  simp only [LinearEquiv.apply_symm_apply] at h'
  rw [h', Module.Basis.equivFun_apply]

theorem coe_eq_sum (d : C) : (d : Fin 24 → ZMod 2) = ∑ i, basisC.repr d i • B i := by
  conv_lhs => rw [← basisC.sum_repr d]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, basisC_apply]

theorem Atri_repr (d e f : C) :
    Atri (basisC.repr d) (basisC.repr e) (basisC.repr f) = A d e f := by
  rw [coe_eq_sum d, coe_eq_sum e, coe_eq_sum f, A_sum_left, Atri]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A_sum_mid, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [A_sum_right, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Ab]
  ring

theorem θ_add_right (d e f : C) : θ d (e + f) = θ d e + θ d f := by
  rw [θ, θ, θ, map_add, Finsupp.coe_add, θc_add_right]

theorem θ_smul_right (d e : C) (c : ZMod 2) : θ d (c • e) = c * θ d e := by
  rw [θ, θ, map_smul, Finsupp.coe_smul, θc_smul_right]

theorem θ_add_left (d e f : C) : θ (d + e) f = θ d f + θ e f + A d e f := by
  rw [θ, θ, θ, map_add, Finsupp.coe_add, θc_add_left, Atri_repr]

@[simp] theorem θ_zero_left (e : C) : θ 0 e = 0 := by
  rw [θ, map_zero, Finsupp.coe_zero, θc_zero_left]

@[simp] theorem θ_zero_right (d : C) : θ d 0 = 0 := by
  rw [θ, map_zero, Finsupp.coe_zero, θc_zero_right]

theorem θ_basis (i j : Fin 12) : θ (basisC i) (basisC j) = β i j := by
  rw [θ, basisC.repr_self, basisC.repr_self, Finsupp.single_eq_pi_single,
    Finsupp.single_eq_pi_single, θc_single]

theorem eq_zero_of_additive (f : C → ZMod 2) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hB : ∀ i, f (basisC i) = 0) (x : C) : f x = 0 := by
  let F : C →+ ZMod 2 := AddMonoidHom.mk' f hadd
  show F x = 0
  rw [← basisC.sum_repr x, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases zmod2_cases (basisC.repr x i) with h | h <;> rw [h]
  · rw [zero_smul, map_zero]
  · rw [one_smul]; exact hB i

theorem θ_add_θ_swap (d e : C) : θ d e + θ e d = K d e := by
  let S : C → C → ZMod 2 := fun d e => θ d e + θ e d + K d e
  have hS : ∀ d d' e, S (d + d') e = S d e + S d' e := by
    intro d d' e
    simp only [S, θ_add_left, θ_add_right, Submodule.coe_add,
      K_add_left d.2 d'.2 e.2]
    linear_combination (A d d' e) * two_eq_zero'
  have hsymm : ∀ d e, S d e = S e d := by
    intro d e
    simp only [S, K_comm (d : Fin 24 → ZMod 2)]
    ring
  have hbasis : ∀ i j, S (basisC i) (basisC j) = 0 := by
    intro i j
    simp only [S, θ_basis, basisC_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · have h1 : β i j = 0 := by simp [β, h]
      have h2 : β j i = K (B j) (B i) := by simp [β, not_lt_of_gt h, (ne_of_lt h).symm]
      rw [h1, h2, K_comm (B j), zero_add]
      linear_combination (K (B i) (B j)) * two_eq_zero'
    · have h1 : β i i = P (B i) := by simp [β]
      rw [h1, K_self (B_mem_C i)]
      linear_combination (P (B i)) * two_eq_zero'
    · have h1 : β j i = 0 := by simp [β, h]
      have h2 : β i j = K (B i) (B j) := by simp [β, not_lt_of_gt h, (ne_of_lt h).symm]
      rw [h1, h2, K_comm (B i), add_zero]
      linear_combination (K (B j) (B i)) * two_eq_zero'
  have h1 : ∀ i e, S (basisC i) e = 0 := by
    intro i e
    rw [hsymm]
    exact eq_zero_of_additive (fun e => S e (basisC i)) (fun x y => hS x y _)
      (fun j => hbasis j i) e
  have h2 : S d e = 0 :=
    eq_zero_of_additive (fun d => S d e) (fun x y => hS x y _) (fun i => h1 i e) d
  linear_combination h2 - (K d e) * two_eq_zero'

theorem θ_self (d : C) : θ d d = P d := by
  let D : C → ZMod 2 := fun d => θ d d + P d
  have hD : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    simp only [D, θ_add_left, θ_add_right, Submodule.coe_add, P_add x.2 y.2,
      A_self_mid x.2 y.2, A_self_right x.2 y.2]
    have := θ_add_θ_swap x y
    linear_combination this + (K x y) * two_eq_zero'
  have hB : ∀ i, D (basisC i) = 0 := by
    intro i
    have h1 : β i i = P (B i) := by simp [β]
    simp only [D, θ_basis, basisC_apply, h1]
    linear_combination (P (B i)) * two_eq_zero'
  have h := eq_zero_of_additive D hD hB d
  linear_combination h - (P d) * two_eq_zero'

end CFSG.Monster.Code
