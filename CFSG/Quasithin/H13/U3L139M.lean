module

public import CFSG.Quasithin.H13.A6Setting134

public section

namespace CFSG.Quasithin.H13.U3

open Equiv CFSG.Quasithin.H13.A6

@[expose] def InA4 (σ : Perm (Fin 6)) : Prop := σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1

instance : DecidablePred InA4 := fun σ => by unfold InA4; infer_instance

@[expose] def Pres45 (σ : Perm (Fin 6)) : Prop := (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4)

instance : DecidablePred Pres45 := fun σ => by unfold Pres45; infer_instance

theorem pow_45_of_odd' {σ : Perm (Fin 6)} {m : ℕ} (hm : Odd m) (h : σ ^ m = 1) :
    σ ^ 45 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h1 : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 2 ^ 4 * 45 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  have hcop : (orderOf σ).Coprime (2 ^ 4) :=
    Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 (Odd.of_dvd_nat hm h1))
  exact hcop.dvd_of_dvd_mul_left h2

theorem inA4_of_pres45 : ∀ σ : Perm (Fin 6), Pres45 σ → σ ^ 45 = 1 → InA4 σ := by
  decide +kernel

theorem cube_of_inA4 : ∀ σ : Perm (Fin 6), InA4 σ → σ ^ 45 = 1 → σ ^ 3 = 1 := by
  decide +kernel

theorem inA4_one : InA4 1 := by decide

theorem inA4_mul {σ τ : Perm (Fin 6)} (hσ : InA4 σ) (hτ : InA4 τ) : InA4 (σ * τ) := by
  obtain ⟨h4, h5, hs⟩ := hσ
  obtain ⟨k4, k5, ks⟩ := hτ
  refine ⟨?_, ?_, ?_⟩
  · rw [Perm.mul_apply, k4, h4]
  · rw [Perm.mul_apply, k5, h5]
  · rw [Perm.sign_mul, hs, ks, mul_one]

theorem inA4_inv {σ : Perm (Fin 6)} (hσ : InA4 σ) : InA4 σ⁻¹ := by
  obtain ⟨h4, h5, hs⟩ := hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [Perm.inv_eq_iff_eq]
    exact h4.symm
  · rw [Perm.inv_eq_iff_eq]
    exact h5.symm
  · rw [Perm.sign_inv, hs]

theorem inA4_pow {σ : Perm (Fin 6)} (hσ : InA4 σ) (n : ℕ) : InA4 (σ ^ n) := by
  induction n with
  | zero => exact inA4_one
  | succ n ih =>
    rw [pow_succ]
    exact inA4_mul ih hσ

@[expose] def c012 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def k4L : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

@[expose] def a4L : List (Perm (Fin 6)) :=
  k4L ++ k4L.map (· * c012) ++ k4L.map (· * (c012 * c012))

theorem inA4_iff_mem : ∀ σ : Perm (Fin 6), InA4 σ ↔ σ ∈ a4L := by
  decide +kernel

@[expose] def d0 : Perm (Fin 6) := swap 0 1 * swap 2 3

theorem d0_mem : InD6 d0 ∧ d0 ∈ alternatingGroup (Fin 6) := by
  refine ⟨by decide, ?_⟩
  rw [Perm.mem_alternatingGroup]
  decide

theorem a4_gen_list : ∀ c ∈ a4L, c ^ 3 = 1 → c ≠ 1 → ∀ σ ∈ a4L,
    ∃ a ∈ [0, 1, 2], ∃ b ∈ [0, 1, 2], ∃ e ∈ [0, 1, 2],
      σ = c ^ a * (d0 * c * d0⁻¹) ^ b * c ^ e := by
  decide +kernel

theorem a4_gen {c : Perm (Fin 6)} (hc : InA4 c) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {σ : Perm (Fin 6)} (hσ : InA4 σ) :
    ∃ a b e : ℕ, σ = c ^ a * (d0 * c * d0⁻¹) ^ b * c ^ e := by
  obtain ⟨a, -, b, -, e, -, h⟩ := a4_gen_list c ((inA4_iff_mem c).1 hc) hc3 hc1 σ
    ((inA4_iff_mem σ).1 hσ)
  exact ⟨a, b, e, h⟩

@[expose] def d1 : Perm (Fin 6) := swap 0 1 * swap 4 5

theorem d1_mem : InD6 d1 ∧ d1 ∈ alternatingGroup (Fin 6) := by
  refine ⟨by decide, ?_⟩
  rw [Perm.mem_alternatingGroup]
  decide

theorem comm_c012_d1 : InA4 (c012 * d1 * c012⁻¹ * d1⁻¹) ∧
    (c012 * d1 * c012⁻¹ * d1⁻¹) ^ 3 = 1 ∧ c012 * d1 * c012⁻¹ * d1⁻¹ ≠ 1 ∧ InA4 c012 := by
  decide +kernel

@[expose] def c234 : Perm (Fin 6) := swap 2 3 * swap 3 4

theorem c012_c234 : c012 ∈ alternatingGroup (Fin 6) ∧ c234 ∈ alternatingGroup (Fin 6) ∧
    ∀ σ : Perm (Fin 6), σ * c012 = c012 * σ → σ * c234 = c234 * σ → σ = 1 := by
  simp only [Perm.mem_alternatingGroup]
  decide +kernel

theorem card_DA : (Finset.univ.filter fun σ : Perm (Fin 6) =>
    InD6 σ ∧ Perm.sign σ = 1).card = 8 := by
  decide +kernel

end CFSG.Quasithin.H13.U3
