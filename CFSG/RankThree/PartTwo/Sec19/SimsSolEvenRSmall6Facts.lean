module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Perm
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.Comb (barPar barPar_mk)

@[expose] def esc1 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 0) (π 2) * swap (π 1) (π 3)

@[expose] def esc2 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 0) (π 4) * swap (π 1) (π 5)

@[expose] def rot1 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 1) (π 3) * swap (π 1) (π 2)

@[expose] def rot2 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 1) (π 5) * swap (π 1) (π 4)

@[expose] def rho3 (π : Perm (Fin 6)) : Perm (Fin 6) :=
  swap (π 0) (π 2) * swap (π 0) (π 4) * (swap (π 1) (π 3) * swap (π 1) (π 5))

@[expose] def quad1 (π : Perm (Fin 6)) : Perm (Fin 6) :=
  swap (π 0) (π 3) * swap (π 0) (π 1) * swap (π 0) (π 2) * swap (π 4) (π 5)

private theorem esc1_eq (π : Perm (Fin 6)) : esc1 π = π * esc1 1 * π⁻¹ := by
  unfold esc1
  rw [swap_apply_apply π 0 2, swap_apply_apply π 1 3]
  simp [mul_assoc]

private theorem esc2_eq (π : Perm (Fin 6)) : esc2 π = π * esc2 1 * π⁻¹ := by
  unfold esc2
  rw [swap_apply_apply π 0 4, swap_apply_apply π 1 5]
  simp [mul_assoc]

private theorem rot1_eq (π : Perm (Fin 6)) : rot1 π = π * rot1 1 * π⁻¹ := by
  unfold rot1
  rw [swap_apply_apply π 1 3, swap_apply_apply π 1 2]
  simp [mul_assoc]

private theorem rot2_eq (π : Perm (Fin 6)) : rot2 π = π * rot2 1 * π⁻¹ := by
  unfold rot2
  rw [swap_apply_apply π 1 5, swap_apply_apply π 1 4]
  simp [mul_assoc]

private theorem rho3_eq (π : Perm (Fin 6)) : rho3 π = π * rho3 1 * π⁻¹ := by
  unfold rho3
  rw [swap_apply_apply π 0 2, swap_apply_apply π 0 4, swap_apply_apply π 1 3,
    swap_apply_apply π 1 5]
  simp [mul_assoc]

private theorem quad1_eq (π : Perm (Fin 6)) : quad1 π = π * quad1 1 * π⁻¹ := by
  unfold quad1
  rw [swap_apply_apply π 0 3, swap_apply_apply π 0 1, swap_apply_apply π 0 2,
    swap_apply_apply π 4 5]
  simp [mul_assoc]

private theorem conj_sig1 (π : Perm (Fin 6)) : π⁻¹ * sig1 π * π = sig1 1 := by
  rw [sig1_eq π]
  group

private theorem conj_sig2 (π : Perm (Fin 6)) : π⁻¹ * sig2 π * π = sig2 1 := by
  rw [sig2_eq π]
  group

private theorem conj_esc1 (π : Perm (Fin 6)) : π⁻¹ * esc1 π * π = esc1 1 := by
  rw [esc1_eq π]
  group

private theorem conj_esc2 (π : Perm (Fin 6)) : π⁻¹ * esc2 π * π = esc2 1 := by
  rw [esc2_eq π]
  group

private theorem mem_alt_of_eq {π a b : Perm (Fin 6)} (h : a = π * b * π⁻¹)
    (hb : b ∈ alternatingGroup (Fin 6)) : a ∈ alternatingGroup (Fin 6) := by
  rw [h]
  exact Subgroup.Normal.conj_mem inferInstance b hb π

theorem sig1_mem_alternatingGroup (π : Perm (Fin 6)) : sig1 π ∈ alternatingGroup (Fin 6) :=
  mem_alt_of_eq (sig1_eq π) (by rw [mem_alternatingGroup]; decide +kernel)

theorem sig2_mem_alternatingGroup (π : Perm (Fin 6)) : sig2 π ∈ alternatingGroup (Fin 6) :=
  mem_alt_of_eq (sig2_eq π) (by rw [mem_alternatingGroup]; decide +kernel)

theorem rho3_mem_alternatingGroup (π : Perm (Fin 6)) : rho3 π ∈ alternatingGroup (Fin 6) :=
  mem_alt_of_eq (rho3_eq π) (by rw [mem_alternatingGroup]; decide +kernel)

theorem quad1_mem_alternatingGroup (π : Perm (Fin 6)) : quad1 π ∈ alternatingGroup (Fin 6) :=
  mem_alt_of_eq (quad1_eq π) (by rw [mem_alternatingGroup]; decide +kernel)

theorem rot1_isThreeCycle (π : Perm (Fin 6)) : (rot1 π).IsThreeCycle := by
  rw [← card_support_eq_three_iff, rot1_eq π, card_support_conj]
  decide +kernel

theorem rot2_isThreeCycle (π : Perm (Fin 6)) : (rot2 π).IsThreeCycle := by
  rw [← card_support_eq_three_iff, rot2_eq π, card_support_conj]
  decide +kernel

private theorem fin_rot1_sig1 : rot1 1 * sig1 1 * (rot1 1)⁻¹ = esc1 1 := by decide +kernel

private theorem fin_rot1_esc1 : rot1 1 * esc1 1 * (rot1 1)⁻¹ = sig1 1 * esc1 1 := by
  decide +kernel

private theorem fin_sig1_esc1 : sig1 1 * esc1 1 = esc1 1 * sig1 1 := by decide +kernel

private theorem fin_rot2_sig2 : rot2 1 * sig2 1 * (rot2 1)⁻¹ = esc2 1 := by decide +kernel

private theorem fin_rot2_esc2 : rot2 1 * esc2 1 * (rot2 1)⁻¹ = sig2 1 * esc2 1 := by
  decide +kernel

private theorem fin_sig2_esc2 : sig2 1 * esc2 1 = esc2 1 * sig2 1 := by decide +kernel

private theorem fin_esc_pow : (esc1 1 * esc2 1) ^ 3 = 1 := by decide +kernel

private theorem fin_esc_ne : esc1 1 * esc2 1 ≠ 1 := by decide +kernel

private theorem fin_rho3_sig1 : rho3 1 * sig1 1 * (rho3 1)⁻¹ = sig2 1 := by decide +kernel

private theorem fin_rho3_sig2 : rho3 1 * sig2 1 * (rho3 1)⁻¹ = sig1 1 * sig2 1 := by
  decide +kernel

private theorem fin_quad1_sq : quad1 1 * quad1 1 = sig1 1 := by decide +kernel

private theorem fin_sig2_quad1 : sig2 1 * quad1 1 = esc1 1 := by decide +kernel

private theorem fin_quad1_sig1 : quad1 1 * sig1 1 = sig1 1 * quad1 1 := by decide +kernel

private theorem fin_sig2_sig1 : sig2 1 * sig1 1 = sig1 1 * sig2 1 := by decide +kernel

theorem rot1_conj_sig1 (π : Perm (Fin 6)) : rot1 π * sig1 π * (rot1 π)⁻¹ = esc1 π := by
  have h := congrArg (MulAut.conj π) fin_rot1_sig1
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rot1_eq π, sig1_eq π, esc1_eq π]
  exact h

theorem rot1_conj_esc1 (π : Perm (Fin 6)) :
    rot1 π * esc1 π * (rot1 π)⁻¹ = sig1 π * esc1 π := by
  have h := congrArg (MulAut.conj π) fin_rot1_esc1
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rot1_eq π, sig1_eq π, esc1_eq π]
  exact h

theorem sig1_mul_esc1 (π : Perm (Fin 6)) : sig1 π * esc1 π = esc1 π * sig1 π := by
  have h := congrArg (MulAut.conj π) fin_sig1_esc1
  simp only [map_mul, MulAut.conj_apply] at h
  rw [sig1_eq π, esc1_eq π]
  exact h

theorem rot2_conj_sig2 (π : Perm (Fin 6)) : rot2 π * sig2 π * (rot2 π)⁻¹ = esc2 π := by
  have h := congrArg (MulAut.conj π) fin_rot2_sig2
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rot2_eq π, sig2_eq π, esc2_eq π]
  exact h

theorem rot2_conj_esc2 (π : Perm (Fin 6)) :
    rot2 π * esc2 π * (rot2 π)⁻¹ = sig2 π * esc2 π := by
  have h := congrArg (MulAut.conj π) fin_rot2_esc2
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rot2_eq π, sig2_eq π, esc2_eq π]
  exact h

theorem sig2_mul_esc2 (π : Perm (Fin 6)) : sig2 π * esc2 π = esc2 π * sig2 π := by
  have h := congrArg (MulAut.conj π) fin_sig2_esc2
  simp only [map_mul, MulAut.conj_apply] at h
  rw [sig2_eq π, esc2_eq π]
  exact h

theorem esc1_mul_esc2_pow_three (π : Perm (Fin 6)) : (esc1 π * esc2 π) ^ 3 = 1 := by
  have h := congrArg (MulAut.conj π) fin_esc_pow
  simp only [map_mul, map_pow, map_one, MulAut.conj_apply] at h
  rw [esc1_eq π, esc2_eq π]
  exact h

theorem esc1_mul_esc2_ne_one (π : Perm (Fin 6)) : esc1 π * esc2 π ≠ 1 := by
  intro h
  apply fin_esc_ne
  apply (MulAut.conj π).injective
  rw [map_mul, map_one]
  simp only [MulAut.conj_apply]
  rw [← esc1_eq π, ← esc2_eq π]
  exact h

theorem rho3_conj_sig1 (π : Perm (Fin 6)) : rho3 π * sig1 π * (rho3 π)⁻¹ = sig2 π := by
  have h := congrArg (MulAut.conj π) fin_rho3_sig1
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rho3_eq π, sig1_eq π, sig2_eq π]
  exact h

theorem rho3_conj_sig2 (π : Perm (Fin 6)) :
    rho3 π * sig2 π * (rho3 π)⁻¹ = sig1 π * sig2 π := by
  have h := congrArg (MulAut.conj π) fin_rho3_sig2
  simp only [map_mul, map_inv, MulAut.conj_apply] at h
  rw [rho3_eq π, sig1_eq π, sig2_eq π]
  exact h

theorem quad1_mul_self (π : Perm (Fin 6)) : quad1 π * quad1 π = sig1 π := by
  have h := congrArg (MulAut.conj π) fin_quad1_sq
  simp only [map_mul, MulAut.conj_apply] at h
  rw [quad1_eq π, sig1_eq π]
  exact h

theorem sig2_mul_quad1 (π : Perm (Fin 6)) : sig2 π * quad1 π = esc1 π := by
  have h := congrArg (MulAut.conj π) fin_sig2_quad1
  simp only [map_mul, MulAut.conj_apply] at h
  rw [sig2_eq π, quad1_eq π, esc1_eq π]
  exact h

theorem quad1_mul_sig1 (π : Perm (Fin 6)) : quad1 π * sig1 π = sig1 π * quad1 π := by
  have h := congrArg (MulAut.conj π) fin_quad1_sig1
  simp only [map_mul, MulAut.conj_apply] at h
  rw [quad1_eq π, sig1_eq π]
  exact h

theorem sig2_mul_sig1 (π : Perm (Fin 6)) : sig2 π * sig1 π = sig1 π * sig2 π := by
  have h := congrArg (MulAut.conj π) fin_sig2_sig1
  simp only [map_mul, MulAut.conj_apply] at h
  rw [sig2_eq π, sig1_eq π]
  exact h

@[expose] def cent1 (π : Perm (Fin 6)) : Subgroup ↥(alternatingGroup (Fin 6)) :=
  Subgroup.centralizer {⟨sig1 π, sig1_mem_alternatingGroup π⟩}

private theorem fin_cent : ∀ τ : Perm (Fin 6), τ * sig1 1 = sig1 1 * τ → sign τ = 1 →
    ∃ i < 4, ∃ j < 2, τ = quad1 1 ^ i * sig2 1 ^ j := by
  decide +kernel

private theorem fin_one : ∀ i < 4, ∀ j < 2, quad1 1 ^ i * sig2 1 ^ j = 1 → i = 0 ∧ j = 0 := by
  decide +kernel

private theorem fin_inj : ∀ p q : Fin 4 × Fin 2,
    quad1 1 ^ p.1.val * sig2 1 ^ p.2.val = quad1 1 ^ q.1.val * sig2 1 ^ q.2.val → p = q := by
  decide +kernel

private theorem quad1_pow_mul_sig2_pow (π : Perm (Fin 6)) (i j : ℕ) :
    quad1 π ^ i * sig2 π ^ j = π * (quad1 1 ^ i * sig2 1 ^ j) * π⁻¹ := by
  have h : MulAut.conj π (quad1 1 ^ i * sig2 1 ^ j) =
      MulAut.conj π (quad1 1) ^ i * MulAut.conj π (sig2 1) ^ j := by
    rw [map_mul, map_pow, map_pow]
  simp only [MulAut.conj_apply] at h
  rw [quad1_eq π, sig2_eq π]
  exact h.symm

theorem eq_of_mem_cent1 (π : Perm (Fin 6)) {σ : ↥(alternatingGroup (Fin 6))}
    (hσ : σ ∈ cent1 π) : ∃ i < 4, ∃ j < 2, (σ : Perm (Fin 6)) = quad1 π ^ i * sig2 π ^ j := by
  have hc : (σ : Perm (Fin 6)) * sig1 π = sig1 π * (σ : Perm (Fin 6)) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hσ)
  have hs : sign (π⁻¹ * (σ : Perm (Fin 6)) * π) = 1 := by
    rw [← mem_alternatingGroup]
    have := Subgroup.Normal.conj_mem inferInstance (σ : Perm (Fin 6)) σ.2 π⁻¹
    rwa [inv_inv] at this
  have hc' : π⁻¹ * (σ : Perm (Fin 6)) * π * sig1 1 =
      sig1 1 * (π⁻¹ * (σ : Perm (Fin 6)) * π) := by
    rw [← conj_sig1 π]
    calc π⁻¹ * (σ : Perm (Fin 6)) * π * (π⁻¹ * sig1 π * π)
        = π⁻¹ * ((σ : Perm (Fin 6)) * sig1 π) * π := by group
      _ = π⁻¹ * (sig1 π * (σ : Perm (Fin 6))) * π := by rw [hc]
      _ = π⁻¹ * sig1 π * π * (π⁻¹ * (σ : Perm (Fin 6)) * π) := by group
  obtain ⟨i, hi, j, hj, h⟩ := fin_cent _ hc' hs
  refine ⟨i, hi, j, hj, ?_⟩
  rw [quad1_pow_mul_sig2_pow, ← h]
  group

theorem quad1_pow_mul_eq_one (π : Perm (Fin 6)) {i j : ℕ} (hi : i < 4) (hj : j < 2)
    (h : quad1 π ^ i * sig2 π ^ j = 1) : i = 0 ∧ j = 0 := by
  refine fin_one i hi j hj ?_
  rw [quad1_pow_mul_sig2_pow] at h
  calc quad1 1 ^ i * sig2 1 ^ j = π⁻¹ * (π * (quad1 1 ^ i * sig2 1 ^ j) * π⁻¹) * π := by group
    _ = 1 := by rw [h]; group

private theorem natCard_alt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have h6 : Nat.factorial 6 = 720 := rfl
  omega

private theorem natCard_cent1 (π : Perm (Fin 6)) : Nat.card (cent1 π) = 8 := by
  have hmem : ∀ p : Fin 4 × Fin 2,
      quad1 π ^ p.1.val * sig2 π ^ p.2.val ∈ alternatingGroup (Fin 6) := fun p =>
    mul_mem (pow_mem (quad1_mem_alternatingGroup π) _) (pow_mem (sig2_mem_alternatingGroup π) _)
  have hcent : ∀ p : Fin 4 × Fin 2,
      (⟨_, hmem p⟩ : ↥(alternatingGroup (Fin 6))) ∈ cent1 π := fun p => by
    rw [cent1, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Commute.pow_left (quad1_mul_sig1 π) _).mul_left
      (Commute.pow_left (sig2_mul_sig1 π) _)
  let f : Fin 4 × Fin 2 → cent1 π := fun p => ⟨⟨_, hmem p⟩, hcent p⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h := congrArg
        (fun x : cent1 π => ((x : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) hpq
      simp only [f] at h
      rw [quad1_pow_mul_sig2_pow π, quad1_pow_mul_sig2_pow π] at h
      exact fin_inj p q (mul_left_cancel (mul_right_cancel h))
    · rintro ⟨σ, hσ⟩
      obtain ⟨i, hi, j, hj, h⟩ := eq_of_mem_cent1 π hσ
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext (Subtype.ext h.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem index_cent1 (π : Perm (Fin 6)) : (cent1 π).index = 45 := by
  have h := Subgroup.card_mul_index (cent1 π)
  rw [natCard_cent1 π, natCard_alt] at h
  omega

private theorem barAct_inv_conj (π σ : Perm (Fin 6)) (w : permBar 6) :
    barAct π⁻¹ (barAct σ w) = barAct (π⁻¹ * σ * π) (barAct π⁻¹ w) := by
  rw [barAct_mul, barAct_mul, ← barAct_mul π π⁻¹, mul_inv_cancel, barAct_one, ← barAct_mul]

private theorem fin_A : ∀ x₁ : Fin 6 → ZMod 2,
    (-vecPerm (sig1 1) x₁ + x₁ = 0 ∨ -vecPerm (sig1 1) x₁ + x₁ = allOnes 6) →
    ∀ x₂ : Fin 6 → ZMod 2,
    (-vecPerm (sig2 1) x₂ + x₂ = 0 ∨ -vecPerm (sig2 1) x₂ + x₂ = allOnes 6) →
    (vecPerm (sig2 1) x₁ + x₁ + (vecPerm (sig1 1) x₂ + x₂) = 0 ∨
      vecPerm (sig2 1) x₁ + x₁ + (vecPerm (sig1 1) x₂ + x₂) = allOnes 6) →
    ∑ i, x₁ i = 0 ∧ ∑ i, x₂ i = 0 := by
  decide +kernel

private theorem fin_B1 : ∀ x : Fin 6 → ZMod 2,
    (-vecPerm (sig1 1) x + x = 0 ∨ -vecPerm (sig1 1) x + x = allOnes 6) →
    (-vecPerm (esc1 1) x + x = 0 ∨ -vecPerm (esc1 1) x + x = allOnes 6) →
    (-vecPerm (rot1 1) x + x = 0 ∨ -vecPerm (rot1 1) x + x = allOnes 6) := by
  decide +kernel

private theorem fin_B2 : ∀ x : Fin 6 → ZMod 2,
    (-vecPerm (sig2 1) x + x = 0 ∨ -vecPerm (sig2 1) x + x = allOnes 6) →
    (-vecPerm (esc2 1) x + x = 0 ∨ -vecPerm (esc2 1) x + x = allOnes 6) →
    (-vecPerm (rot2 1) x + x = 0 ∨ -vecPerm (rot2 1) x + x = allOnes 6) := by
  decide +kernel

theorem barPar_eq_zero_of_fixed (hn : Even 6) (π : Perm (Fin 6)) {w₁ w₂ : permBar 6}
    (h1 : barAct (sig1 π) w₁ = w₁) (h2 : barAct (sig2 π) w₂ = w₂)
    (h : barAct (sig2 π) w₁ + w₁ + (barAct (sig1 π) w₂ + w₂) = 0) :
    barPar hn w₁ = 0 ∧ barPar hn w₂ = 0 := by
  obtain ⟨x₁, hx₁⟩ := QuotientAddGroup.mk_surjective (barAct π⁻¹ w₁)
  obtain ⟨x₂, hx₂⟩ := QuotientAddGroup.mk_surjective (barAct π⁻¹ w₂)
  have f1 := congrArg (barAct π⁻¹) h1
  have f2 := congrArg (barAct π⁻¹) h2
  have f3 := congrArg (barAct π⁻¹) h
  rw [barAct_inv_conj, conj_sig1, ← hx₁, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f1
  rw [barAct_inv_conj, conj_sig2, ← hx₂, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f2
  simp only [map_zero, map_add] at f3
  rw [barAct_inv_conj π (sig2 π) w₁, barAct_inv_conj π (sig1 π) w₂, conj_sig2, conj_sig1,
    ← hx₁, ← hx₂] at f3
  simp only [barAct_mk, ← QuotientAddGroup.mk_add] at f3
  rw [QuotientAddGroup.eq_zero_iff, mem_zmultiples_allOnes_iff] at f3
  have hpar : ∀ u : permBar 6, barPar hn (barAct π⁻¹ u) = barPar hn u := by
    intro u
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [barAct_mk, barPar_mk, barPar_mk]
    simp only [vecPerm_apply, inv_inv]
    exact Equiv.sum_comp π x
  rw [← hpar w₁, ← hpar w₂, ← hx₁, ← hx₂, barPar_mk, barPar_mk]
  exact fin_A x₁ f1 x₂ f2 f3

theorem barAct_rot1_eq (π : Perm (Fin 6)) {v : permBar 6} (h1 : barAct (sig1 π) v = v)
    (h2 : barAct (esc1 π) v = v) : barAct (rot1 π) v = v := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (barAct π⁻¹ v)
  have f1 := congrArg (barAct π⁻¹) h1
  have f2 := congrArg (barAct π⁻¹) h2
  rw [barAct_inv_conj, conj_sig1, ← hx, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f1
  rw [barAct_inv_conj, conj_esc1, ← hx, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f2
  have f4 : barAct (rot1 1) (barAct π⁻¹ v) = barAct π⁻¹ v := by
    rw [← hx, barAct_mk, QuotientAddGroup.eq, mem_zmultiples_allOnes_iff]
    exact fin_B1 x f1 f2
  rw [rot1_eq π, barAct_mul, barAct_mul, f4, ← barAct_mul, mul_inv_cancel, barAct_one]

theorem barAct_rot2_eq (π : Perm (Fin 6)) {v : permBar 6} (h1 : barAct (sig2 π) v = v)
    (h2 : barAct (esc2 π) v = v) : barAct (rot2 π) v = v := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (barAct π⁻¹ v)
  have f1 := congrArg (barAct π⁻¹) h1
  have f2 := congrArg (barAct π⁻¹) h2
  rw [barAct_inv_conj, conj_sig2, ← hx, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f1
  rw [barAct_inv_conj, conj_esc2, ← hx, barAct_mk, QuotientAddGroup.eq,
    mem_zmultiples_allOnes_iff] at f2
  have f4 : barAct (rot2 1) (barAct π⁻¹ v) = barAct π⁻¹ v := by
    rw [← hx, barAct_mk, QuotientAddGroup.eq, mem_zmultiples_allOnes_iff]
    exact fin_B2 x f1 f2
  rw [rot2_eq π, barAct_mul, barAct_mul, f4, ← barAct_mul, mul_inv_cancel, barAct_one]

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
