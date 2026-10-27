module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.Fan86

open Equiv

namespace FrobPrime

variable {Ω : Type*} [Finite Ω]

theorem exists_pow_apply_eq {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p) {σ : Perm Ω}
    (hσ : orderOf σ = p) (a b : Ω) : ∃ i : ℕ, (σ ^ i) a = b := by
  classical
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card] at hΩ
  have hcyc : σ.IsCycle := Perm.isCycle_of_prime_order'' (by rw [hΩ]; exact hp) (by rw [hσ, hΩ])
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hσ, hΩ]
  have hmove : ∀ x, σ x ≠ x := fun x =>
    Equiv.Perm.mem_support.1 (by rw [hsupp]; exact Finset.mem_univ x)
  exact hcyc.exists_pow_eq (hmove a) (hmove b)

theorem conj_pow_of_frobenius {p : ℕ} (hp : p.Prime) (hΩ : Nat.card Ω = p)
    (Q : Subgroup (Perm Ω))
    (hfrob : ∀ q ∈ Q, ∀ a b : Ω, a ≠ b → q a = a → q b = b → q = 1)
    {σ : Perm Ω} (hσQ : σ ∈ Q) (hσ : orderOf σ = p) :
    ∀ q ∈ Q, ∃ i : ℕ, q * σ * q⁻¹ = σ ^ i := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite Ω
  have hΩ' : Fintype.card Ω = p := by rwa [Nat.card_eq_fintype_card] at hΩ
  obtain ⟨a, b, hab⟩ : ∃ a b : Ω, a ≠ b :=
    Fintype.exists_pair_of_one_lt_card (by rw [hΩ']; exact hp.one_lt)
  let : Fintype Q := Fintype.ofFinite Q
  have hle : Nat.card Q ≤ p * p - p := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset Q))
      (t := (Finset.univ : Finset Ω).offDiag)
      (fun q => (((q : Perm Ω) a), ((q : Perm Ω) b)))
      (fun q _ => by
        rw [Finset.mem_coe, Finset.mem_offDiag]
        exact ⟨Finset.mem_univ _, Finset.mem_univ _, (q : Perm Ω).injective.ne hab⟩)
      (fun q _ q' _ h => by
        simp only [Prod.mk.injEq] at h
        have h1 : (q : Perm Ω)⁻¹ * q' = 1 := hfrob _ (Q.mul_mem (Q.inv_mem q.2) q'.2) a b hab
          (by simp [Perm.mul_apply, ← h.1]) (by simp [Perm.mul_apply, ← h.2])
        exact Subtype.ext (inv_mul_eq_one.1 h1))
    simpa [Nat.card_eq_fintype_card, Finset.offDiag_card, hΩ'] using h
  have hdvd : p ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨σ, hσQ⟩ : Q)
    rwa [Subgroup.orderOf_mk, hσ] at this
  obtain ⟨h, hh⟩ := hdvd
  have hpos : 0 < h := by
    have := Nat.card_pos (α := Q)
    rw [hh] at this
    exact Nat.pos_of_mul_pos_left this
  have hlt : h < p := by
    have h1 : p * h ≤ p * (p - 1) := by rw [Nat.mul_sub, mul_one]; omega
    have := Nat.le_of_mul_le_mul_left h1 hp.pos
    have := hp.pos
    omega
  set P : Subgroup Q := Subgroup.zpowers (⟨σ, hσQ⟩ : Q) with hP
  have hPcard : Nat.card P = p := by rw [hP, Nat.card_zpowers, Subgroup.orderOf_mk, hσ]
  have hPgrp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hindex : P.index = h := by
    have := P.card_mul_index
    rw [hPcard, hh] at this
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hndvd : ¬ p ∣ P.index := by
    rw [hindex]
    intro hd
    have := Nat.le_of_dvd hpos hd
    omega
  let S : Sylow p Q := hPgrp.toSylow hndvd
  have hmod := card_sylow_modEq_one p Q
  have hdiv := S.card_dvd_index
  have hn : Nat.card (Sylow p Q) = 1 := by
    have hle' : Nat.card (Sylow p Q) ≤ h := Nat.le_of_dvd hpos (by simpa [S, hindex] using hdiv)
    have h2 : Nat.card (Sylow p Q) % p = 1 % p := hmod
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp.one_lt] at h2
  have : Subsingleton (Sylow p Q) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hnorm : (S : Subgroup Q).Normal := Sylow.normal_of_subsingleton S
  intro q hq
  have hmem : (⟨q, hq⟩ * ⟨σ, hσQ⟩ * ⟨q, hq⟩⁻¹ : Q) ∈ P :=
    hnorm.conj_mem _ (Subgroup.mem_zpowers _) ⟨q, hq⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk' : q * σ * q⁻¹ = σ ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  refine ⟨(k % (orderOf σ : ℤ)).toNat, ?_⟩
  rw [hk', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
    exact_mod_cast (orderOf_pos σ).ne')), zpow_mod_orderOf]

structure Data (Ω : Type*) [Finite Ω] (p : ℕ) [Fact p.Prime] where
  Q : Subgroup (Perm Ω)
  σ : Perm Ω
  σ_mem : σ ∈ Q
  card_eq : Nat.card Ω = p
  orderOf_σ : orderOf σ = p
  conj : ∀ q ∈ Q, ∃ i : ℕ, q * σ * q⁻¹ = σ ^ i

namespace Data

variable {p : ℕ} [Fact p.Prime] (D : Data Ω p)

noncomputable def conjExp (q : D.Q) : ZMod p := ((Classical.choose (D.conj q q.2) : ℕ) : ZMod p)

theorem pow_val_eq_pow (n : ℕ) : D.σ ^ (n : ZMod p).val = D.σ ^ n := by
  rw [ZMod.val_natCast]
  have := pow_mod_orderOf D.σ n
  rwa [D.orderOf_σ] at this

theorem conjExp_spec (q : D.Q) :
    (q : Perm Ω) * D.σ * (q : Perm Ω)⁻¹ = D.σ ^ (D.conjExp q).val := by
  rw [conjExp, D.pow_val_eq_pow]
  exact Classical.choose_spec (D.conj q q.2)

theorem eq_of_pow_val_eq {c c' : ZMod p} (h : D.σ ^ c.val = D.σ ^ c'.val) : c = c' := by
  have h1 := pow_eq_pow_iff_modEq.1 h
  rw [D.orderOf_σ] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  simpa using h2

theorem conjExp_mul (q q' : D.Q) : D.conjExp (q * q') = D.conjExp q * D.conjExp q' := by
  apply D.eq_of_pow_val_eq
  calc D.σ ^ (D.conjExp (q * q')).val
      = ((q * q' : D.Q) : Perm Ω) * D.σ * ((q * q' : D.Q) : Perm Ω)⁻¹ := (D.conjExp_spec _).symm
    _ = (q : Perm Ω) * ((q' : Perm Ω) * D.σ * (q' : Perm Ω)⁻¹) * (q : Perm Ω)⁻¹ := by
        simp [mul_assoc]
    _ = (q : Perm Ω) * D.σ ^ (D.conjExp q').val * (q : Perm Ω)⁻¹ := by rw [D.conjExp_spec q']
    _ = ((q : Perm Ω) * D.σ * (q : Perm Ω)⁻¹) ^ (D.conjExp q').val := (conj_pow).symm
    _ = (D.σ ^ (D.conjExp q).val) ^ (D.conjExp q').val := by rw [D.conjExp_spec q]
    _ = D.σ ^ ((D.conjExp q).val * (D.conjExp q').val) := (pow_mul _ _ _).symm
    _ = D.σ ^ (D.conjExp q * D.conjExp q').val := by
        rw [ZMod.val_mul]
        have := pow_mod_orderOf D.σ ((D.conjExp q).val * (D.conjExp q').val)
        rw [D.orderOf_σ] at this
        exact this.symm

theorem conjExp_one : D.conjExp 1 = 1 := by
  apply D.eq_of_pow_val_eq
  rw [← D.conjExp_spec 1, ZMod.val_one]
  simp

noncomputable def conjChar : D.Q →* (ZMod p)ˣ :=
  MonoidHom.toHomUnits
    { toFun := D.conjExp, map_one' := D.conjExp_one, map_mul' := D.conjExp_mul }

theorem conjChar_spec (q : D.Q) :
    (q : Perm Ω) * D.σ * (q : Perm Ω)⁻¹ = D.σ ^ ((D.conjChar q : (ZMod p)ˣ) : ZMod p).val :=
  D.conjExp_spec q

theorem eq_one_of_conjChar_eq_one {q : D.Q} (h : D.conjChar q = 1) {a : Ω}
    (ha : (q : Perm Ω) a = a) : (q : Perm Ω) = 1 := by
  have h1 := D.conjChar_spec q
  rw [h] at h1
  simp only [Units.val_one, ZMod.val_one, pow_one] at h1
  have hcomm : Commute (q : Perm Ω) D.σ := by
    have := congrArg (· * (q : Perm Ω)) h1
    have h3 : (q : Perm Ω) * D.σ = D.σ * q := by simpa [mul_assoc] using this
    exact h3
  ext b
  obtain ⟨i, hi⟩ := exists_pow_apply_eq (Fact.out : p.Prime) D.card_eq D.orderOf_σ a b
  have h2 := congrArg (fun f : Perm Ω => f a) (hcomm.pow_right i).eq
  simp only [Perm.mul_apply, ha, hi] at h2
  simpa using h2

end Data

end FrobPrime

end CFSG.Quasithin.Fan86
