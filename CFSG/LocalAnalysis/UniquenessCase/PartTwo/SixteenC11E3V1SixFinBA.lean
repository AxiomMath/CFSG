module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixNormA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13.U3.S6Out Equiv

@[expose] def s1611e3_sixE6Nat (x : SixE6) : ℕ :=
  ∑ i : Fin 6, (Multiplicative.toAdd (x : PermMod 6) i).val * 2 ^ (i : ℕ)

@[expose] def s1611e3_sixBitAct (σ : Perm (Fin 6)) (m : ℕ) : ℕ :=
  ∑ i : Fin 6, ((m >>> (σ⁻¹ i).val) &&& 1) * 2 ^ (i : ℕ)

theorem s1611e3_sixE6Nat_lt (x : SixE6) : s1611e3_sixE6Nat x < 64 := by
  revert x
  decide +kernel

theorem s1611e3_sixE6Nat_injective : Function.Injective s1611e3_sixE6Nat := by
  decide +kernel

theorem s1611e3_sixE6Nat_coreAct (σ : Perm (Fin 6)) (x : SixE6) :
    s1611e3_sixE6Nat (coreAct 6 σ x) = s1611e3_sixBitAct σ (s1611e3_sixE6Nat x) := by
  revert σ x
  decide +kernel

theorem s1611e3_sixE6Nat_add (x y : SixE6) :
    s1611e3_sixE6Nat (x * y) = s1611e3_sixE6Nat x ^^^ s1611e3_sixE6Nat y := by
  revert x y
  decide +kernel

theorem s1611e3_sixE6Nat_one : s1611e3_sixE6Nat 1 = 0 := by
  decide +kernel

@[expose] def s1611e3_sixVNat (u : SixE6 × SixE6) : ℕ :=
  s1611e3_sixE6Nat u.1 + 64 * s1611e3_sixE6Nat u.2

theorem s1611e3_sixVNat_lt (u : SixE6 × SixE6) : s1611e3_sixVNat u < 4096 := by
  revert u
  decide +kernel

theorem s1611e3_sixVNat_injective : Function.Injective s1611e3_sixVNat := by
  intro u v h
  have hu1 : (s1611e3_sixE6Nat u.1 + 64 * s1611e3_sixE6Nat u.2) % 64 =
      s1611e3_sixE6Nat u.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (s1611e3_sixE6Nat_lt u.1)]
  have hv1 : (s1611e3_sixE6Nat v.1 + 64 * s1611e3_sixE6Nat v.2) % 64 =
      s1611e3_sixE6Nat v.1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (s1611e3_sixE6Nat_lt v.1)]
  have hu2 : (s1611e3_sixE6Nat u.1 + 64 * s1611e3_sixE6Nat u.2) / 64 =
      s1611e3_sixE6Nat u.2 := by
    rw [Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 64),
      Nat.div_eq_of_lt (s1611e3_sixE6Nat_lt u.1), zero_add]
  have hv2 : (s1611e3_sixE6Nat v.1 + 64 * s1611e3_sixE6Nat v.2) / 64 =
      s1611e3_sixE6Nat v.2 := by
    rw [Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 64),
      Nat.div_eq_of_lt (s1611e3_sixE6Nat_lt v.1), zero_add]
  have h1 : s1611e3_sixE6Nat u.1 = s1611e3_sixE6Nat v.1 := by
    have hh := congrArg (fun n => n % 64) h
    simp only [s1611e3_sixVNat] at hh
    rwa [hu1, hv1] at hh
  have h2 : s1611e3_sixE6Nat u.2 = s1611e3_sixE6Nat v.2 := by
    have hh := congrArg (fun n => n / 64) h
    simp only [s1611e3_sixVNat] at hh
    rwa [hu2, hv2] at hh
  exact Prod.ext (s1611e3_sixE6Nat_injective h1) (s1611e3_sixE6Nat_injective h2)

private theorem s1611e3_testBit_add_mul_two_pow (x y k : ℕ) (hx : x < 64) :
    (x + 64 * y).testBit k = if k < 6 then x.testBit k else y.testBit (k - 6) := by
  have hx' : x < 2 ^ 6 := by norm_num at hx ⊢; exact hx
  rw [show x + 64 * y = 2 ^ 6 * y + x by ring,
    Nat.testBit_two_pow_mul_add y hx' k]

theorem s1611e3_xor_add (a b c d : ℕ) (ha : a < 64) (hc : c < 64) :
    (a + 64 * b) ^^^ (c + 64 * d) = (a ^^^ c) + 64 * (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, s1611e3_testBit_add_mul_two_pow a b k ha,
    s1611e3_testBit_add_mul_two_pow c d k hc,
    s1611e3_testBit_add_mul_two_pow (a ^^^ c) (b ^^^ d) k
      (Nat.xor_lt_two_pow (n := 6) (by rw [show (2:ℕ)^6 = 64 by norm_num]; exact ha)
        (by rw [show (2:ℕ)^6 = 64 by norm_num]; exact hc))]
  by_cases hk : k < 6 <;> simp [hk, Nat.testBit_xor]

theorem s1611e3_sixVNat_mul (u v : SixE6 × SixE6) :
    s1611e3_sixVNat (u * v) = s1611e3_sixVNat u ^^^ s1611e3_sixVNat v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [s1611e3_sixVNat, Prod.fst_mul, Prod.snd_mul, s1611e3_sixE6Nat_add]
  exact (s1611e3_xor_add (s1611e3_sixE6Nat u1) (s1611e3_sixE6Nat u2)
    (s1611e3_sixE6Nat v1) (s1611e3_sixE6Nat v2)
    (s1611e3_sixE6Nat_lt u1) (s1611e3_sixE6Nat_lt v1)).symm

structure s1611e3_SixCode where
  sigma : Perm (Fin 6)
  tau : Perm (Fin 6)
  eps : Bool

instance s1611e3_SixCode.instDecidableEq : DecidableEq s1611e3_SixCode := fun c d =>
  if h : c.sigma = d.sigma ∧ c.tau = d.tau ∧ c.eps = d.eps then
    isTrue (by
      obtain ⟨σ, τ, ε⟩ := c
      obtain ⟨σ', τ', ε'⟩ := d
      obtain ⟨h1, h2, h3⟩ := h
      simp only at h1 h2 h3
      subst h1 h2 h3
      rfl)
  else
    isFalse (fun e => h (by subst e; exact ⟨rfl, rfl, rfl⟩))

@[expose] def s1611e3_sixCodeMul (c d : s1611e3_SixCode) : s1611e3_SixCode :=
  if c.eps then
    if d.eps then ⟨c.tau * d.sigma, c.sigma * d.tau, false⟩
    else ⟨c.sigma * d.sigma, c.tau * d.tau, true⟩
  else
    if d.eps then ⟨c.tau * d.sigma, c.sigma * d.tau, true⟩
    else ⟨c.sigma * d.sigma, c.tau * d.tau, false⟩

@[expose] def s1611e3_sixCodeOne : s1611e3_SixCode := ⟨1, 1, false⟩

@[expose] def s1611e3_sixCodeInv (c : s1611e3_SixCode) : s1611e3_SixCode :=
  if c.eps then ⟨c.tau⁻¹, c.sigma⁻¹, true⟩ else ⟨c.sigma⁻¹, c.tau⁻¹, false⟩

@[expose] def s1611e3_sixCodeValid (c : s1611e3_SixCode) : Prop := c.tau = sixAlpha c.sigma

@[expose] def s1611e3_sixGhatOf (c : s1611e3_SixCode) : MulAut (SixE6 × SixE6) :=
  if c.eps then sixSwap * sixRho c.sigma else sixRho c.sigma

@[expose] def s1611e3_sixCodeAct (c : s1611e3_SixCode) (m : ℕ) : ℕ :=
  if c.eps then
    s1611e3_sixBitAct c.tau (m >>> 6) + 64 * s1611e3_sixBitAct c.sigma (m &&& 63)
  else
    s1611e3_sixBitAct c.sigma (m &&& 63) + 64 * s1611e3_sixBitAct c.tau (m >>> 6)

private theorem s1611e3_sixSwap_mul_rho (σ : Perm (Fin 6)) :
    sixSwap * sixRho σ = sixRho (sixAlpha σ) * sixSwap := by
  have h := sixSwap_conj_rho σ
  rw [← h]
  group

private theorem s1611e3_sixRho_mul_swap (σ : Perm (Fin 6)) :
    sixRho σ * sixSwap = sixSwap * sixRho (sixAlpha σ) := by
  have h := s1611e3_sixSwap_mul_rho (sixAlpha σ)
  rw [sixAlpha_sixAlpha] at h
  exact h.symm

theorem s1611e3_sixCodeValid_mul {c d : s1611e3_SixCode}
    (hc : s1611e3_sixCodeValid c) (hd : s1611e3_sixCodeValid d) :
    s1611e3_sixCodeValid (s1611e3_sixCodeMul c d) := by
  obtain ⟨σ1, τ1, ε1⟩ := c
  obtain ⟨σ2, τ2, ε2⟩ := d
  simp only [s1611e3_sixCodeValid] at hc hd
  rw [show τ1 = sixAlpha σ1 from hc, show τ2 = sixAlpha σ2 from hd]
  cases ε1 <;> cases ε2 <;>
    simp only [s1611e3_sixCodeMul, s1611e3_sixCodeValid, Bool.false_eq_true, if_true, if_false,
      reduceIte, map_mul, sixAlpha_sixAlpha]

theorem s1611e3_sixGhatOf_mul {c d : s1611e3_SixCode}
    (hc : s1611e3_sixCodeValid c) (hd : s1611e3_sixCodeValid d) :
    s1611e3_sixGhatOf (s1611e3_sixCodeMul c d) =
      s1611e3_sixGhatOf c * s1611e3_sixGhatOf d := by
  obtain ⟨σ1, τ1, ε1⟩ := c
  obtain ⟨σ2, τ2, ε2⟩ := d
  simp only [s1611e3_sixCodeValid] at hc hd
  rw [show τ1 = sixAlpha σ1 from hc, show τ2 = sixAlpha σ2 from hd]
  cases ε1 <;> cases ε2 <;>
    simp only [s1611e3_sixCodeMul, s1611e3_sixGhatOf, Bool.false_eq_true, if_true, if_false,
      reduceIte]
  · exact map_mul sixRho σ1 σ2
  · rw [← mul_assoc, s1611e3_sixRho_mul_swap, mul_assoc, ← map_mul]
  · rw [mul_assoc, ← map_mul]
  · have h := s1611e3_sixSwap_mul_rho σ1
    have h2 : (sixSwap : MulAut (SixE6 × SixE6)) * sixSwap = 1 := sixSwap_mul_self
    rw [map_mul, h, mul_assoc]
    congr 1

theorem s1611e3_sixCodeValid_inv {c : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c) :
    s1611e3_sixCodeValid (s1611e3_sixCodeInv c) := by
  obtain ⟨σ, τ, ε⟩ := c
  simp only [s1611e3_sixCodeValid] at hc
  rw [show τ = sixAlpha σ from hc]
  cases ε <;>
    simp only [s1611e3_sixCodeInv, s1611e3_sixCodeValid, Bool.false_eq_true, if_true, if_false,
      reduceIte, map_inv, sixAlpha_sixAlpha]

theorem s1611e3_sixGhatOf_inv {c : s1611e3_SixCode} (hc : s1611e3_sixCodeValid c) :
    s1611e3_sixGhatOf (s1611e3_sixCodeInv c) = (s1611e3_sixGhatOf c)⁻¹ := by
  obtain ⟨σ, τ, ε⟩ := c
  simp only [s1611e3_sixCodeValid] at hc
  rw [show τ = sixAlpha σ from hc]
  cases ε
  · simp only [s1611e3_sixCodeInv, s1611e3_sixGhatOf, Bool.false_eq_true, if_false, reduceIte]
    rw [map_inv]
  · simp only [s1611e3_sixCodeInv, s1611e3_sixGhatOf, Bool.false_eq_true, if_false, if_true,
      reduceIte]
    rw [mul_inv_rev,
      show sixSwap⁻¹ = sixSwap from inv_eq_of_mul_eq_one_right sixSwap_mul_self,
      show (sixRho σ)⁻¹ = sixRho σ⁻¹ from (map_inv sixRho σ).symm,
      s1611e3_sixRho_mul_swap,
      show sixAlpha σ⁻¹ = (sixAlpha σ)⁻¹ from map_inv sixAlpha σ]

@[expose] def s1611e3_sixGhatSub : Subgroup (MulAut (SixE6 × SixE6)) where
  carrier := {a | ∃ c : s1611e3_SixCode, s1611e3_sixCodeValid c ∧ s1611e3_sixGhatOf c = a}
  one_mem' := ⟨⟨1, 1, false⟩, by simp [s1611e3_sixCodeValid], by simp [s1611e3_sixGhatOf]⟩
  mul_mem' := by
    rintro a b ⟨ca, hca, rfl⟩ ⟨cb, hcb, rfl⟩
    exact ⟨s1611e3_sixCodeMul ca cb, s1611e3_sixCodeValid_mul hca hcb,
      s1611e3_sixGhatOf_mul hca hcb⟩
  inv_mem' := by
    rintro a ⟨ca, hca, rfl⟩
    exact ⟨s1611e3_sixCodeInv ca, s1611e3_sixCodeValid_inv hca,
      s1611e3_sixGhatOf_inv hca⟩

theorem s1611e3_sixGhat_eq_sub : sixGhat = s1611e3_sixGhatSub := by
  apply le_antisymm
  · rw [sixGhat, Subgroup.closure_le]
    rintro a (ha | rfl)
    · obtain ⟨σ, rfl⟩ := ha
      exact ⟨⟨σ, sixAlpha σ, false⟩, rfl, rfl⟩
    · exact ⟨⟨1, sixAlpha 1, true⟩, rfl, by simp [s1611e3_sixGhatOf]⟩
  · rintro a ⟨c, -, rfl⟩
    cases c with
    | mk σ τ ε =>
      cases ε
      · exact Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
          (Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩))

theorem s1611e3_sixGhatOf_surjective : ∀ a ∈ sixGhat, ∃ c : s1611e3_SixCode,
    s1611e3_sixCodeValid c ∧ s1611e3_sixGhatOf c = a := by
  intro a ha
  have : a ∈ s1611e3_sixGhatSub := by rwa [← s1611e3_sixGhat_eq_sub]
  exact this

theorem s1611e3_sixVNat_act (c : s1611e3_SixCode) (u : SixE6 × SixE6)
    (hc : s1611e3_sixCodeValid c) :
    s1611e3_sixVNat (s1611e3_sixGhatOf c u) = s1611e3_sixCodeAct c (s1611e3_sixVNat u) := by
  obtain ⟨σ, τ, ε⟩ := c
  simp only [s1611e3_sixCodeValid] at hc
  rw [show τ = sixAlpha σ from hc]
  obtain ⟨u1, u2⟩ := u
  have hsig : s1611e3_sixE6Nat u1 < 64 := s1611e3_sixE6Nat_lt u1
  have h1 : (s1611e3_sixE6Nat u1 + 64 * s1611e3_sixE6Nat u2) &&& 63 = s1611e3_sixE6Nat u1 := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsig]
  have h2 : (s1611e3_sixE6Nat u1 + 64 * s1611e3_sixE6Nat u2) >>> 6 = s1611e3_sixE6Nat u2 := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 6 = 64 by norm_num,
      Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 64), Nat.div_eq_of_lt hsig, zero_add]
  have hrho : (sixRho σ) (u1, u2) =
      ((coreAct 6 σ) u1, (coreAct 6 (sixAlpha σ)) u2) := rfl
  cases ε
  · simp only [s1611e3_sixGhatOf, s1611e3_sixCodeAct, s1611e3_sixVNat, Bool.false_eq_true,
      if_false, reduceIte, h1, h2]
    rw [hrho, s1611e3_sixE6Nat_coreAct, s1611e3_sixE6Nat_coreAct]
  · simp only [s1611e3_sixGhatOf, s1611e3_sixCodeAct, s1611e3_sixVNat, Bool.false_eq_true,
      if_true, reduceIte, h1, h2]
    rw [show (sixSwap * sixRho σ) (u1, u2) =
        ((coreAct 6 (sixAlpha σ)) u2, (coreAct 6 σ) u1) from rfl]
    show s1611e3_sixE6Nat ((coreAct 6 (sixAlpha σ)) u2) +
        64 * s1611e3_sixE6Nat ((coreAct 6 σ) u1) =
      s1611e3_sixBitAct (sixAlpha σ) (s1611e3_sixE6Nat u2) +
        64 * s1611e3_sixBitAct σ (s1611e3_sixE6Nat u1)
    rw [s1611e3_sixE6Nat_coreAct, s1611e3_sixE6Nat_coreAct]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
