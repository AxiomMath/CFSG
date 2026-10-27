module

public import Mathlib.Combinatorics.Colex
public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCDefs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ReeB2Fixed

@[expose] def r (e : ℕ) : ZMod (2 ^ e - 1) := 2 ^ ((e + 1) / 2)

@[expose] def sig (e : ℕ) [NeZero e] (k : Fin e) : Fin e :=
  ⟨(k : ℕ) * ((e + 1) / 2) % e, Nat.mod_lt _ (NeZero.pos e)⟩

private theorem two_mul_half (e : ℕ) (he : Odd e) : ((e + 1) / 2) * 2 = e + 1 := by
  obtain ⟨m, hm⟩ := he
  rw [hm]
  omega

private theorem two_pow_e_eq_one (e : ℕ) (he : Odd e) : (2 : ZMod (2 ^ e - 1)) ^ e = 1 := by
  have hle : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  calc (2 : ZMod (2 ^ e - 1)) ^ e = ((2 ^ e : ℕ) : ZMod (2 ^ e - 1)) := by
        push_cast
        ring
    _ = (((2 ^ e - 1 : ℕ)) : ZMod (2 ^ e - 1)) + 1 := by
        rw [← Nat.sub_add_cancel hle]
        push_cast
        ring
    _ = 1 := by
        rw [ZMod.natCast_self]
        ring

private theorem sum_range_two_pow (e : ℕ) :
    ∑ i ∈ Finset.range e, 2 ^ i = 2 ^ e - 1 := by
  rw [Nat.geomSum_eq (by omega : 2 ≤ 2) e]
  simp

private theorem bijective_add_two (e : ℕ) [NeZero e] :
    Function.Bijective (fun k : Fin e => k + 2) := by
  apply Function.Injective.bijective_of_finite
  intro a b hab
  exact add_right_cancel hab

theorem r_sq (e : ℕ) (he : Odd e) : r e ^ 2 = 2 := by
  have hh := two_mul_half e he
  have h2 := two_pow_e_eq_one e he
  calc r e ^ 2 = (2 ^ ((e + 1) / 2)) ^ 2 := rfl
    _ = 2 ^ (((e + 1) / 2) * 2) := by rw [pow_mul]
    _ = 2 ^ (e + 1) := by rw [hh]
    _ = 2 ^ e * 2 := by rw [pow_succ]
    _ = 1 * 2 := by rw [h2]
    _ = 2 := by ring

theorem r_pow_self (e : ℕ) (he : Odd e) : r e ^ e = 1 := by
  have h2 := two_pow_e_eq_one e he
  calc r e ^ e = (2 ^ ((e + 1) / 2)) ^ e := rfl
    _ = 2 ^ (((e + 1) / 2) * e) := by rw [pow_mul]
    _ = 2 ^ (e * ((e + 1) / 2)) := by rw [Nat.mul_comm ((e + 1) / 2) e]
    _ = (2 ^ e) ^ ((e + 1) / 2) := by rw [pow_mul]
    _ = 1 := by rw [h2, one_pow]

theorem r_pow_eq (e : ℕ) (he : Odd e) [NeZero e] (k : Fin e) : r e ^ (k : ℕ) = 2 ^ (sig e k : ℕ) := by
  have h2 := two_pow_e_eq_one e he
  calc r e ^ (k : ℕ) = (2 ^ ((e + 1) / 2)) ^ (k : ℕ) := rfl
    _ = 2 ^ (((e + 1) / 2) * (k : ℕ)) := by rw [pow_mul]
    _ = 2 ^ ((k : ℕ) * ((e + 1) / 2)) := by rw [Nat.mul_comm ((e + 1) / 2) (k : ℕ)]
    _ = 2 ^ (((k : ℕ) * ((e + 1) / 2)) % e) := pow_eq_pow_mod _ h2
    _ = 2 ^ (sig e k : ℕ) := rfl

private theorem r_pow_add_two (e : ℕ) (he : Odd e) [NeZero e] (j : Fin e) :
    r e ^ ((j + 2 : Fin e) : ℕ) = 2 * r e ^ (j : ℕ) := by
  have hmod : ((j + 2 : Fin e) : ℕ) % e = ((j : ℕ) + 2) % e := by
    rw [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.mod_mod, Nat.add_mod_mod]
  have hpow : r e ^ ((j + 2 : Fin e) : ℕ) = r e ^ ((j : ℕ) + 2) := by
    rw [pow_eq_pow_mod ((j + 2 : Fin e) : ℕ) (r_pow_self e he),
      pow_eq_pow_mod ((j : ℕ) + 2) (r_pow_self e he), hmod]
  rw [hpow, pow_add, r_sq e he]
  ring

theorem sig_add_one (e : ℕ) (he : Odd e) [NeZero e] (k : Fin e) :
    sig e (k + 1) = succσ e (sig e k) := by
  apply Fin.ext
  simp only [sig, succσ, Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod,
    Nat.mod_mul_mod, Nat.mod_add_mod]
  congr 1
  ring

theorem sig_bijective (e : ℕ) (he : Odd e) [NeZero e] : Function.Bijective (sig e) := by
  apply Function.Injective.bijective_of_finite
  intro k k' hkk
  have hval : (k : ℕ) * ((e + 1) / 2) % e = (k' : ℕ) * ((e + 1) / 2) % e :=
    congrArg Fin.val hkk
  have hmod : (k : ℕ) * ((e + 1) / 2) ≡ (k' : ℕ) * ((e + 1) / 2) [MOD e] := hval
  have hh : ((e + 1) / 2) * 2 = e + 1 := two_mul_half e he
  have hmul : (k : ℕ) * ((e + 1) / 2) * 2 ≡ (k' : ℕ) * ((e + 1) / 2) * 2 [MOD e] :=
    hmod.mul_right 2
  have hleft : (k : ℕ) * ((e + 1) / 2) * 2 = (k : ℕ) * (e + 1) := by rw [mul_assoc, hh]
  have hright : (k' : ℕ) * ((e + 1) / 2) * 2 = (k' : ℕ) * (e + 1) := by rw [mul_assoc, hh]
  rw [hleft, hright] at hmul
  have hk : (k : ℕ) * (e + 1) ≡ (k : ℕ) [MOD e] := by
    have : (k : ℕ) * (e + 1) = e * (k : ℕ) + (k : ℕ) := by ring
    rw [this]
    exact Nat.ModEq.modulus_mul_add
  have hk' : (k' : ℕ) * (e + 1) ≡ (k' : ℕ) [MOD e] := by
    have : (k' : ℕ) * (e + 1) = e * (k' : ℕ) + (k' : ℕ) := by ring
    rw [this]
    exact Nat.ModEq.modulus_mul_add
  have hfin : (k : ℕ) ≡ (k' : ℕ) [MOD e] := hk.symm.trans (hmul.trans hk')
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hfin k.isLt k'.isLt)

theorem sum_eq_zero_of_carries (e : ℕ) (he : Odd e) [NeZero e] (z c : Fin e → ℤ)
    (h : ∀ k, z k + c (k - 2) = 2 * c k) :
    ∑ k, (z k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) = 0 := by
  have hz (k : Fin e) : (z k : ZMod (2 ^ e - 1)) =
      2 * (c k : ZMod (2 ^ e - 1)) - (c (k - 2) : ZMod (2 ^ e - 1)) := by
    have hk := congrArg (fun x : ℤ => (x : ZMod (2 ^ e - 1))) (h k)
    push_cast at hk
    rw [eq_sub_iff_add_eq]
    exact hk
  have hreindex : ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) =
      2 * ∑ k, (c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
    have h1 : ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) =
        ∑ j, (c j : ZMod (2 ^ e - 1)) * r e ^ ((j + 2 : Fin e) : ℕ) := by
      have hcomp := Equiv.sum_comp
        (Equiv.ofBijective (fun j : Fin e => j + 2) (bijective_add_two e))
        (fun k : Fin e => (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ))
      have : ∑ j, (c j : ZMod (2 ^ e - 1)) * r e ^ ((j + 2 : Fin e) : ℕ) =
          ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
        simpa [add_sub_cancel_right] using hcomp
      exact this.symm
    calc ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)
        = ∑ j, (c j : ZMod (2 ^ e - 1)) * r e ^ ((j + 2 : Fin e) : ℕ) := h1
      _ = ∑ j, 2 * ((c j : ZMod (2 ^ e - 1)) * r e ^ (j : ℕ)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [r_pow_add_two e he j]
            ring
      _ = 2 * ∑ j, (c j : ZMod (2 ^ e - 1)) * r e ^ (j : ℕ) := by
            rw [Finset.mul_sum]
  calc ∑ k, (z k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)
      = ∑ k, (2 * (c k : ZMod (2 ^ e - 1))
          - (c (k - 2) : ZMod (2 ^ e - 1))) * r e ^ (k : ℕ) :=
          Finset.sum_congr rfl (fun k _ => by rw [hz k])
    _ = ∑ k, (2 * ((c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ))
          - (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k, 2 * ((c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)))
          - ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
          rw [Finset.sum_sub_distrib]
    _ = 2 * ∑ k, (c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)
          - ∑ k, (c (k - 2) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
          rw [Finset.mul_sum]
    _ = 2 * ∑ k, (c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)
          - 2 * ∑ k, (c k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
          rw [hreindex]
    _ = 0 := by ring

theorem sum_digits_eq (e : ℕ) (he : Odd e) [NeZero e] (y d c : Fin e → ℤ)
    (h : ∀ k, y k + c (k - 2) = d k + 2 * c k) :
    ∑ k, (d k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) =
      ∑ k, (y k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
  have hz : ∀ k, (y k - d k) + c (k - 2) = 2 * c k := by
    intro k
    have hk := h k
    linarith
  have hzero := sum_eq_zero_of_carries e he (fun k => y k - d k) c hz
  have hcast : ∀ k, (((y k - d k : ℤ)) : ZMod (2 ^ e - 1)) =
      (y k : ZMod (2 ^ e - 1)) - (d k : ZMod (2 ^ e - 1)) := by
    intro k
    push_cast
    ring
  have hsub : ∑ k, ((y k : ZMod (2 ^ e - 1)) - (d k : ZMod (2 ^ e - 1)))
      * r e ^ (k : ℕ) = 0 := by
    simpa only [hcast] using hzero
  have hsplit : ∑ k, ((y k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)
      - (d k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ)) = 0 := by
    rw [← hsub]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [Finset.sum_sub_distrib] at hsplit
  exact (sub_eq_zero.mp hsplit).symm

theorem digits_eq_of_sum (e : ℕ) (he : Odd e) [NeZero e] (D : Finset (Fin e)) (x : ZMod (2 ^ e - 1))
    (hx : x ≠ 0) (hD : x = ∑ k ∈ D, r e ^ (k : ℕ)) :
    digits e x = D.map ⟨sig e, (sig_bijective e he).1⟩ := by
  let emb2 : Fin e ↪ ℕ := ⟨fun j => (j : ℕ), by intro a b hab; exact Fin.ext hab⟩
  let D' : Finset (Fin e) := D.map ⟨sig e, (sig_bijective e he).1⟩
  let D'' : Finset ℕ := D'.map emb2
  let n : ℕ := ∑ j ∈ D', 2 ^ (j : ℕ)
  have hsum : x = ∑ j ∈ D', 2 ^ (j : ℕ) := by
    have hrw : ∑ k ∈ D, r e ^ (k : ℕ) = ∑ k ∈ D, 2 ^ (sig e k : ℕ) :=
      Finset.sum_congr rfl (fun k _ => r_pow_eq e he k)
    have hmap : ∑ k ∈ D, (2 : ZMod (2 ^ e - 1)) ^ (sig e k : ℕ) = ∑ j ∈ D', 2 ^ (j : ℕ) := by
      have := Finset.sum_map D ⟨sig e, (sig_bijective e he).1⟩
        (fun j : Fin e => (2 : ZMod (2 ^ e - 1)) ^ (j : ℕ))
      simpa [D'] using this.symm
    calc x = ∑ k ∈ D, r e ^ (k : ℕ) := hD
      _ = ∑ k ∈ D, 2 ^ (sig e k : ℕ) := hrw
      _ = ∑ j ∈ D', 2 ^ (j : ℕ) := hmap
  have hn : n = ∑ i ∈ D'', 2 ^ i := by
    rw [show n = ∑ j ∈ D', 2 ^ (j : ℕ) from rfl]
    exact (Finset.sum_map D' emb2 (fun i : ℕ => 2 ^ i)).symm
  have hxn : x = (n : ZMod (2 ^ e - 1)) := by
    rw [hsum]
    rw [show n = ∑ j ∈ D', 2 ^ (j : ℕ) from rfl]
    push_cast
    rfl
  have hsubD : D'' ⊆ Finset.range e := by
    intro i hi
    simp only [D'', emb2, Finset.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Finset.mem_range.mpr j.isLt
  have hle : n ≤ 2 ^ e - 1 := by
    have h1 : ∑ i ∈ D'', 2 ^ i ≤ ∑ i ∈ Finset.range e, 2 ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubD (fun i _ _ => by positivity)
    have h2 : ∑ i ∈ Finset.range e, 2 ^ i = 2 ^ e - 1 := sum_range_two_pow e
    rw [hn]
    exact h1.trans_eq h2
  have hn_ne : n ≠ 2 ^ e - 1 := by
    intro hn_eq
    apply hx
    rw [hxn, hn_eq]
    exact ZMod.natCast_self _
  have hn_lt : n < 2 ^ e - 1 := lt_of_le_of_ne hle hn_ne
  have hxval : x.val = n := by rw [hxn, ZMod.val_natCast_of_lt hn_lt]
  have hbits : n.bitIndices.toFinset = D'' := by
    rw [hn]
    exact Finset.toFinset_bitIndices_sum_two_pow D''
  have hbit (j : Fin e) : x.val.testBit j ↔ j ∈ D' := by
    rw [hxval, ← Nat.mem_bitIndices, ← List.mem_toFinset, hbits]
    simp only [D'', emb2, Finset.mem_map]
    constructor
    · rintro ⟨i, hi, hji⟩
      have hji' : i = j := Fin.ext hji
      simpa [hji'] using hi
    · intro hj
      exact ⟨j, hj, rfl⟩
  apply Finset.ext
  intro j
  simp only [digits, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hbit j

end CFSG.StandardType.ReeB2Fixed
