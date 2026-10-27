module

public import Certificates.Certificate43
public import Mathlib.Basic.Finite.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.Asc72WreathDefs
public import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

theorem pow_sub_one_ne {Y n : ℕ} (hY : 2 ≤ Y) (hn : n = 3 ∨ n = 4) :
    (Y ^ 2 - 1) ^ n ≠ (Y ^ n - 1) ^ 2 := by
  have hY1 : 1 ≤ Y ^ 2 := Nat.one_le_pow 2 Y (by omega)
  have hYn : 1 ≤ Y ^ n := Nat.one_le_pow n Y (by omega)
  intro h
  have hz : ((Y : ℤ) ^ 2 - 1) ^ n = ((Y : ℤ) ^ n - 1) ^ 2 := by
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hY1, Nat.cast_sub hYn, Nat.cast_one] at h'
    push_cast at h'
    exact h'
  have hY' : (2 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  rcases hn with rfl | rfl
  ·
    ring_nf at hz
    have hfac : 3 * (Y : ℤ) ^ 4 - 2 * (Y : ℤ) ^ 3 - 3 * (Y : ℤ) ^ 2 + 2
        = ((Y : ℤ) - 1) ^ 2 * (3 * (Y : ℤ) ^ 2 + 4 * (Y : ℤ) + 2) := by ring
    have hpos1 : 0 < ((Y : ℤ) - 1) ^ 2 := by
      rw [sq]
      exact mul_pos (by linarith) (by linarith)
    have hpos2 : 0 < 3 * (Y : ℤ) ^ 2 + 4 * (Y : ℤ) + 2 := by
      nlinarith [sq_nonneg (Y : ℤ)]
    have hpos : 0 < 3 * (Y : ℤ) ^ 4 - 2 * (Y : ℤ) ^ 3 - 3 * (Y : ℤ) ^ 2 + 2 := by
      rw [hfac]
      exact mul_pos hpos1 hpos2
    nlinarith
  ·
    ring_nf at hz
    have hfac : 4 * (Y : ℤ) ^ 2 * ((Y : ℤ) ^ 2 - 1) ^ 2
        = ((Y : ℤ) ^ 4 - 1) ^ 2 - ((Y : ℤ) ^ 2 - 1) ^ 4 := by ring
    have hpos1 : 0 < (Y : ℤ) ^ 2 := by positivity
    have hpos2 : 0 < ((Y : ℤ) ^ 2 - 1) ^ 2 := by
      rw [sq]
      exact mul_pos (by nlinarith) (by nlinarith)
    have hpos : 0 < 4 * (Y : ℤ) ^ 2 * ((Y : ℤ) ^ 2 - 1) ^ 2 := by
      have : 0 < 4 * (Y : ℤ) ^ 2 := by positivity
      exact mul_pos this hpos2
    nlinarith

theorem padicValNat_two_pow_mul_sq_sub_one {k : ℕ} (hk : 1 ≤ k) :
    padicValNat 2 (2 ^ k * ((2 ^ k) ^ 2 - 1)) = k := by
  have hk0 : k ≠ 0 := by omega
  have h2 : 2 ≤ 2 ^ k := by
    have h : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_of_le (by norm_num : 1 < 2) hk
    simpa using h
  have hpos : 0 < (2 ^ k) ^ 2 - 1 := by
    apply Nat.sub_pos_of_lt
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left h2 2
  have hodd : Odd ((2 ^ k) ^ 2 - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow 2 _ (by omega)) ?_ (by norm_num : Odd 1)
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hk0⟩, by norm_num⟩
  have hval : padicValNat 2 ((2 ^ k) ^ 2 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat
  rw [padicValNat_base_pow_mul (p := 2) (n := (2 ^ k) ^ 2 - 1) (by norm_num : 1 < 2)
    hpos.ne' k, hval]
  omega

theorem two_pow_mul_sq_sub_one_pow_ne {f f' n : ℕ} (hf : 2 ≤ f) (hf' : 2 ≤ f')
    (hn : n = 3 ∨ n = 4) :
    (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ n ≠
      (2 ^ f' * ((2 ^ f') ^ 2 - 1)) ^ 2 := by
  intro h
  have hf1 : 1 ≤ f := by omega
  have hf'1 : 1 ≤ f' := by omega
  have hvalA := padicValNat_two_pow_mul_sq_sub_one (k := f) hf1
  have hvalB := padicValNat_two_pow_mul_sq_sub_one (k := f') hf'1
  have hexp : n * f = 2 * f' := by
    have h2 := congrArg (fun x : ℕ => padicValNat 2 x) h
    rw [padicValNat.pow, padicValNat.pow, hvalA, hvalB] at h2
    exact h2
  have hYpow : (2 ^ f) ^ n = (2 ^ f') ^ 2 := by
    have hmn : f * n = f' * 2 := by
      rw [Nat.mul_comm f n, hexp, Nat.mul_comm]
    rw [← pow_mul, ← pow_mul, hmn]
  have hAB : ((2 ^ f) ^ 2 - 1) ^ n = ((2 ^ f') ^ 2 - 1) ^ 2 := by
    have h1 : (2 ^ f) ^ n * ((2 ^ f) ^ 2 - 1) ^ n =
        (2 ^ f') ^ 2 * ((2 ^ f') ^ 2 - 1) ^ 2 := by
      rw [← mul_pow, ← mul_pow]
      exact h
    rw [hYpow] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos (by norm_num) f') 2) h1
  have hfin : ((2 ^ f) ^ 2 - 1) ^ n = (((2 ^ f) ^ n) - 1) ^ 2 := by
    rw [hYpow]
    exact hAB
  have h2f : 2 ≤ 2 ^ f := by
    have h : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_of_le (by norm_num : 1 < 2) hf
    calc 2 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := h
  exact pow_sub_one_ne (Y := 2 ^ f) (n := n) h2f hn hfin

theorem two_lt_r_of_l2Wreath {X : Type} [Group X] [Finite X]
    {D : Set X} (hS : Setup X D) {f n : ℕ} (hf : 2 ≤ f) (hn : n = 3 ∨ n = 4)
    (e : X ≃* L2Wreath f n) (W : WreathData X D ((l2WreathBase f n).comap e.toMonoidHom)) :
    2 < W.r := by
  classical
  by_contra hle
  push Not at hle
  let M : Subgroup X := (l2WreathBase f n).comap e.toMonoidHom
  obtain ⟨f', hf', ⟨eS⟩⟩ := wreathData_factor_psl2 hS W ⟨0, by have := W.two_le; omega⟩
  rcases W with ⟨r, hr2, S, hsimple, hnotcomm, hleM, eW, he_single, π, hconj, htrans, hswap⟩
  have hr : r = 2 := le_antisymm hle hr2
  subst hr
  have hcardM1 : Nat.card M = Nat.card (PSL2Model f) ^ n := by
    have hmap : M.map e.toMonoidHom = l2WreathBase f n :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective (l2WreathBase f n)
    have he : M ≃* l2WreathBase f n := by
      have h := Subgroup.equivMapOfInjective M e.toMonoidHom e.injective
      rwa [hmap] at h
    rw [Nat.card_congr he.toEquiv, CFSG.OddTranspositions.PartThree.card_l2WreathBase]
  have hcardM2 : Nat.card M = Nat.card (S 0) * Nat.card (S 1) := by
    rw [← Nat.card_congr eW.toEquiv,
      Nat.card_congr (piFinTwoEquiv (fun i : Fin 2 => ↥(S i))), Nat.card_prod]
  have hcardS : Nat.card (S 0) = Nat.card (S 1) := by
    obtain ⟨g, hg⟩ := htrans 0 1
    have hmap : (S 0).map (MulAut.conj g).toMonoidHom = S 1 := by
      rw [hconj g 0, hg]
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hS0 : Nat.card (S 0) = Nat.card (PSL2Model f') := Nat.card_congr eS.toEquiv
  have hS1 : Nat.card (S 1) = Nat.card (PSL2Model f') := hcardS ▸ hS0
  have hcardPS : Nat.card (PSL2Model f) ^ n = Nat.card (PSL2Model f') ^ 2 := by
    rw [← hcardM1, hcardM2, hS0, hS1, pow_two]
  have hcardNat : (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ n =
      (2 ^ f' * ((2 ^ f') ^ 2 - 1)) ^ 2 := by
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (show 1 ≤ f by omega),
      CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (show 1 ≤ f' by omega)] at hcardPS
    exact hcardPS
  exact two_pow_mul_sq_sub_one_pow_ne hf hf' hn hcardNat

end CFSG.OddTranspositions.PartThree.EightSix
