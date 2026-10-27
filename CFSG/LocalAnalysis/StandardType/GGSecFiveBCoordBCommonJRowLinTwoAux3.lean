module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGHalfCentSupp
import CFSG.LocalAnalysis.StandardType.GGHalfCentralizer
import CFSG.LocalAnalysis.StandardType.GGHalfNumberTheory
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL
import CFSG.Mathlib.GroupTheory.ConjCentralizer
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

public section

namespace CFSG.StandardType.CommonJRowLinTwo

open CFSG.Assembly
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf

private lemma natCard_f2 : Nat.card F2 = 2 := by
  simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)

private lemma natCard_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by omega)]
  norm_num

private lemma padicValNat_three_factorial_succ (n : ℕ) :
    padicValNat 3 (n + 1).factorial = padicValNat 3 (n + 1) + padicValNat 3 n.factorial := by
  rw [Nat.factorial_succ]
  exact padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)

private lemma padicValNat_three_factorial_mono (n : ℕ) :
    n + padicValNat 3 n.factorial ≤ (n + 1) + padicValNat 3 (n + 1).factorial := by
  rw [padicValNat_three_factorial_succ]
  omega

private lemma padicValNat_three_factorial_mono_le {n m : ℕ} (h : n ≤ m) :
    n + padicValNat 3 n.factorial ≤ m + padicValNat 3 m.factorial := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (padicValNat_three_factorial_mono _)

private lemma padicValNat_three_factorial_sub_two {k : ℕ} (hk : 2 ≤ k) :
    (k - 2) + padicValNat 3 (k - 2).factorial + 2 ≤ k + padicValNat 3 k.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 2 = m from by omega]
  have h2 : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [h2, padicValNat.mul (by omega : m + 2 ≠ 0)
      (by positivity : ((m + 1) * m.factorial) ≠ 0),
    padicValNat.mul (by omega : m + 1 ≠ 0) (Nat.factorial_ne_zero m)]
  omega

private lemma not_three_dvd_two_pow_odd (t : ℕ) : ¬ 3 ∣ 2 ^ (t + t + 1) - 1 := by
  intro hdvd
  have hone : 1 ≤ 2 ^ (t + t + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h0 : ((2 : ZMod 3) ^ (t + t + 1) - 1) = 0 := by
    have hcast : ((2 : ZMod 3) ^ (t + t + 1) - 1) =
        ((2 ^ (t + t + 1) - 1 : ℕ) : ZMod 3) := by
      rw [Nat.cast_sub hone, Nat.cast_one, Nat.cast_pow]
      norm_num
    rw [hcast, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hp : ((2 : ZMod 3) ^ (t + t + 1)) = -1 := by
    rw [show (2 : ZMod 3) = -1 by decide]
    exact (show Odd (t + t + 1) from ⟨t, by ring⟩).neg_one_pow
  rw [hp] at h0
  exact (by decide : ((-1 - 1 : ZMod 3)) ≠ 0) h0

private lemma padicValNat_three_four_pow_sub_one (t : ℕ) :
    padicValNat 3 (4 ^ (t + 1) - 1) = 1 + padicValNat 3 (t + 1) := by
  have h := padicValNat.pow_sub_pow (p := 3) (hp1 := by decide) (x := 4) (y := 1)
    (by norm_num : (1 : ℕ) < 4) (by norm_num : (3 : ℕ) ∣ 4 - 1)
    (by norm_num : ¬ (3 : ℕ) ∣ 4) (n := t + 1) (by omega)
  simpa using h

private lemma padicValNat_three_card_sl_two_step (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) / 2 + padicValNat 3 ((n + 1) / 2).factorial =
      n / 2 + padicValNat 3 (n / 2).factorial + padicValNat 3 (2 ^ (n + 1) - 1) := by
  rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    have ht1 : 1 ≤ t := by omega
    have hz : padicValNat 3 (2 ^ (t + t + 1) - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (not_three_dvd_two_pow_odd t)
    have h1 : (t + t + 1) / 2 = t := by omega
    have h2 : (t + t) / 2 = t := by omega
    rw [h1, h2, hz, add_zero]
  · subst ht
    have h1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have h2 : (2 * t + 1) / 2 = t := by omega
    have hz : 2 ^ (2 * t + 1 + 1) - 1 = 4 ^ (t + 1) - 1 := by
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) from by ring, pow_mul]
      norm_num
    rw [h1, h2, hz, padicValNat_three_four_pow_sub_one,
      padicValNat_three_factorial_succ]
    omega

private lemma card_sl_succ_mul {K : Type*} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1)) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) K) *
        (Nat.card K ^ n * (Nat.card K ^ (n + 1) - 1)) := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := n + 1)
    (by omega)
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := n) hn
  rw [h1, h2]
  have hprod : ∏ j ∈ Finset.Icc 2 (n + 1), (Nat.card K ^ j - 1) =
      (∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1)) * (Nat.card K ^ (n + 1) - 1) := by
    rw [Finset.prod_Icc_succ_top (a := 2) (b := n) (by omega) (fun j => Nat.card K ^ j - 1)]
  have hpow : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
    have h : (n + 1) * n = n * (n - 1) + n * 2 := by
      have h1 : n + 1 = (n - 1) + 2 := by omega
      rw [Nat.mul_comm (n + 1) n, h1, Nat.mul_add]
    rw [h, Nat.add_mul_div_right _ _ (by norm_num : (0 : ℕ) < 2)]
  have hsub : n + 1 - 1 = n := by omega
  rw [hsub, hprod, hpow, pow_add]
  ring

private lemma padicValNat_three_card_sl_two {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin n) F2)) =
      n / 2 + padicValNat 3 (n / 2).factorial := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  induction t with
  | zero =>
      have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 1) F2) = 1 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F2) (n := 1)
          (by norm_num)]
        norm_num
      rw [h1]
      norm_num
  | succ t ih =>
      have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin (t + 1 + 1)) F2) =
          Nat.card (Matrix.SpecialLinearGroup (Fin (t + 1)) F2) *
            (2 ^ (t + 1) * (2 ^ (t + 1 + 1) - 1)) := by
        have h := card_sl_succ_mul (K := F2) (t + 1) (by omega)
        rwa [natCard_f2] at h
      have hc1 : Nat.card (Matrix.SpecialLinearGroup (Fin (t + 1)) F2) ≠ 0 :=
        Nat.card_pos.ne'
      have hc2 : (2 : ℕ) ^ (t + 1) * (2 ^ (t + 1 + 1) - 1) ≠ 0 := by
        have h2 : 1 ≤ 2 ^ (t + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
        have h3 : (0 : ℕ) < 2 ^ (t + 1 + 1) - 1 := by omega
        positivity
      have h3 : (2 : ℕ) ^ (t + 1) ≠ 0 := by positivity
      have h4 : (2 : ℕ) ^ (t + 1 + 1) - 1 ≠ 0 := by
        have h2 : 1 ≤ 2 ^ (t + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hz : padicValNat 3 (2 ^ (t + 1)) = 0 := by
        refine padicValNat.eq_zero_of_not_dvd fun h => ?_
        have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        norm_num at h2
      rw [hcard, padicValNat.mul hc1 hc2, padicValNat.mul h3 h4, hz, zero_add,
        ih (by omega), padicValNat_three_card_sl_two_step (t + 1) (by omega)]

private lemma padicValNat_three_card_sl_four {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2))) =
      (n - 1) + padicValNat 3 n.factorial := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  induction t with
  | zero =>
      have h1 : Nat.card
          (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 2)) = 1 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
          (K := GaloisField 2 2) (n := 1) (by norm_num)]
        norm_num
      rw [h1]
      norm_num
  | succ t ih =>
      have hcard : Nat.card
          (Matrix.SpecialLinearGroup (Fin (t + 1 + 1)) (GaloisField 2 2)) =
          Nat.card (Matrix.SpecialLinearGroup (Fin (t + 1)) (GaloisField 2 2)) *
            (4 ^ (t + 1) * (4 ^ (t + 1 + 1) - 1)) := by
        have h := card_sl_succ_mul (K := GaloisField 2 2) (t + 1) (by omega)
        rwa [natCard_gf4] at h
      have hq : (4 : ℕ) ^ (t + 1) ≠ 0 := by positivity
      have hq4 : (4 : ℕ) ^ (t + 1 + 1) - 1 ≠ 0 := by
        have h2 : 1 ≤ (4 : ℕ) ^ (t + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hc1 : Nat.card
          (Matrix.SpecialLinearGroup (Fin (t + 1)) (GaloisField 2 2)) ≠ 0 :=
        Nat.card_pos.ne'
      have hc2 : (4 : ℕ) ^ (t + 1) * (4 ^ (t + 1 + 1) - 1) ≠ 0 := by positivity
      have hz : padicValNat 3 ((4 : ℕ) ^ (t + 1)) = 0 := by
        refine padicValNat.eq_zero_of_not_dvd fun h => ?_
        have h2 : (3 : ℕ) ∣ 4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        norm_num at h2
      have hz4 : padicValNat 3 ((4 : ℕ) ^ (t + 1 + 1) - 1) =
          1 + padicValNat 3 (t + 1 + 1) := by
        have h := padicValNat_three_four_pow_sub_one (t + 1)
        rwa [show t + 1 + 1 = (t + 1) + 1 from rfl] at h
      rw [hcard, padicValNat.mul hc1 hc2, padicValNat.mul hq hq4, hz, zero_add,
        ih (by omega), hz4]
      have hfac := padicValNat_three_factorial_succ (t + 1)
      omega

private theorem card_sl_four_ne_card_sl_two_aux {r m : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hmr : m < 2 * r - 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) ≠
      Nat.card (Matrix.SpecialLinearGroup (Fin m) F2) := by
  intro heq
  have hv : padicValNat 3
      (Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2))) =
      padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin m) F2)) := by rw [heq]
  rw [padicValNat_three_card_sl_four (by omega), padicValNat_three_card_sl_two (by omega)] at hv
  have hm2 : m / 2 ≤ r - 2 := by omega
  have hmono := padicValNat_three_factorial_mono_le hm2
  have hdiff := padicValNat_three_factorial_sub_two hr
  omega

private lemma card_exponent_zero_on {s : ℕ} (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) :
    Nat.card {u : Multiplicative (Fin s → ZMod 3) |
      ∀ i, k i = 0 → Multiplicative.toAdd u i = 0} = 3 ^ ones k := by
  classical
  have hzero : ∀ i : Fin s, ¬ k i = 1 → k i = 0 := by
    intro i hi
    rcases hk i with h | h
    · exact h
    · exact absurd h hi
  have hcard : Fintype.card {i : Fin s // k i = 1} = ones k := by
    rw [Fintype.card_subtype]
    rfl
  let e : Fin (ones k) ≃ {i : Fin s // k i = 1} := (Fintype.equivFinOfCardEq hcard).symm
  have hbij : Nat.card {u : Multiplicative (Fin s → ZMod 3) |
      ∀ i, k i = 0 → Multiplicative.toAdd u i = 0} =
      Nat.card (Fin (ones k) → ZMod 3) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun u j => Multiplicative.toAdd u.1 (e j).1
        invFun := fun v => ⟨Multiplicative.ofAdd fun i =>
          if h : k i = 1 then v (e.symm ⟨i, h⟩) else 0, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro i hi
      show Multiplicative.toAdd (Multiplicative.ofAdd (fun i =>
        if h : k i = 1 then v (e.symm ⟨i, h⟩) else 0)) i = 0
      change (if h : k i = 1 then v (e.symm ⟨i, h⟩) else 0) = 0
      rw [dif_neg (by omega : ¬ k i = 1)]
    · intro u
      apply Subtype.ext
      apply Multiplicative.ext
      funext i
      by_cases hi : k i = 1
      · show (if h : k i = 1 then Multiplicative.toAdd u.1 (e (e.symm ⟨i, h⟩)).1 else 0) =
          Multiplicative.toAdd u.1 i
        rw [dif_pos hi, Equiv.apply_symm_apply]
      · show (if h : k i = 1 then Multiplicative.toAdd u.1 (e (e.symm ⟨i, h⟩)).1 else 0) =
          Multiplicative.toAdd u.1 i
        rw [dif_neg hi]
        exact (u.2 i (hzero i hi)).symm
    · intro v
      funext j
      have h1 : k (e j).1 = 1 := (e j).2
      show (if h : k (e j).1 = 1 then v (e.symm ⟨(e j).1, h⟩) else 0) = v j
      rw [dif_pos h1]
      have harg : (⟨(e j).1, h1⟩ : {i : Fin s // k i = 1}) = e j := Subtype.ext rfl
      rw [harg, Equiv.symm_apply_apply]
  rw [hbij, Nat.card_fun, Nat.card_zmod]
  simp

private lemma card_exponent_const_on {s : ℕ} (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) (hne : 1 ≤ ones k) :
    Nat.card {u : Fin s → ZMod 3 | ∀ i j, k i = 1 → k j = 1 → u i = u j} =
      3 ^ (s - ones k + 1) := by
  classical
  have hzero : ∀ i : Fin s, ¬ k i = 1 → k i = 0 := by
    intro i hi
    rcases hk i with h | h
    · exact h
    · exact absurd h hi
  have hpos : 0 < (Finset.univ.filter fun i : Fin s => k i = 1).card := by
    simpa [ones] using hne
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos
  have hk₀ : k i₀ = 1 := (Finset.mem_filter.mp hi₀).2
  have hcard_inact : Fintype.card {i : Fin s // k i = 0} = s - ones k := by
    rw [Fintype.card_subtype]
    have hcompl : (Finset.univ.filter fun i : Fin s => k i = 0) =
        (Finset.univ.filter fun i : Fin s => ¬ k i = 1) := by
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · intro h
        rcases hk i with h0 | h1
        · omega
        · omega
      · intro h
        rcases hk i with h0 | h1
        · exact h0
        · exact absurd h1 h
    rw [hcompl]
    have hone : (Finset.univ.filter fun i : Fin s => k i = 1).card = ones k := rfl
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s))) (p := fun i => k i = 1)
    rw [Finset.card_univ, Fintype.card_fin, hone] at hsum
    omega
  let e0 : Fin (s - ones k) ≃ {i : Fin s // k i = 0} :=
    (Fintype.equivFinOfCardEq hcard_inact).symm
  have hbij : Nat.card {u : Fin s → ZMod 3 | ∀ i j, k i = 1 → k j = 1 → u i = u j} =
      Nat.card (ZMod 3 × (Fin (s - ones k) → ZMod 3)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun u => (u.1 i₀, fun j => u.1 (e0 j).1)
        invFun := fun p =>
          ⟨fun i => if h : k i = 1 then p.1 else p.2 (e0.symm ⟨i, hzero i h⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro i j hi hj
      show (if h : k i = 1 then p.1 else p.2 (e0.symm ⟨i, hzero i h⟩)) =
        (if h : k j = 1 then p.1 else p.2 (e0.symm ⟨j, hzero j h⟩))
      rw [dif_pos hi, dif_pos hj]
    · intro u
      ext i
      by_cases hi : k i = 1
      · show (if h : k i = 1 then u.1 i₀ else u.1 (e0 (e0.symm ⟨i, hzero i h⟩)).1) = u.1 i
        rw [dif_pos hi]
        exact (u.2 i i₀ hi hk₀).symm
      · show (if h : k i = 1 then u.1 i₀ else u.1 (e0 (e0.symm ⟨i, hzero i h⟩)).1) = u.1 i
        rw [dif_neg hi, Equiv.apply_symm_apply]
    · intro p
      refine Prod.ext ?_ ?_
      · show (if h : k i₀ = 1 then p.1 else p.2 (e0.symm ⟨i₀, hzero i₀ h⟩)) = p.1
        rw [dif_pos hk₀]
      · funext j
        show (if h : k (e0 j).1 = 1 then p.1 else
          p.2 (e0.symm ⟨(e0 j).1, hzero (e0 j).1 h⟩)) = p.2 j
        rw [dif_neg (by have := (e0 j).2; omega : ¬ k (e0 j).1 = 1)]
        have harg : (⟨(e0 j).1, (e0 j).2⟩ : {i : Fin s // k i = 0}) = e0 j :=
          Subtype.ext rfl
        rw [harg, Equiv.symm_apply_apply]
  rw [hbij, Nat.card_prod, Nat.card_fun, Nat.card_zmod]
  rw [show (3 : ℕ) * 3 ^ Nat.card (Fin (s - ones k)) = 3 ^ (s - ones k + 1) by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.pow_succ, Nat.mul_comm]]

private lemma torus_ofAdd {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (u : Fin s → ZMod 3) :
    (SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r) (p := 3)
        ε det_rootMat_phi3 rootMat_phi3_pow_three) (Multiplicative.ofAdd u) =
      SLNS.nsSL ε det_rootMat_phi3 fun i => (u i).val :=
  SlNsRootGen.torusSL_apply rootMat_phi3_pow_three u

private lemma torus_injective {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :
    Function.Injective (SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s)
      (r := r) (p := 3) ε det_rootMat_phi3 rootMat_phi3_pow_three) := by
  refine CoordSL.frameHom_injective (ψ := MonoidHom.id _) (A₀ := 1) (ε := ε)
    (C := rootMat phi3) (hC := det_rootMat_phi3) rootMat_phi3_pow_three ?_ ?_ ?_
  · rw [MonoidHom.ker_id]
    exact bot_le
  · rw [rootPB_phi3_dim]
    norm_num
  · intro j hj c
    exact CoordSL.isUnit_rootMat_pow_sub (K := F2) (g := phi3) (ℓ := 3) Nat.prime_three
      (by rw [natCard_f2]; norm_num) natCast_three_ne_zero phi3_dvd_cyclotomic j hj c

private lemma torus_card {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :
    Nat.card ↥((SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r)
        (p := 3) ε det_rootMat_phi3 rootMat_phi3_pow_three).range) = 3 ^ s := by
  have hinj := torus_injective ε
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod]

private lemma isElemAbelian_torus {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :
    CFSG.Open.IsElemAbelian 3 (SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s)
      (r := r) (p := 3) ε det_rootMat_phi3 rootMat_phi3_pow_three).range := by
  have hsmul : ∀ x : ZMod 3, (3 : ℕ) • x = 0 := by decide
  have hpow : ∀ (a : Multiplicative (Fin s → ZMod 3)) (n : ℕ),
      (a ^ n).toAdd = n • a.toAdd := by
    intro a n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, succ_nsmul,
          show (a ^ n * a).toAdd = (a ^ n).toAdd + a.toAdd from rfl, ih]
  have h3 : ∀ u : Multiplicative (Fin s → ZMod 3), u ^ 3 = 1 := by
    intro u
    apply Multiplicative.ext
    rw [hpow]
    change 3 • u.toAdd = 0
    funext i
    change 3 • (u.toAdd i) = 0
    exact hsmul _
  constructor
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    change (a : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) * b =
      (b : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) * a
    rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
  · intro x hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow, h3 u, map_one]

private lemma fixS_eq_zeroCoords {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (k : Fin s → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1) :
    SLNS.fixS ε (Finset.univ.filter fun i : Fin s => k i = 1) =
      CoordSL.zeroCoords ε (fun i => (k i : ZMod 3)) := by
  ext x
  rw [SLNS.mem_fixS]
  rcases hx : ε x with ⟨a, i⟩ | j
  · have hzi : (x ∈ CoordSL.zeroCoords ε fun i => (k i : ZMod 3)) ↔ (k i : ZMod 3) = 0 :=
      CoordSL.mem_zeroCoords_inl hx
    rw [hzi]
    change (¬ i ∈ Finset.univ.filter fun i : Fin s => k i = 1) ↔ (k i : ZMod 3) = 0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases hk i with h0 | h1
      · simpa [h0]
      · exact absurd h1 h
    · intro h h1
      rw [h1] at h
      exact absurd h (by decide)
  · simp [SLNS.inT, CoordSL.mem_zeroCoords_inr hx]

private theorem card_inter_centralizer_zeroBlk {n s r : ℕ}
    (hd : n + 1 = 2 * s ∨ n + 1 = 2 * s + 1) (hs : 3 ≤ s)
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (k : Fin s → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1)
    (h2 : 2 ≤ n + 1 - 2 * ones k) :
    Nat.card ↥((SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r)
        (p := 3) ε det_rootMat_phi3 rootMat_phi3_pow_three).range ⊓
      Subgroup.centralizer ((zeroBlk (n := n) (s := s) (r := r) ε k :
        Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) = 3 ^ ones k := by
  classical
  set τ := SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r) (p := 3)
    ε det_rootMat_phi3 rootMat_phi3_pow_three with hτ
  set C : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2) :=
    Subgroup.centralizer ((zeroBlk (n := n) (s := s) (r := r) ε k :
      Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) with hC
  have hzero : ∀ i : Fin s, ¬ k i = 1 → k i = 0 := by
    intro i hi
    rcases hk i with h | h
    · exact h
    · exact absurd h hi
  let Tb : Finset (Fin s) := Finset.univ.filter fun i => k i = 1
  have hTb : Tb.card = ones k := rfl
  let A : Subgroup (Multiplicative (Fin s → ZMod 3)) :=
    { carrier := {u | ∀ i, k i = 0 → Multiplicative.toAdd u i = 0}
      one_mem' := by intro i _; simp
      mul_mem' := by
        intro a b ha hb i hi
        show Multiplicative.toAdd (a * b) i = 0
        rw [show Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b
          from rfl, Pi.add_apply, ha i hi, hb i hi, add_zero]
      inv_mem' := by
        intro a ha i hi
        show Multiplicative.toAdd a⁻¹ i = 0
        rw [show Multiplicative.toAdd a⁻¹ = -Multiplicative.toAdd a from rfl, Pi.neg_apply,
          ha i hi, neg_zero] }
  have hAle : A.map τ ≤ τ.range ⊓ C := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨u, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hcomm := CoordSL.comm_zeroBlock_of_torus (K := F2) (g := phi3) (n := n + 1)
      (s := s) (r := r) (β := fun i => (k i : ZMod 3)) (ε := ε)
      (hC := det_rootMat_phi3) (k := fun i => (Multiplicative.toAdd u i).val) ?_ hy
    · have hτu : τ u = SLNS.nsSL ε det_rootMat_phi3
          (fun i => (Multiplicative.toAdd u i).val) :=
        show τ u = _ from torus_ofAdd ε (Multiplicative.toAdd u)
      rw [hτu]
      exact hcomm.symm
    · intro i hi
      have hk0 : k i = 0 := by
        rcases hk i with h0 | h1
        · exact h0
        · exfalso
          rw [h1] at hi
          exact absurd hi (by decide)
      have := hu i hk0
      rw [this]
      simp
  have hcardA : Nat.card ↥(A.map τ) = 3 ^ ones k := by
    rw [Subgroup.card_map_of_injective (torus_injective ε)]
    exact card_exponent_zero_on k hk
  have hstar : GGBstar 3 τ.range τ.range := by
    refine ⟨le_rfl, isElemAbelian_torus ε, ?_, ?_⟩
    · rw [torus_card ε]
      omega
    · intro g hg _
      exact CommonJRowLinTwo.ggCommonJRowLinTwo_hsc hd hs (isElemAbelian_torus ε)
        (torus_card ε) g (fun e he => (Subgroup.mem_centralizer_iff.mp hg e he).symm)
  have hcent : Subgroup.centralizer (⊤ : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) =
      ⊥ := by
    rw [show (⊤ : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) = Set.univ from rfl,
      Subgroup.centralizer_univ]
    exact CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (by omega) (Or.inr natCard_f2)
  have hnsp : ∀ c : F2, c ^ 3 = 1 → c = 1 := by
    intro c hc
    haveI : Fintype F2 := Fintype.ofFinite F2
    have hcard : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, natCard_f2]
    have hsq : c ^ 2 = c := by
      have h := FiniteField.pow_card (K := F2) c
      rwa [hcard] at h
    have hc3 : c ^ 3 = c := by
      rw [pow_succ, hsq, ← pow_two, hsq]
    rw [hc] at hc3
    exact hc3.symm
  have hgg : SLRep.ggFrame (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))
      1 = MonoidHom.id _ := by
    ext X
    simp only [SLRep.ggFrame_apply, MonoidHom.id_apply, one_mul, inv_one, mul_one]
  have hframe : ∀ b ∈ τ.range, ∃ k' : Fin s → ℕ,
      b = SLRep.ggFrame (MonoidHom.id _) 1 (SLNS.nsSL ε det_rootMat_phi3 k') := by
    intro b hb
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hb
    refine ⟨fun i => (Multiplicative.toAdd u i).val, ?_⟩
    have hτu : τ u = SLNS.nsSL ε det_rootMat_phi3
        (fun i => (Multiplicative.toAdd u i).val) :=
      show τ u = _ from torus_ofAdd ε (Multiplicative.toAdd u)
    rw [hτu, hgg, MonoidHom.id_apply]
  have hctx : SLNS.NSCtx (ε := ε) (hC := det_rootMat_phi3) (C := rootMat phi3)
      (G := Matrix.SpecialLinearGroup (Fin (n + 1)) F2) 3 τ.range τ.range ⊤
      (MonoidHom.id _) 1 :=
    { bstar := hstar
      ker := by rw [MonoidHom.ker_id]; exact bot_le
      range := MonoidHom.range_eq_top.mpr Function.surjective_id
      cent := hcent
      prime := Nat.prime_three
      nsplit := hnsp
      cp := rootMat_phi3_pow_three
      cunit := fun j hj c => CoordSL.isUnit_rootMat_pow_sub (K := F2) (g := phi3) (ℓ := 3)
        Nat.prime_three (by rw [natCard_f2]; norm_num) natCast_three_ne_zero
        phi3_dvd_cyclotomic j hj c
      frame := hframe }
  have hblock : Subgroup.map (SLRep.ggFrame (MonoidHom.id
        (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) 1)
      (CFSG.RankThree.CALinearPlane.coordBlockSL F2 (SLNS.fixS ε Tb)) =
      zeroBlk (n := n) (s := s) (r := r) ε k := by
    rw [hgg, Subgroup.map_id]
    congr 1
    exact fixS_eq_zeroCoords ε k hk
  have hS2 : 2 ≤ (SLNS.fixS ε Tb).card := by
    rw [fixS_eq_zeroCoords ε k hk, GGHalf.card_zeroCoords ε k hk]
    exact h2
  have hup : Nat.card ↥(τ.range ⊓ C) ≤ 3 ^ ones k := by
    have hle := hctx.card_centralizer_le (Tb := Tb) hS2 (by rw [rootPB_phi3_dim]; norm_num)
    rwa [hblock, hTb] at hle
  have hlow : 3 ^ ones k ≤ Nat.card ↥(τ.range ⊓ C) := by
    rw [← hcardA]
    let g : ↥(A.map τ) → ↥(τ.range ⊓ C) := fun x => ⟨x.1, hAle x.2⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have h : (x : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) = y :=
        congrArg (fun z : ↥(τ.range ⊓ C) =>
          (z : Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) hxy
      exact Subtype.ext h
    exact Nat.card_le_card_of_injective g hg
  change Nat.card ↥(τ.range ⊓ C) = 3 ^ ones k
  exact le_antisymm hup hlow

private lemma root_phi3_pow_val_eq {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : AdjoinRoot.root phi3 ^ a = AdjoinRoot.root phi3 ^ b) : a = b := by
  have hord : orderOf (AdjoinRoot.root phi3) = 3 :=
    (CoordSL.root_isPrimitiveRoot (g := phi3) (ℓ := 3) Nat.prime_three
      natCast_three_ne_zero phi3_dvd_cyclotomic).eq_orderOf.symm
  refine pow_injOn_Iio_orderOf (x := AdjoinRoot.root phi3) ?_ ?_ h
  · rwa [hord]
  · rwa [hord]

private lemma transvection_mem_classBlockCoord {s : ℕ} {k : Fin s → ℕ} {i j : Fin s}
    (hij : i ≠ j) (hi : k i = 1) (hj : k j = 1) :
    Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3) ∈
      CFSG.RankThree.CALinearPlane.coordBlockSL (AdjoinRoot phi3)
        (CoordSL.classSet (fun i => (k i : ZMod 3)) 1) := by
  rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff]
  intro a b hab
  have hia : ¬ (i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    rcases hab with h | h
    · exact h (CoordSL.mem_classSet.mpr (by simp [hi]))
    · exact h (CoordSL.mem_classSet.mpr (by simp [hj]))
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, if_neg hia]
  by_cases hab' : a = b
  · subst b
    simp [hia]
  · simp [hia, hab']

private lemma exponent_eq_of_comm_transvection {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    {t : Fin s → ZMod 3} {i j : Fin s} (hij : i ≠ j)
    (hcomm : SLNS.nsSL ε det_rootMat_phi3 (fun l => (t l).val) *
        CoordSL.theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3)) =
      CoordSL.theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3)) *
        SLNS.nsSL ε det_rootMat_phi3 (fun l => (t l).val)) :
    t i = t j := by
  classical
  set T : Matrix (Fin s) (Fin s) (AdjoinRoot phi3) :=
    ((Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3) :
      Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot phi3)) :
        Matrix (Fin s) (Fin s) (AdjoinRoot phi3)) with hT
  have hm : SLNS.nsMat ε (rootMat phi3) (fun l => (t l).val) * CoordSL.thetaMat phi3 ε T =
      CoordSL.thetaMat phi3 ε T * SLNS.nsMat ε (rootMat phi3) (fun l => (t l).val) := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 =>
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) hcomm
    exact h
  have hfr : CoordSL.frameForm phi3 ε (SLNS.nsMat ε (rootMat phi3) (fun l => (t l).val)) ∘ₗ
        CoordSL.frameForm phi3 ε (CoordSL.thetaMat phi3 ε T) =
      CoordSL.frameForm phi3 ε (CoordSL.thetaMat phi3 ε T) ∘ₗ
        CoordSL.frameForm phi3 ε (SLNS.nsMat ε (rootMat phi3) (fun l => (t l).val)) := by
    have h := congrArg (CoordSL.frameForm phi3 ε) hm
    simpa only [CoordSL.frameForm_mul] using h
  have hx : CoordSL.torusAct phi3 (fun l => (t l).val)
        (CoordSL.blockAct (r := r) phi3 T (Pi.single j 1, (0 : Fin r → F2))) =
      CoordSL.blockAct (r := r) phi3 T
        (CoordSL.torusAct phi3 (fun l => (t l).val) (Pi.single j 1, (0 : Fin r → F2))) := by
    have h := LinearMap.congr_fun hfr (Pi.single j (1 : AdjoinRoot phi3), (0 : Fin r → F2))
    simpa only [LinearMap.comp_apply, CoordSL.frameForm_nsMat, CoordSL.frameForm_thetaMat] using h
  have hTA : CoordSL.blockAct (r := r) phi3 T (Pi.single j 1, (0 : Fin r → F2)) =
      (Pi.single j 1 + Pi.single i 1, (0 : Fin r → F2)) := by
    rw [CoordSL.blockAct_apply, hT, CoordSL.transvection_mulVec]
    simp
  have hTB : CoordSL.torusAct phi3 (fun l => (t l).val) (Pi.single j 1, (0 : Fin r → F2)) =
      ((fun l => if l = j then AdjoinRoot.root phi3 ^ (t j).val else 0), (0 : Fin r → F2)) := by
    refine Prod.ext (funext fun l => ?_) rfl
    by_cases hl : l = j
    · subst hl
      simp [CoordSL.torusAct]
    · simp [CoordSL.torusAct, Pi.single_apply, hl, Ne.symm hl]
  have hL : (CoordSL.torusAct phi3 (fun l => (t l).val)
        (Pi.single j 1 + Pi.single i 1, (0 : Fin r → F2))).1 i =
      AdjoinRoot.root phi3 ^ (t i).val := by
    simp [CoordSL.torusAct, Pi.single_apply, hij, Ne.symm hij]
  have hR : (CoordSL.blockAct (r := r) phi3 T
        ((fun l => if l = j then AdjoinRoot.root phi3 ^ (t j).val else 0),
          (0 : Fin r → F2))).1 i = AdjoinRoot.root phi3 ^ (t j).val := by
    rw [CoordSL.blockAct_apply, hT, CoordSL.transvection_mulVec]
    simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hTA, hTB] at hx
  have h2 := congrFun (congrArg Prod.fst hx) i
  rw [hL, hR] at h2
  exact ZMod.val_injective 3
    (root_phi3_pow_val_eq (ZMod.val_lt (t i)) (ZMod.val_lt (t j)) h2)

private lemma card_exponent_const_on_mul {s : ℕ} (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) (hne : 1 ≤ ones k) :
    Nat.card {u : Multiplicative (Fin s → ZMod 3) |
      ∀ i j, k i = 1 → k j = 1 → Multiplicative.toAdd u i = Multiplicative.toAdd u j} =
      3 ^ (s - ones k + 1) := by
  rw [← card_exponent_const_on k hk hne]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun _ => Iff.rfl))

private theorem card_inter_centralizer_classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (k : Fin s → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1) (hne : 1 ≤ ones k) :
    Nat.card ↥((SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r)
        (p := 3) ε det_rootMat_phi3 rootMat_phi3_pow_three).range ⊓
      Subgroup.centralizer ((classBlk (n := n) (s := s) (r := r) ε k :
        Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
        Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) = 3 ^ (s - ones k + 1) := by
  classical
  set τ := SlNsRootGen.torusSL (K := F2) (g := phi3) (n := n + 1) (s := s) (r := r) (p := 3)
    ε det_rootMat_phi3 rootMat_phi3_pow_three with hτ
  set C : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2) :=
    Subgroup.centralizer ((classBlk (n := n) (s := s) (r := r) ε k :
      Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) with hC
  let A : Subgroup (Multiplicative (Fin s → ZMod 3)) :=
    { carrier := {u | ∀ i j, k i = 1 → k j = 1 →
        Multiplicative.toAdd u i = Multiplicative.toAdd u j}
      one_mem' := by intro i j _ _; simp
      mul_mem' := by
        intro a b ha hb i j hi hj
        show Multiplicative.toAdd (a * b) i = Multiplicative.toAdd (a * b) j
        rw [show Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b
          from rfl, Pi.add_apply, Pi.add_apply, ha i j hi hj, hb i j hi hj]
      inv_mem' := by
        intro a ha i j hi hj
        show Multiplicative.toAdd a⁻¹ i = Multiplicative.toAdd a⁻¹ j
        rw [show Multiplicative.toAdd a⁻¹ = -Multiplicative.toAdd a from rfl, Pi.neg_apply,
          Pi.neg_apply, ha i j hi hj] }
  have hk1 : ∀ i, (k i : ZMod 3) = 1 → k i = 1 := by
    intro i hi
    rcases hk i with h0 | h1
    · rw [h0] at hi
      simp at hi
    · exact h1
  have hAle : A.map τ ≤ τ.range ⊓ C := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨u, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hy
    have hconst : ∀ i j, (k i : ZMod 3) = 1 → (k j : ZMod 3) = 1 →
        (Multiplicative.toAdd u i).val = (Multiplicative.toAdd u j).val := by
      intro i j hi hj
      rw [hu i j (hk1 i hi) (hk1 j hj)]
    have hτu : (τ u : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) =
        SLNS.nsSL ε det_rootMat_phi3 (fun l => (Multiplicative.toAdd u l).val) :=
      torus_ofAdd ε (Multiplicative.toAdd u)
    rw [hτu]
    exact CoordSL.comm_classBlock_of_torus (β := fun i => (k i : ZMod 3)) (c := 1)
      (k := fun l => (Multiplicative.toAdd u l).val) (ε := ε) (hC := det_rootMat_phi3)
      (g := phi3) (K := F2) (n := n + 1) (s := s) (r := r) (p := 3) hconst hM
  have hAge : τ.range ⊓ C ≤ A.map τ := by
    intro x hx
    obtain ⟨hxr, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hxr
    refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    change ∀ i j, k i = 1 → k j = 1 →
      Multiplicative.toAdd u i = Multiplicative.toAdd u j
    intro i j hi hj
    by_cases hij : i = j
    · rw [hij]
    have hTmem : Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3) ∈
        CFSG.RankThree.CALinearPlane.coordBlockSL (AdjoinRoot phi3)
          (CoordSL.classSet (fun i => (k i : ZMod 3)) 1) :=
      transvection_mem_classBlockCoord hij hi hj
    have hθmem : CoordSL.theta phi3 ε
        (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3)) ∈
        classBlk (n := n) (s := s) (r := r) ε k :=
      Subgroup.mem_map_of_mem _ hTmem
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hθmem
    have hτu : (τ u : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) =
        SLNS.nsSL ε det_rootMat_phi3 (fun l => (Multiplicative.toAdd u l).val) :=
      torus_ofAdd ε (Multiplicative.toAdd u)
    rw [hτu] at hc
    exact exponent_eq_of_comm_transvection ε hij hc.symm
  have hcard : Nat.card ↥(A.map τ) = 3 ^ (s - ones k + 1) := by
    rw [Subgroup.card_map_of_injective (torus_injective ε)]
    exact card_exponent_const_on_mul k hk hne
  have hEq : A.map τ = τ.range ⊓ C := le_antisymm hAle hAge
  rw [← hEq]
  exact hcard

private lemma natCard_sl_le_one {K : Type*} [Field K] [Finite K] {m : ℕ} (hm : m ≤ 1) :
    Nat.card (Matrix.SpecialLinearGroup (Fin m) K) = 1 := by
  interval_cases m
  · refine Nat.card_eq_one_iff_unique.mpr ⟨?_, ⟨1⟩⟩
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim (a : Matrix (Fin 0) (Fin 0) K) b)⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 1)
      (by norm_num), Finset.Icc_eq_empty (by norm_num : ¬ (2 : ℕ) ≤ 1)]
    simp

private lemma natCard_sl_two_four :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
    natCard_gf4]
  norm_num

private lemma natCard_sl_three_four :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 3) (by norm_num),
    natCard_gf4]
  decide

private lemma natCard_sl_two_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F2) = 6 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
    natCard_f2]
  norm_num

private lemma natCard_sl_three_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F2) = 168 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 3) (by norm_num),
    natCard_f2]
  decide

private lemma card_sl_four_mono {s r : ℕ} (hs : 2 ≤ s) (hsr : s ≤ r) :
    Nat.card (Matrix.SpecialLinearGroup (Fin s) (GaloisField 2 2)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) := by
  refine Nat.le_induction (m := s)
    (P := fun r _ => Nat.card (Matrix.SpecialLinearGroup (Fin s) (GaloisField 2 2)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2))) le_rfl ?_ r hsr
  intro t ht ih
  refine ih.trans ?_
  rw [card_sl_succ_mul (K := GaloisField 2 2) t (by omega)]
  refine Nat.le_mul_of_pos_right _ ?_
  have h2 : 2 ≤ Nat.card (GaloisField 2 2) := by rw [natCard_gf4]; norm_num
  have h1 : 1 ≤ Nat.card (GaloisField 2 2) ^ t := Nat.one_le_pow _ _ (by omega)
  have hq : 2 ≤ Nat.card (GaloisField 2 2) ^ (t + 1) := by
    calc 2 ≤ Nat.card (GaloisField 2 2) ^ 1 := by rw [pow_one, natCard_gf4]; norm_num
      _ ≤ Nat.card (GaloisField 2 2) ^ (t + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 1 ≤ Nat.card (GaloisField 2 2) ^ (t + 1) - 1 := by omega
  calc 1 = 1 * 1 := (Nat.mul_one 1).symm
    _ ≤ Nat.card (GaloisField 2 2) ^ t * (Nat.card (GaloisField 2 2) ^ (t + 1) - 1) :=
        Nat.mul_le_mul h1 h3

private lemma card_sl_four_ge_sixty {r : ℕ} (hr : 2 ≤ r) :
    60 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) := by
  have h := card_sl_four_mono (s := 2) (r := r) le_rfl hr
  rwa [natCard_sl_two_four] at h

private lemma card_sl_four_ge_60480 {r : ℕ} (hr : 3 ≤ r) :
    60480 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) := by
  have h := card_sl_four_mono (s := 3) (r := r) (by norm_num) hr
  rwa [natCard_sl_three_four] at h

private theorem natCard_sl_four_ne_sl_two {n m r s : ℕ}
    (hd : n + 1 = 2 * m ∨ n + 1 = 2 * m + 1) (hm : 3 ≤ m) (hs : s = n + 1 - 2 * r) :
    Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) ≠
      Nat.card (Matrix.SpecialLinearGroup (Fin s) F2) := by
  intro heq
  have hn : 6 ≤ n + 1 := by omega
  rcases lt_or_ge r 2 with hr1 | hr2
  · have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin r) (GaloisField 2 2)) = 1 :=
      natCard_sl_le_one (K := GaloisField 2 2) (by omega)
    rw [h1] at heq
    have hs2 : 2 ≤ s := by omega
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F2) ≤
        Nat.card (Matrix.SpecialLinearGroup (Fin s) F2) := by
      rcases eq_or_lt_of_le hs2 with h | h
      · rw [← h]
      · exact le_of_lt (card_sl_two_strictMono (by norm_num) h)
    rw [natCard_sl_two_two] at h6
    omega
  · rcases lt_or_ge s 4 with hs3 | hs4
    · interval_cases s
      · have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 0) F2) = 1 :=
          natCard_sl_le_one (K := F2) (by omega)
        rw [h1] at heq
        have h60 := card_sl_four_ge_sixty hr2
        omega
      · have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 1) F2) = 1 :=
          natCard_sl_le_one (K := F2) (by omega)
        rw [h1] at heq
        have h60 := card_sl_four_ge_sixty hr2
        omega
      · rw [natCard_sl_two_two] at heq
        have h60 := card_sl_four_ge_sixty hr2
        omega
      · rw [natCard_sl_three_two] at heq
        rcases eq_or_lt_of_le hr2 with h2 | h3
        · rw [← h2, natCard_sl_two_four] at heq
          omega
        · have hge := card_sl_four_ge_60480 h3
          omega
    · rcases lt_or_ge s (2 * r - 2) with hlt | hge
      · exact card_sl_four_ne_card_sl_two_aux hr2 (by omega) hlt heq
      · exact card_sl_four_ne_card_sl_two hr2 hs4 (by omega) heq

private theorem exists_conj_torus_binary {n m : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (n + 1 - 2 * m))
    (f : Fin m → Multiplicative (ZMod 3)) :
    ∃ (M : Matrix.SpecialLinearGroup (Fin (n + 1)) F2) (k' : Fin m → ℕ),
      (∀ i, k' i = 0 ∨ k' i = 1) ∧
      (∀ i, k' i = 0 ↔ f i = 1) ∧
      (ggCommonJRowLinTwo_torus ε).range.map (MulAut.conj M⁻¹).toMonoidHom =
        (ggCommonJRowLinTwo_torus ε).range ∧
      M⁻¹ * ggCommonJRowLinTwo_torus ε f * M = SLNS.nsSL ε det_rootMat_phi3 k' := by
  have h01 : ∀ a : ZMod 3, (((if a = 2 then -1 else 1 : (ZMod 3)ˣ) : ZMod 3) * a).val = 0 ∨
      (((if a = 2 then -1 else 1 : (ZMod 3)ˣ) : ZMod 3) * a).val = 1 := by
    intro a
    rw [← ZMod.natCast_zmod_val a]
    have h := ZMod.val_lt (n := 3) a
    interval_cases a.val <;> decide
  have hz0 : ∀ a : ZMod 3, (((if a = 2 then -1 else 1 : (ZMod 3)ˣ) : ZMod 3) * a).val = 0 ↔
      a = 0 := by
    intro a
    rw [← ZMod.natCast_zmod_val a]
    have h := ZMod.val_lt (n := 3) a
    interval_cases a.val <;> decide
  classical
  let η : Fin m → (ZMod 3)ˣ := fun i => if Multiplicative.toAdd (f i) = 2 then -1 else 1
  have hη : ∀ i, η i ∈ galExp phi3 root_phi3_pow_three := fun i => galExp_phi3 (η i)
  obtain ⟨M, hM⟩ := exists_conj_frameHom phi3
    (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) 1 ε det_rootMat_phi3
    rootMat_phi3_pow_three root_phi3_pow_three (Equiv.refl _) η hη
  have hM' : ∀ t : Fin m → ZMod 3,
      (MulAut.conj M⁻¹) (ggCommonJRowLinTwo_torus ε (Multiplicative.ofAdd t)) =
        ggCommonJRowLinTwo_torus ε (Multiplicative.ofAdd fun i => (η i : ZMod 3) * t i) := by
    intro t
    have h := hM t
    simpa only [ggCommonJRowLinTwo_torus, SlNsRootGen.torusSL, SLRep.ggFrame_apply,
      MonoidHom.id_apply, one_mul, inv_one, mul_one, Equiv.refl_apply, MulAut.conj_apply,
      inv_inv] using h
  let k' : Fin m → ℕ := fun i => ((η i : ZMod 3) * Multiplicative.toAdd (f i)).val
  refine ⟨M, k', ?_, ?_, ?_, ?_⟩
  · intro i
    exact h01 (Multiplicative.toAdd (f i))
  · intro i
    rw [hz0 (Multiplicative.toAdd (f i))]
    constructor
    · intro h
      have h' := congrArg Multiplicative.ofAdd h
      simpa using h'
    · intro h
      rw [h]
      rfl
  · refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
      exact ⟨Multiplicative.ofAdd fun i => (η i : ZMod 3) * Multiplicative.toAdd u i,
        (hM' (Multiplicative.toAdd u)).symm⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj M⁻¹).injective]
  · have hf : f = Multiplicative.ofAdd (fun i => Multiplicative.toAdd (f i)) := rfl
    rw [hf]
    show M⁻¹ * ggCommonJRowLinTwo_torus ε
        (Multiplicative.ofAdd fun i => Multiplicative.toAdd (f i)) * M =
      SLNS.nsSL ε det_rootMat_phi3 fun i => ((η i : ZMod 3) * Multiplicative.toAdd (f i)).val
    simpa only [MulAut.conj_apply, inv_inv] using
      (hM' fun i => Multiplicative.toAdd (f i)).trans
        (torus_ofAdd ε fun i => (η i : ZMod 3) * Multiplicative.toAdd (f i))

private lemma card_inter_centralizer_conj {n m : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (n + 1 - 2 * m))
    (M : Matrix.SpecialLinearGroup (Fin (n + 1)) F2)
    (hτ : (ggCommonJRowLinTwo_torus ε).range.map (MulAut.conj M⁻¹).toMonoidHom =
      (ggCommonJRowLinTwo_torus ε).range)
    (J : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
    Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) =
      Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer ((J.map (MulAut.conj M⁻¹).toMonoidHom :
          Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
            Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) := by
  classical
  set φ : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 →*
      Matrix.SpecialLinearGroup (Fin (n + 1)) F2 := (MulAut.conj M⁻¹).toMonoidHom with hφ
  set ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 →*
      Matrix.SpecialLinearGroup (Fin (n + 1)) F2 := (MulAut.conj M).toMonoidHom with hψ
  have hinj : Function.Injective φ := by rw [hφ]; exact (MulAut.conj M⁻¹).injective
  have hφψ : φ.comp ψ = MonoidHom.id _ := by
    ext x
    simp [hφ, hψ, MulAut.conj_apply, mul_assoc]
  have hψφ : ψ.comp φ = MonoidHom.id _ := by
    ext x
    simp [hφ, hψ, MulAut.conj_apply, mul_assoc]
  have hcent : (Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))).map
        φ = Subgroup.centralizer ((J.map φ : Subgroup
          (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
            Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) := by
    refine le_antisymm ?_ ?_
    · have h := Subgroup.map_centralizer_le_centralizer_image
        (s := (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) φ
      simpa only [← Subgroup.coe_map] using h
    · have h2 : (Subgroup.centralizer ((J.map φ : Subgroup
            (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
              Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))).map ψ ≤
          Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) := by
        have h := Subgroup.map_centralizer_le_centralizer_image
          (s := ((J.map φ : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) :
            Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) ψ
        simpa only [← Subgroup.coe_map, Subgroup.map_map, hψφ, Subgroup.map_id] using h
      have h3 := Subgroup.map_mono (f := φ) h2
      rwa [Subgroup.map_map, hφψ, Subgroup.map_id] at h3
  rw [← Subgroup.card_map_of_injective (K := (ggCommonJRowLinTwo_torus ε).range ⊓
      Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) hinj,
    Subgroup.map_inf _ _ φ hinj, hτ, hcent]

private lemma two_le_card_component {G : Type*} [Group G] [Finite G]
    {J K : Subgroup G} (hJ : IsComponentOf J K) : 2 ≤ Nat.card ↥J := by
  have hq : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
  have hJnt : Nontrivial ↥J :=
    @Function.Surjective.nontrivial ↥J (↥J ⧸ Subgroup.center ↥J) hq
      (QuotientGroup.mk' (Subgroup.center ↥J)) (QuotientGroup.mk'_surjective _)
  have h := @Finite.one_lt_card ↥J _ hJnt
  omega

theorem ggCommonJRowLinTwo_hcompCount {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (hm : 3 ≤ m)
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m))
    (f : Fin m → Multiplicative (ZMod 3))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (hJ : IsComponentOf J (Subgroup.centralizer
      ({(ggCommonJRowLinTwo_torus ε) f} : Set (Matrix.SpecialLinearGroup (Fin d) F2)))) :
    let k := (Finset.univ.filter fun i : Fin m => f i ≠ 1).card
    (Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin (d - 2 * k)) F2) →
      Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin d) F2))) = 3 ^ k) ∧
    (Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2)) →
      Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin d) F2))) =
        3 ^ (m - k + 1)) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  subst hn
  let k := (Finset.univ.filter fun i : Fin m => f i ≠ 1).card
  change (Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * k)) F2) →
      Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) =
        3 ^ k) ∧
    (Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2)) →
      Nat.card ↥((ggCommonJRowLinTwo_torus ε).range ⊓
        Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) =
        3 ^ (m - k + 1))
  obtain ⟨M, k', hk', hzero, hτ, hkey⟩ := exists_conj_torus_binary ε f
  have hones : ones k' = k := by
    show (Finset.univ.filter fun i : Fin m => k' i = 1).card = k
    have hiff : ∀ i, (k' i = 1 ↔ f i ≠ 1) := by
      intro i
      rcases hk' i with h | h
      · have hf : f i = 1 := (hzero i).mp h
        rw [h, hf]
        simp
      · have hf : f i ≠ 1 := by
          intro hf1
          have h0 := (hzero i).mpr hf1
          rw [h] at h0
          exact absurd h0 (by decide)
        rw [h]
        simp [hf]
    congr 1
    exact Finset.filter_congr fun i _ => hiff i
  have htrans := card_inter_centralizer_conj ε M hτ J
  have hJ' : IsComponentOf (J.map (MulAut.conj M⁻¹).toMonoidHom)
      (Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k'} : Set
        (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))) := by
    have hcent : (Subgroup.centralizer ({(ggCommonJRowLinTwo_torus ε) f} : Set
        (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))).map
          (MulAut.conj M⁻¹).toMonoidHom =
        Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k'} : Set
          (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)) := by
      rw [Subgroup.map_conj_centralizer_singleton, inv_inv, hkey]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_centralizer_singleton_iff] at ⊢
      change Commute ((MulAut.conj M⁻¹) y) (SLNS.nsSL ε det_rootMat_phi3 k')
      simp only [MulAut.conj_apply, inv_inv]
      have hyt : Commute y ((ggCommonJRowLinTwo_torus ε) f) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hy)
      have h := Commute.map hyt (MulAut.conj M⁻¹)
      simp only [MulAut.conj_apply, inv_inv] at h
      rwa [hkey] at h
    · have hsub := hJ.2.1.map (MulAut.conj M⁻¹).toMonoidHom
      rwa [hcent] at hsub
    · exact (Assembly.IsQuasisimple.congr
        (Subgroup.equivMapOfInjective J (MulAut.conj M⁻¹).toMonoidHom
          (MulAut.conj M⁻¹).injective)).mp hJ.2.2
  have hcase := comp_eq_zeroBlk_or_classBlk ε k' hk' hJ'
  have hJnt : 2 ≤ Nat.card ↥J := two_le_card_component hJ
  refine ⟨?_, ?_⟩
  · rintro ⟨eJ⟩
    have hcardJ : Nat.card ↥J =
        Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * k)) F2) :=
      Nat.card_congr eJ.toEquiv
    rcases hcase with hz | hc
    · have h2 : 2 ≤ n + 1 - 2 * ones k' := by
        have hfinal : Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * ones k')) F2) =
            Nat.card ↥J := by
          rw [← natCard_zeroBlk ε k' hk', ← hz,
            Subgroup.card_map_of_injective (K := J) (f := (MulAut.conj M⁻¹).toMonoidHom)
              (MulAut.conj M⁻¹).injective]
        by_contra hcon
        have hle : n + 1 - 2 * ones k' ≤ 1 := by omega
        have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * ones k')) F2) = 1 :=
          natCard_sl_le_one (K := F2) hle
        omega
      rw [htrans, hz, card_inter_centralizer_zeroBlk hd hm ε k' hk' h2, hones]
    · exfalso
      have heqorder : Nat.card (Matrix.SpecialLinearGroup (Fin (ones k')) (GaloisField 2 2)) =
          Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * ones k')) F2) := by
        rw [← natCard_classBlk ε k' hk', ← hc,
          Subgroup.card_map_of_injective (K := J) (f := (MulAut.conj M⁻¹).toMonoidHom)
            (MulAut.conj M⁻¹).injective, hcardJ, ← hones]
      exact (natCard_sl_four_ne_sl_two (r := ones k') (s := n + 1 - 2 * ones k')
        hd hm rfl) heqorder
  · rintro ⟨eJ⟩
    have hcardJ : Nat.card ↥J =
        Nat.card (Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2)) :=
      Nat.card_congr eJ.toEquiv
    rcases hcase with hz | hc
    · exfalso
      have heqorder : Nat.card (Matrix.SpecialLinearGroup (Fin (n + 1 - 2 * ones k')) F2) =
          Nat.card (Matrix.SpecialLinearGroup (Fin (ones k')) (GaloisField 2 2)) := by
        rw [← natCard_zeroBlk ε k' hk', ← hz,
          Subgroup.card_map_of_injective (K := J) (f := (MulAut.conj M⁻¹).toMonoidHom)
            (MulAut.conj M⁻¹).injective, hcardJ, ← hones]
      exact (natCard_sl_four_ne_sl_two (r := ones k') (s := n + 1 - 2 * ones k')
        hd hm rfl) heqorder.symm
    · have hone : 1 ≤ ones k' := by
        by_contra hcon
        have h0 : ones k' = 0 := by omega
        have h1 : Nat.card ↥(classBlk ε k') = 1 := by
          rw [natCard_classBlk ε k' hk', h0]
          exact natCard_sl_le_one (K := GaloisField 2 2) (by omega)
        have h2 : Nat.card ↥J = 1 := by
          rw [← Subgroup.card_map_of_injective (K := J) (f := (MulAut.conj M⁻¹).toMonoidHom)
            (MulAut.conj M⁻¹).injective, hc]
          exact h1
        omega
      rw [htrans, hc, card_inter_centralizer_classBlk ε k' hk' hone, hones]


end CFSG.StandardType.CommonJRowLinTwo

end
