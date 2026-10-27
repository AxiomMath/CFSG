module

public import CFSG.RankThree.SubgroupLists.MitchellDicksonTwo
public import CFSG.RankThree.SubgroupLists.MitchellIsoCent
public import CFSG.RankThree.SubgroupLists.MitchellIsoLevi
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

section TwoByTwo

variable {K : Type} [Field K]

private theorem pow_eq_one_add_smul {U : Matrix (Fin 2) (Fin 2) K} (hN : (U - 1) * (U - 1) = 0)
    (m : ℕ) : U ^ m = 1 + (m : K) • (U - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hNU : (U - 1) * U = U - 1 := by
      calc (U - 1) * U = (U - 1) * (U - 1) + (U - 1) := by noncomm_ring
        _ = U - 1 := by rw [hN, zero_add]
    rw [pow_succ, ih, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hNU, Nat.cast_succ]
    module

private theorem torus_conj_mat {d : K} (hd : 2 * d = 1) :
    Matrix.diagonal ![(2 : K), d] * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] ^ 4 * Matrix.diagonal ![2, d] := by
  have hU4 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) ^ 4 = !![1, 4; 0, 1] := by
    rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]
    simp only [Matrix.mul_fin_two]
    norm_num
  rw [hU4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -2 * hd

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

private theorem trace_eq_two_of_pow_prime_eq_one {U : Matrix (Fin 2) (Fin 2) K}
    (hdet : U.det = 1) (hU : U ^ p = 1) : U.trace = 2 ∧ (U - 1) * (U - 1) = 0 := by
  have hNp : (U - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right U), hU, one_pow, sub_self]
  have hCH := fin_two_mul_self U
  rw [hdet, one_smul] at hCH
  have hsq : (U - 1) * (U - 1) = (U.trace - 2) • U := by
    have e : (U - 1) * (U - 1) = U * U - (2 : K) • U + 1 := by
      rw [two_smul]
      noncomm_ring
    rw [e, hCH]
    module
  have ht : U.trace = 2 := by
    by_contra hs
    have hU' : U = (U.trace - 2)⁻¹ • ((U - 1) * (U - 1)) := by
      rw [hsq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hs), one_smul]
    have h0 : U ^ p = 0 := by
      rw [hU', smul_pow, (Commute.refl (U - 1)).mul_pow, hNp, zero_mul, smul_zero]
    rw [hU] at h0
    exact one_ne_zero h0
  exact ⟨ht, by rw [hsq, ht, sub_self, zero_smul]⟩

private theorem borel_core {U X X' : Matrix (Fin 2) (Fin 2) K} (h2 : (2 : K) ≠ 0)
    (hXX' : X * X' = 1) (hX'X : X' * X = 1) (hXdet : X.det = 1)
    (hVdet : (X * U * X').det = 1) (htr : U.trace = 2) (hN2 : (U - 1) * (U - 1) = 0)
    (hU1 : U ≠ 1) {ε : K} (hVU : X * U * X' * U = ε • (U * (X * U * X'))) :
    ∃ β : K, X * U * X' = 1 + β • (U - 1) ∧ (β * β = 1 → X ^ (4 * p) = 1) := by
  have hNsc : ∀ c : K, U - 1 ≠ c • 1 := by
    intro c hc
    rw [hc, smul_mul_smul_comm, Matrix.one_mul] at hN2
    have hc0 : c * c = 0 := by simpa using congrFun (congrFun hN2 0) 0
    exact hU1 (sub_eq_zero.mp (by rw [hc, mul_self_eq_zero.mp hc0, zero_smul]))
  have htrN : (U - 1).trace = 0 := by
    rw [Matrix.trace_sub, htr, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hVtr : (X * U * X').trace = 2 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hX'X, Matrix.one_mul, htr]
  have hVV := fin_two_mul_self (X * U * X')
  rw [hVtr, hVdet, one_smul] at hVV
  have hW : X * U * X' * ((2 : K) • 1 - X * U * X') = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hVV]
    abel
  have hW' : ((2 : K) • 1 - X * U * X') * (X * U * X') = 1 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hVV]
    abel
  have hε : ε = 1 := by
    have key : X * U * X' * U * ((2 : K) • 1 - X * U * X') = ε • U := by
      rw [hVU, Matrix.smul_mul, Matrix.mul_assoc U, hW, Matrix.mul_one]
    have h' := congrArg Matrix.trace key
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW', Matrix.one_mul, Matrix.trace_smul, htr,
      smul_eq_mul] at h'
    have h'' : (ε - 1) * 2 = 0 := by linear_combination -h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h'').resolve_right h2)
  rw [hε, one_smul] at hVU
  have hVN : X * U * X' * (U - 1) = (U - 1) * (X * U * X') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hVU, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_smul_of_commute hNsc hVN
  have hα : α = 1 := by
    have h' := congrArg Matrix.trace hαβ
    rw [hVtr, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htrN, Matrix.trace_one,
      Fintype.card_fin, smul_zero, add_zero, smul_eq_mul] at h'
    have h'' : (α - 1) * 2 = 0 := by push_cast at h'; linear_combination -h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h'').resolve_right h2)
  rw [hα, one_smul] at hαβ
  refine ⟨β, hαβ, fun hb => ?_⟩
  have hM : X * (U - 1) * X' = β • (U - 1) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hXX', hαβ]
    abel
  have hXN : X * (U - 1) = β • ((U - 1) * X) := by
    calc X * (U - 1) = X * (U - 1) * X' * X := by rw [Matrix.mul_assoc _ X', hX'X, Matrix.mul_one]
      _ = β • ((U - 1) * X) := by rw [hM, Matrix.smul_mul]
  have hXXN : X * X * (U - 1) = (U - 1) * (X * X) := by
    calc X * X * (U - 1) = X * (X * (U - 1)) := Matrix.mul_assoc _ _ _
      _ = (β * β) • ((U - 1) * (X * X)) := by
        rw [hXN, Matrix.mul_smul, ← Matrix.mul_assoc X (U - 1) X, hXN, Matrix.smul_mul, smul_smul,
          Matrix.mul_assoc (U - 1) X X]
      _ = (U - 1) * (X * X) := by rw [hb, one_smul]
  obtain ⟨a, b, hab⟩ := exists_eq_add_smul_of_commute hNsc hXXN
  have hNp : (U - 1) ^ p = 0 := pow_eq_zero_of_le hp.out.two_le (by rw [sq]; exact hN2)
  have hX2p : (X * X) ^ p = a ^ p • 1 := by
    rw [hab, add_pow_char_of_commute p (((Commute.one_left (U - 1)).smul_left a).smul_right b),
      smul_pow, smul_pow, hNp, smul_zero, add_zero, one_pow]
  have hs : (a ^ p) ^ 2 = 1 := by
    have h' := congrArg Matrix.det hX2p
    rw [Matrix.det_pow, Matrix.det_mul, hXdet, mul_one, one_pow, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin] at h'
    exact h'.symm
  calc X ^ (4 * p) = ((X * X) ^ p) ^ 2 := by
        rw [show 4 * p = 2 * p * 2 by ring, pow_mul, pow_mul, sq X]
    _ = 1 := by rw [hX2p, smul_pow, one_pow, hs, one_smul]

end TwoByTwo

theorem false_of_isoLeviImage_eq_top {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) (htop : isoLeviImage (ZMod p) G = ⊤) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd (by norm_num)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h0))
    omega
  obtain ⟨d, hd⟩ : ∃ d : ZMod p, 2 * d = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2⟩
  have hmem : ∀ A : SL(2, ZMod p), ∃ w ∈ G, w ∈ isoCent (ZMod p) ∧
      leviBlock (w : Matrix V₄ V₄ (ZMod p)) = (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := fun A =>
    exists_leviBlock_eq_of_mem hneg (by rw [htop]; exact Subgroup.mem_top _)
  obtain ⟨g, hgG, hgC, hg⟩ : ∃ w ∈ G, w ∈ isoCent (ZMod p) ∧
      leviBlock (w : Matrix V₄ V₄ (ZMod p)) = !![1, 1; 0, 1] :=
    hmem ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨h, hhG, hhC, hh⟩ : ∃ w ∈ G, w ∈ isoCent (ZMod p) ∧
      leviBlock (w : Matrix V₄ V₄ (ZMod p)) = Matrix.diagonal ![2, d] :=
    hmem ⟨Matrix.diagonal ![2, d], by simpa [Matrix.det_diagonal, Fin.prod_univ_two] using hd⟩
  have hconj : h * g * h⁻¹ = g ^ 4 := by
    rw [mul_inv_eq_iff_eq_mul]
    refine eq_of_leviBlock_eq hU0 (G.mul_mem hhG hgG) (G.mul_mem (G.pow_mem hgG 4) hhG)
      (mul_mem hhC hgC) (mul_mem (pow_mem hgC 4) hhC) ?_
    rw [leviBlock_val_mul _ hgC, leviBlock_val_mul _ hhC, leviBlock_val_pow hgC, hg, hh]
    exact torus_conj_mat hd
  have hhk : h ^ (p - 1) = 1 := by
    refine eq_of_leviBlock_eq hU0 (G.pow_mem hhG _) G.one_mem (pow_mem hhC _) (one_mem _) ?_
    rw [leviBlock_val_pow hhC, hh, Units.val_one, leviBlock_one, Matrix.diagonal_pow,
      ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp [ZMod.pow_card_sub_one_eq_one h2]
    · simp [ZMod.pow_card_sub_one_eq_one (right_ne_zero_of_mul_eq_one hd)]
  have hg1 : g ≠ 1 := by
    rintro rfl
    simpa [leviBlock] using congrFun (congrFun hg 0) 1
  have htr : (leviBlock (g : Matrix V₄ V₄ (ZMod p))).trace = 2 := by
    rw [hg, Matrix.trace_fin_two_of]
    norm_num
  have hpk : ¬ p ∣ p - 1 := fun h' => by
    have := Nat.le_of_dvd (by omega) h'
    omega
  have hm : ((4 : ℕ) : ZMod p) ^ 2 ≠ 1 := by
    intro h16
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h16
    have h15 : p ∣ 3 * 5 := (Nat.modEq_iff_dvd' (by norm_num)).mp h16.symm
    rcases (Nat.Prime.dvd_mul hp.out).mp h15 with h' | h' <;>
      have := Nat.le_of_dvd (by norm_num) h' <;> omega
  exact false_of_isoCent_conj_pow (by omega) hU0 hgG hgC hhC hg1 htr hhk hpk hconj hm

theorem false_of_isoCent_normalizes {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {g x : GL V₄ (ZMod p)} (hgG : g ∈ G) (hxG : x ∈ G)
    (hgC : g ∈ isoCent (ZMod p)) (hxC : x ∈ isoCent (ZMod p)) (hgp : g ^ p = 1) (hg1 : g ≠ 1)
    {k : ℕ} (hk : x ^ k = 1) (hpk : ¬ p ∣ k) (hx4 : x ^ 4 ≠ 1)
    (hcomm : ∃ ε : ZMod p, ε * ε = 1 ∧
      leviBlock ((x * g * x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *
          leviBlock (g : Matrix V₄ V₄ (ZMod p)) =
        ε • (leviBlock (g : Matrix V₄ V₄ (ZMod p)) *
          leviBlock ((x * g * x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)))) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd (by norm_num)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h0))
    omega
  have hcC : x * g * x⁻¹ ∈ isoCent (ZMod p) := mul_mem (mul_mem hxC hgC) (inv_mem hxC)
  have hcG : x * g * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hxG hgG) (G.inv_mem hxG)
  have hV : leviBlock ((x * g * x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) =
      leviBlock (x : Matrix V₄ V₄ (ZMod p)) * leviBlock (g : Matrix V₄ V₄ (ZMod p)) *
        leviBlock ((x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) := by
    rw [leviBlock_val_mul _ (inv_mem hxC), leviBlock_val_mul _ hgC]
  have hXX' : leviBlock (x : Matrix V₄ V₄ (ZMod p)) *
      leviBlock ((x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) = 1 := by
    rw [← leviBlock_val_mul _ (inv_mem hxC), mul_inv_cancel, Units.val_one, leviBlock_one]
  have hX'X : leviBlock ((x⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *
      leviBlock (x : Matrix V₄ V₄ (ZMod p)) = 1 := by
    rw [← leviBlock_val_mul _ hxC, inv_mul_cancel, Units.val_one, leviBlock_one]
  have hUp : leviBlock (g : Matrix V₄ V₄ (ZMod p)) ^ p = 1 := by
    rw [← leviBlock_val_pow hgC, hgp, Units.val_one, leviBlock_one]
  obtain ⟨htr, hN2⟩ := trace_eq_two_of_pow_prime_eq_one (det_leviBlock hgC) hUp
  have hU1 : leviBlock (g : Matrix V₄ V₄ (ZMod p)) ≠ 1 := fun h =>
    hg1 (hU0 g hgG (isSqZero_of_leviBlock_eq_one hgC h))
  obtain ⟨ε, -, hVU⟩ := hcomm
  rw [hV] at hVU
  obtain ⟨β, hβV, hβ⟩ := borel_core h2 hXX' hX'X (det_leviBlock hxC)
    (by rw [← hV]; exact det_leviBlock hcC) htr hN2 hU1 hVU
  have hconj : x * g * x⁻¹ = g ^ β.val := by
    refine eq_of_leviBlock_eq hU0 hcG (G.pow_mem hgG _) hcC (pow_mem hgC _) ?_
    rw [hV, hβV, leviBlock_val_pow hgC, pow_eq_one_add_smul hN2, ZMod.natCast_zmod_val]
  by_cases hb : β * β = 1
  · apply hx4
    have hx4p : x ^ (4 * p) = 1 := hU0 _ (G.pow_mem hxG _)
      (isSqZero_of_leviBlock_eq_one (pow_mem hxC _) (by rw [leviBlock_val_pow hxC]; exact hβ hb))
    have hco : Nat.Coprime (orderOf x) p := Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hk) (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
        hp.out).mpr hpk))
    exact orderOf_dvd_iff_pow_eq_one.mp (hco.dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one hx4p))
  · exact false_of_isoCent_conj_pow hp5 hU0 hgG hgC hxC hg1 htr hk hpk hconj
      (by rw [ZMod.natCast_zmod_val, sq]; exact hb)

end CFSG.RankThree.SubgroupLists
