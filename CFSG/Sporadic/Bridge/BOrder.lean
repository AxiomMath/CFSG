module

public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Monster.B.Final.Max2Nodes
public import CFSG.Monster.B.Pinned.Primes.FiveSubgroup
public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.Monster.B.Pinned.Primes.ThreeTwelve
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.BSeven
public import CFSG.Sporadic.Bridge.BOrderInputs
public import Certificates.Certificate16002
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3159
public import Certificates.Certificate3160
public import Certificates.Certificate3161
public import CFSG.Monster.Existence.BabyOrder
public import Certificates.Certificate16008
public import Certificates.Certificate16027
public import Certificates.Certificate3027
public import Certificates.Certificate15954
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import CFSG.Monster.B.TwoA.Unitary.Action

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native
open scoped Matrix

@[expose] noncomputable def genK (i : ℕ) : GL (Fin 8) (ZMod 3) :=
  if i = 0 then XThreeU else if i = 1 then YThreeU else 1

theorem genK_mem (i : ℕ) : genK i ∈ KThree := by
  unfold genK
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact one_mem _

theorem coe_genK_letter (l : ℕ × Bool) (h : l.1 < 2) :
    (((if l.2 then genK l.1 else (genK l.1)⁻¹ : GL (Fin 8) (ZMod 3))) :
      Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 (genRows l.1 l.2) := by
  obtain ⟨i, b⟩ := l
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> cases b <;> rfl

theorem genRows_length (i : ℕ) (b : Bool) : (genRows i b).length = 8 := by
  unfold genRows
  split_ifs <;> rfl

theorem wordRows_length_aux (w : List (ℕ × Bool)) (acc : List (List ℕ)) (h : acc.length = 8) :
    (w.foldl (fun acc l => lmul acc (genRows l.1 l.2)) acc).length = 8 := by
  induction w generalizing acc with
  | nil => exact h
  | cons l w ih => exact ih _ (by rw [lmul_length, h])

theorem coe_wordProd_K (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 2) :
    ((wordProd genK w : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      rowsMat 3 8 (wordRows w) := by
  unfold wordRows wordProd
  suffices ∀ (acc : List (List ℕ)) (g : GL (Fin 8) (ZMod 3)), acc.length = 8 →
      (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 acc →
      ((g * (w.map fun l => if l.2 then genK l.1 else (genK l.1)⁻¹).prod :
        GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
        rowsMat 3 8 (w.foldl (fun acc l => lmul acc (genRows l.1 l.2)) acc) by
    have h := this (lpow threeXRows 0) 1 (lpow_length _ 0) (by
      rw [Units.val_one, rowsMat_lpow, pow_zero])
    rwa [one_mul] at h
  induction w with
  | nil => intro acc g _ hg; simpa using hg
  | cons l w ih =>
    intro acc g hacc hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) (lmul acc (genRows l.1 l.2))
      _ (by rw [lmul_length, hacc])
    rw [Units.val_mul, hg, coe_genK_letter l (hw l List.mem_cons_self), rowsMat_lmul hacc]

theorem w1_lt : ∀ l ∈ w1, l.1 < 2 :=
  Certificates.certificate16002.1

theorem w2_lt : ∀ l ∈ w2, l.1 < 2 :=
  Certificates.certificate16002.2.1

theorem rows_facts :
    lpow (wordRows w1) 3 = lpow (wordRows w1) 0 ∧ lpow (wordRows w2) 3 = lpow (wordRows w2) 0 ∧
    lvecMul 3 8 orbitBase (wordRows w1) = orbitBase ∧
    lvecMul 3 8 orbitBase (wordRows w2) = orbitBase ∧
    lmul (wordRows w1) (wordRows w2) = lmul (wordRows w2) (wordRows w1) ∧
    rowsMat 3 8 (wordRows w1) ≠ 1 ∧ rowsMat 3 8 (wordRows w2) ≠ 1 ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (wordRows w1) ∧
    rowsMat 3 8 (wordRows w2) ≠ rowsMat 3 8 (lpow (wordRows w1) 2) :=
  Certificates.certificate16002.2.2

theorem wordRows_length (w : List (ℕ × Bool)) : (wordRows w).length = 8 :=
  wordRows_length_aux w _ (lpow_length _ 0)

theorem coe_pow_of_rows {s : GL (Fin 8) (ZMod 3)} {R : List (List ℕ)}
    (hc : (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 R) (e : ℕ) :
    ((s ^ e : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      rowsMat 3 8 (lpow R e) := by
  rw [Units.val_pow_eq_pow_val, hc, rowsMat_lpow]

theorem pow_three_of_rows {s : GL (Fin 8) (ZMod 3)} {R : List (List ℕ)}
    (hc : (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 R) (h : lpow R 3 = lpow R 0) :
    s ^ 3 = 1 := by
  apply Units.ext
  rw [coe_pow_of_rows hc, h, ← coe_pow_of_rows hc, pow_zero]

theorem fix_of_rows {s : GL (Fin 8) (ZMod 3)} {R : List (List ℕ)}
    (hc : (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 R)
    (h : lvecMul 3 8 orbitBase R = orbitBase) :
    vThree ᵥ* (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree := by
  rw [hc, vThree_eq, ← rowsVec_lvecMul, h]

@[expose] noncomputable def s1 : KThree := ⟨wordProd genK w1, wordProd_mem genK_mem w1⟩

@[expose] noncomputable def s2 : KThree := ⟨wordProd genK w2, wordProd_mem genK_mem w2⟩

theorem coe_s1 :
    ((s1 : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
    rowsMat 3 8 (wordRows w1) :=
  coe_wordProd_K w1 w1_lt

theorem coe_s2 :
    ((s2 : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
    rowsMat 3 8 (wordRows w2) :=
  coe_wordProd_K w2 w2_lt

theorem mem_stabilizer_of_fix (g : KThree)
    (h : vThree ᵥ* ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree) :
    g ∈ MulAction.stabilizer KThree vRow := by
  rw [MulAction.mem_stabilizer_iff]
  apply RowV.ext
  rw [vec_smul]
  show vThree ᵥ* (((g : GL (Fin 8) (ZMod 3))⁻¹ : GL (Fin 8) (ZMod 3)) :
    Matrix (Fin 8) (Fin 8) (ZMod 3)) = vThree
  conv_lhs => rw [← h]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem three_four_dvd_card_KThree : 3 ^ 4 ∣ Nat.card KThree := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hidx := MulAction.index_stabilizer KThree vRow
  rw [ncard_orbit_vRow] at hidx
  have hcard := (MulAction.stabilizer KThree vRow).card_mul_index
  rw [hidx] at hcard
  obtain ⟨hc3a, hc3b, hfa, hfb, hcomm, hne1, hne2, hne21, hne2sq⟩ := rows_facts
  have h1 : (s1 : GL (Fin 8) (ZMod 3)) ^ 3 = 1 := pow_three_of_rows coe_s1 hc3a
  have h2 : (s2 : GL (Fin 8) (ZMod 3)) ^ 3 = 1 := pow_three_of_rows coe_s2 hc3b
  have hK1 : s1 ^ 3 = 1 := Subtype.ext (by simpa using h1)
  have hK2 : s2 ^ 3 = 1 := Subtype.ext (by simpa using h2)
  have hcommK : s1 * s2 = s2 * s1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_s1, coe_s2,
      ← rowsMat_lmul (wordRows_length _), ← rowsMat_lmul (wordRows_length _), hcomm]
  have hs1 : s1 ≠ 1 := fun h => hne1 (by rw [← coe_s1, h]; rfl)
  have hs21 : s2 ≠ s1 := fun h => hne21 (by rw [← coe_s1, ← coe_s2, h])
  have hyx : ∀ k : ℕ, k < 3 → s2 ≠ s1 ^ k := by
    intro k hk h
    interval_cases k
    · exact hne2 (by rw [← coe_s2, h]; rfl)
    · exact hs21 (by simpa using h)
    · apply hne2sq
      have := congrArg (fun g : KThree => ((g : GL (Fin 8) (ZMod 3)) :
        Matrix (Fin 8) (Fin 8) (ZMod 3))) h
      rw [Subgroup.coe_pow, coe_pow_of_rows coe_s1, coe_s2] at this
      exact this
  have hst1 : s1 ∈ MulAction.stabilizer KThree vRow :=
    mem_stabilizer_of_fix s1 (fix_of_rows coe_s1 hfa)
  have hst2 : s2 ∈ MulAction.stabilizer KThree vRow :=
    mem_stabilizer_of_fix s2 (fix_of_rows coe_s2 hfb)
  have h9 : 3 ^ 2 ∣ Nat.card (MulAction.stabilizer KThree vRow) :=
    prime_sq_dvd_card_subgroup _ hst1 hst2 hK1 hK2 hcommK hs1 hyx
  rw [← hcard, show (3 : ℕ) ^ 4 = 3 ^ 2 * 3 ^ 2 by norm_num]
  exact Nat.mul_dvd_mul h9 (by norm_num)

theorem three_pow_thirteen_dvd :
    3 ^ 13 ∣ Nat.card NativeSporadic.B := by
  have := finite_B
  have h1 : Nat.card rhoThree.ker * Nat.card rhoThree.range = Nat.card LThree := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : 3 ^ 9 ∣ Nat.card rhoThree.ker := by
    have := Subgroup.card_dvd_of_le QThree_le_ker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QThree_le_LThree).toEquiv,
      card_QThree] at this
  have h3 : 3 ^ 4 ∣ Nat.card rhoThree.range := by
    rw [range_rhoThree]
    exact three_four_dvd_card_KThree
  have hL : 3 ^ 13 ∣ Nat.card LThree := by
    rw [← h1, show (3 : ℕ) ^ 13 = 3 ^ 9 * 3 ^ 4 by norm_num]
    exact Nat.mul_dvd_mul h2 h3
  exact hL.trans (Subgroup.card_subgroup_dvd_card LThree)

theorem exists_explicitBinary :
    ∃ β : Cbar →* GL (Fin 4370) (ZMod 2), IsExplicitBinary β :=
  ⟨_, betaS_explicit⟩

theorem two_pow_41_dvd :
    2 ^ 41 ∣ Nat.card NativeSporadic.B := by
  obtain ⟨β, hβ⟩ := exists_explicitBinary
  obtain ⟨ι, -, hιβ, -⟩ := iota_facts hβ
  exact (pinned_B_max2_full_native_centralizer_and_two_part hβ ι hιβ).2.2.1

theorem small_primes_dvd :
    2 * 3 * 5 * 11 * 23 ∣ Nat.card NativeSporadic.B := by
  obtain ⟨β, hβ⟩ := exists_explicitBinary
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := pinned_B_explicit_embedding hβ
  exact h

theorem five_pow_6_dvd :
    5 ^ 6 ∣ Nat.card NativeSporadic.B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := pinned_B_five_power_six_subgroup
  exact h

theorem six_primes_dvd :
    7 * 13 * 17 * 19 * 31 * 47 ∣ Nat.card NativeSporadic.B := by
  rw [CFSG.Monster.Existence.card_nativeB]
  unfold CFSG.Open.monsterBabyOrder
  norm_num

theorem order_dvd
    : 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 ∣
    Nat.card NativeSporadic.B := by
  rw [CFSG.Monster.Existence.card_nativeB]
  unfold CFSG.Open.monsterBabyOrder
  exact dvd_rfl

theorem card_B_pos : 0 < Nat.card NativeSporadic.B := by
  have := finite_B
  exact Nat.card_pos

theorem card_le_card_B
    : 4154781481226426191177580544000000 ≤ Nat.card NativeSporadic.B := by
  have := Nat.le_of_dvd card_B_pos order_dvd
  norm_num at this
  exact this

end CFSG.Sporadic.Bridge.B
