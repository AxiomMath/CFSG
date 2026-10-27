module

public import CFSG.Certificates.Kernel.BabyMonster.LatStats
public import Certificates.Kernel.BabyMonster.LatBind
public import Certificates.Data.Kernel.BabyMonster.LatText
public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles
public import CFSG.Certificates.Kernel.BabyMonster.CensusSound
public import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Ring
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.All

public section

namespace CertificateChecks.KernelBM.Lat

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.Monster.B.Dyadic.Native

theorem bitAt_eq (x i : Nat) : bitAt x i = x.testBit i := by
  rw [bitAt, Nat.testBit]
  have e1 : Nat.land (Nat.shiftRight x i) 1 = (x >>> i) % 2 := Nat.and_one_is_mod _
  have e2 : (1 &&& (x >>> i)) = (x >>> i) % 2 := Nat.one_and_eq_mod_two _
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> rw [h] <;> rfl

theorem zeroBits_sound {x : Nat} : ∀ {n : Nat}, zeroBits x n = true → ∀ i < n, bitAt x i = false
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : zeroBits x (n + 1) = andB (zeroBits x n) (notB (bitAt x n)) := rfl
    obtain ⟨h1, h2⟩ := andB_eq_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact zeroBits_sound h1 i hi
    · cases hb : bitAt x i
      · rfl
      · rw [hb] at h2
        exact absurd h2 Bool.false_ne_true

theorem fixed_bits : CFSG.Monster.B.Binary.Native.fixedVector.testBit 1197 = true ∧
    ∀ i < 1197, CFSG.Monster.B.Binary.Native.fixedVector.testBit i = false := by
  have h : fixedBitsOK = true := by quickRfl
  obtain ⟨h1, h2⟩ := andB_eq_true h
  refine ⟨(bitAt_eq _ _).symm.trans h1, fun i hi => ?_⟩
  rw [← bitAt_eq]
  exact zeroBits_sound h2 i hi

theorem count_eq {e : Array Nat} {N k : Nat} :
    ∀ n ≤ 4371, (∀ i < 4371, e[i]! = chAt N i - 48) →
      ((List.range n).map fun i => if e[i]! = k then 1 else 0).sum = digCountN N k n
  | 0, _, _ => rfl
  | n + 1, hn, he => by
    rw [List.range_succ, List.map_append, List.sum_append, count_eq n (by omega) he]
    change _ = digCountN N k n + Bool.rec 0 1 (Nat.beq (chAt N n - 48) k)
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, he n (by omega)]
    by_cases h : chAt N n - 48 = k
    · rw [ite_eq_left h, h, Nat.beq_refl]
    · rw [ite_eq_right h, Bool.eq_false_iff.2 (fun hc => h (Nat.eq_of_beq_eq_true hc))]

theorem defect_eq {e : Array Nat} {N : Nat} :
    ∀ n ≤ 4371, (∀ i < 4371, e[i]! = chAt N i - 48) →
      ((List.range n).map fun i => 7 - e[i]!).sum = digDefectN N n
  | 0, _, _ => rfl
  | n + 1, hn, he => by
    rw [List.range_succ, List.map_append, List.sum_append, defect_eq n (by omega) he]
    change _ = digDefectN N n + (7 - (chAt N n - 48))
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, he n (by omega)]

theorem stats_of_digits {e : Array Nat} {N : Nat} (he : ∀ i < 4371, e[i]! = chAt N i - 48)
    (h : statsOK N = true) :
    (List.range 8).map (expCountOf e) = [0, 12, 284, 993, 1782, 1035, 243, 22] ∧
      expDefectOf e = 13123 := by
  obtain ⟨h0, h⟩ := andB_eq_true h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h⟩ := andB_eq_true h
  obtain ⟨h7, h8⟩ := andB_eq_true h
  have c : ∀ k, expCountOf e k = digCountN N k 4371 := fun k => count_eq 4371 le_rfl he
  refine ⟨?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, c, Nat.eq_of_beq_eq_true h0,
      Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
      Nat.eq_of_beq_eq_true h7]
  · change ((List.range 4371).map fun i => 7 - e[i]!).sum = 13123
    rw [defect_eq 4371 le_rfl he]
    exact Nat.eq_of_beq_eq_true h8

theorem stats_text :
    (List.range 8).map (expCountOf (diagExpOf CFSG.Monster.B.LatText.text)) =
        [0, 12, 284, 993, 1782, 1035, 243, 22] ∧
      expDefectOf (diagExpOf CFSG.Monster.B.LatText.text) = 13123 := by
  have h : statsOK (getP CFSG.KD.LatBind.CH 0).1 = true := by quickRfl
  rw [text_eq]
  exact stats_of_digits (diagExpOf_eq CFSG.KD.LatBind.diag) h

end CertificateChecks.KernelBM.Lat

end
