module

public import CFSG.Sporadic.Co2Cert.Cert
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Sporadic.Co2InvData
import Certificates.Kernel.Co2Rank.Fix1
import Certificates.Kernel.Co2Rank.Fix2
import CFSG.Sporadic.Co2Cert.Faithful

public section

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Inv
  Matrix

namespace CertificateChecks.Batch129082

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Inv
  Matrix

private theorem foldl_lt {d v : ℕ} {R : Array ℕ} (hR : ∀ j : ℕ, R[j]?.getD 0 < 2 ^ d) :
    ∀ (l : List ℕ) (acc : ℕ), acc < 2 ^ d →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc < 2 ^ d
  | [], _, h => h
  | j :: l, acc, h => by
    rw [List.foldl_cons]
    apply foldl_lt hR l
    split_ifs
    · exact Nat.xor_lt_two_pow h (hR j)
    · exact h

private theorem vecMulN_lt (R : Array ℕ) (v : ℕ) : vecMulN 22 (transposeRows 22 R) v < 2 ^ 22 := by
  unfold vecMulN
  refine foldl_lt (fun j => ?_) _ 0 (by norm_num)
  unfold transposeRows
  rw [Array.getElem?_ofFn]
  split_ifs
  · exact ofBits_lt _ _
  · norm_num

private theorem card_fin_filter (n : ℕ) (g : ℕ → Bool) :
    (Finset.univ.filter fun p : Fin n => g p.val = true).card =
      (List.range n).countP g := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun p => if g p = true then 1 else 0) n,
    ← Finset.card_filter, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe]

private theorem card_fix (R : Array ℕ) :
    (Finset.univ.filter fun i : Fin 2300 => rowsMatrix 22 R *ᵥ co2Vec i = co2Vec i).card =
      (List.range 2300).countP (fun i =>
        vecMulN 22 (transposeRows 22 R) co2PackedVecs[i]! == co2PackedVecs[i]!) := by
  rw [← card_fin_filter]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  rw [co2Vec_eq i.2, rowsMatrix_mulVec, beq_iff_eq]
  exact ⟨fun h => toVecD_injective (vecMulN_lt _ _) (co2Packed_facts i.2).1 h,
    fun h => by rw [h]⟩

end CertificateChecks.Batch129082

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Inv Matrix in
theorem certificate129082 :
    (Finset.univ.filter fun i : Fin 2300 =>
      CFSG.Sporadic.SmallF2.rowsMatrix 22 co2InvReps[1]! *ᵥ co2Vec i = co2Vec i).card = 140 ∧
    (Finset.univ.filter fun i : Fin 2300 =>
      CFSG.Sporadic.SmallF2.rowsMatrix 22 co2InvReps[2]! *ᵥ co2Vec i = co2Vec i).card = 52 :=
  ⟨by rw [CertificateChecks.Batch129082.card_fix]; exact KernelCo2Rank.fix1,
    by rw [CertificateChecks.Batch129082.card_fix]; exact KernelCo2Rank.fix2⟩

end Certificates

end
