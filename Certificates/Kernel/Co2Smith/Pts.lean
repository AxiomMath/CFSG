module

public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Data.Kernel.Co2Smith.Pts
public import CFSG.Certificates.Kernel.Co1F2Sound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.SporSch.PosTable
public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith CFSG.KC.Enum
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Co2M CFSG.KC.M1F2
open CFSG.Sporadic.Co2Cert CertificateChecks.KernelSporSch.Co2M CFSG.KS CFSG.KS.Raw CFSG.KS.MatRep

theorem hpt : ∀ j < 2300, (co2PosTable[co2PackedVecs[j]!]!).toNat = j := by
  intro j hj
  unfold co2PosTable
  exact posTable_get good.nodup good.lt (by rw [V_size]; norm_num) (by rw [V_size]; exact hj)

theorem colAct_unpack (A v : Nat) : colAct (unpackR 22 A) v = vmF 22 (trK 22 A) v := by
  rw [colAct, tr_sound (Nat.beq_refl _), CFSG.KC.F2W.vecMulN_unpackR]

theorem bind_facts {A P : Nat} (h : bindVK (PV 0) P (trK 22 A) = true) {i : Nat} (hi : i < 2300) :
    pg 12 4095 P i < 2300 ∧ co2PackedVecs[pg 12 4095 P i]! = colAct (unpackR 22 A) co2PackedVecs[i]! := by
  have h1 := allN_spec h i hi
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  refine ⟨h1.1, ?_⟩
  rw [V_get h1.1, V_get hi, colAct_unpack]
  exact Nat.eq_of_beq_eq_true h1.2

theorem unpack12 {P i : Nat} (hi : i < 2300) : (unpack 2300 12 P)[i]! = pg 12 4095 P i := by
  rw [CFSG.KC.Misc.PairCount.unpack_get hi]
  rfl

theorem unpack_size12 (P : Nat) : (unpack 2300 12 P).size = 2300 := Array.size_ofFn

theorem permArr_eq {A P : Nat} (h : bindVK (PV 0) P (trK 22 A) = true) :
    glPermArr (unpackR 22 A) = unpack 2300 12 P := by
  have he : ∀ i (hi : i < 2300), (co2PosTable[colAct (unpackR 22 A) co2PackedVecs[i]!]!).toNat =
      pg 12 4095 P i := by
    intro i hi
    obtain ⟨hlt, hv⟩ := bind_facts h hi
    rw [← hv]
    exact hpt _ hlt
  refine Array.ext (by rw [glPermArr, Array.size_ofFn, unpack_size12]) (fun i h1 h2 => ?_)
  have hi : i < 2300 := by rwa [unpack_size12] at h2
  simp only [glPermArr, unpack, Array.getElem_ofFn, mask12]
  exact he i hi

theorem permOK_of {A P : Nat} (h : bindVK (PV 0) P (trK 22 A) = true) :
    glPermOK (unpackR 22 A) (glPermArr (unpackR 22 A)) = true := by
  rw [permArr_eq h]
  unfold glPermOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨unpack_size12 P, ?_⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [unpack12 hi]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact bind_facts h hi

theorem fixCount_eq (P : Nat) : glMkFixCount (unpack 2300 12 P) = fixCntK P := by
  have hf : ((List.range 2300).filter fun i => (unpack 2300 12 P)[i]! == i) =
      (List.range 2300).filter fun i => Nat.beq (pg 12 4095 P i) i := by
    apply List.filter_congr
    intro i hi
    rw [unpack12 (List.mem_range.1 hi)]
    by_cases e : pg 12 4095 P i = i
    · rw [e, Nat.beq_refl]
      exact beq_self_eq_true _
    · rw [beq_false e]
      exact beq_eq_false_iff_ne.2 e
  unfold glMkFixCount fixCntK
  rw [hf]

theorem fixIs_of {A P : Nat} (h : bindVK (PV 0) P (trK 22 A) = true) (k : Nat) :
    glMkFixIs (unpackR 22 A) k = (fixCntK P == k) := by
  unfold glMkFixIs
  simp only
  rw [permOK_of h, Bool.true_and, permArr_eq h, fixCount_eq]

end CertificateChecks.KernelCo2Smith
