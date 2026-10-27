module

public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.SporSch.Co1.Split
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T CertificateChecks.KernelSporSch.Co1Packed

theorem kBase : (Nat.beq (L.M 9) PA && Nat.beq (L.M 10) PB) = true := by quickRfl

theorem kA : allN 6 (fun i => Nat.beq (L.M i) (CertificateChecks.KernelSporSch.Co1Elem.AF i)) =
    true := by quickRfl

theorem kG : allN 3 (fun i => Nat.beq (L.M (Nat.add 6 i))
    (CertificateChecks.KernelSporSch.Co1Split.GF i)) = true := by quickRfl

theorem base_eq : [aR, bR] = (List.range 2).map fun i => unpack 24 24 (SM i) := by
  have h := kBase
  simp only [Bool.and_eq_true] at h
  rw [aR_u, bR_u, ← Nat.eq_of_beq_eq_true h.1, ← Nat.eq_of_beq_eq_true h.2]
  rfl

theorem sDag_eq : Native.sDag () = ((List.range 66).map fun i => unpack 24 24 (SM i),
    (List.range 66).map fun i => unpack 24 24 (SMI i), true) := by
  unfold Native.sDag
  exact dagWK_sound base_eq kS

theorem invL {k : Nat} (hk : k < 75) : invOKW (L.M k) (L.MI k) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact MatL.allN_iff.1 kI k h
  · have e := dagWK_inv kS (k - 9) (by omega)
    change invOKW (L.M (9 + (k - 9))) (L.MI (9 + (k - 9))) = true at e
    rwa [Nat.add_sub_cancel' h] at e

theorem lRows_eq : Native.lRows () = (List.range 75).map fun i => unpack 24 24 (L.M i) := by
  unfold Native.lRows
  rw [sDag_eq, CertificateChecks.KernelSporSch.Co1Elem.aRows_eq,
    CertificateChecks.KernelSporSch.Co1Split.gRows_eq]
  have e : (75 : Nat) = 6 + 3 + 66 := rfl
  rw [e, List.range_add, List.range_add, List.map_append, List.map_append, List.map_map,
    List.map_map]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (List.map_congr_left fun i hi => ?_)
    (List.map_congr_left fun i hi => ?_)) (List.map_congr_left fun i _ => rfl)
  · exact congrArg (unpack 24 24)
      (Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kA i (List.mem_range.1 hi))).symm
  · exact congrArg (unpack 24 24)
      (Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kG i (List.mem_range.1 hi))).symm

theorem lInvs_eq : Native.lInvs () = (List.range 75).map fun i => unpack 24 24 (L.MI i) := by
  unfold Native.lInvs
  rw [lRows_eq, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact (invOKW_sound (invL (List.mem_range.1 hi))).2

theorem wordL_eq {w : List Nat} (h : CFSG.KS.SporSch.M24.lettersK 75 w = true) :
    Native.wordL w = unpack 24 24 (wordWK L.M L.MI w) := by
  unfold Native.wordL
  rw [lRows_eq, lInvs_eq]
  exact word_eq_wordWK h

theorem rootK {j : Nat} (hj : j < 3) :
    CFSG.KS.SporSch.M24.lettersK 75 (Data.rootWords.getD j []) = true ∧
    Nat.beq (wordWK L.M L.MI (Data.rootWords.getD j [])) (R.M j) = true ∧
      invOKW (R.M j) (R.MI j) = true := by
  obtain ⟨h1, h⟩ := MatS.bAnd_split (MatL.allN_iff.1 kR j hj)
  exact ⟨h1, MatS.bAnd_split h⟩

theorem rootRows_eq {j : Nat} (hj : j < 3) : Native.rootRows j = unpack 24 24 (R.M j) := by
  obtain ⟨h1, h2, -⟩ := rootK hj
  unfold Native.rootRows
  rw [wordL_eq h1, Nat.eq_of_beq_eq_true h2]

end CertificateChecks.KernelCo1ThreeK

end
