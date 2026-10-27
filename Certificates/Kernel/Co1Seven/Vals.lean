module

public import Certificates.Kernel.Co1Seven.Bind
public import Certificates.Kernel.Co1Seven.Rest
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.Co1Three.TermSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.KS.Raw CFSG.Sporadic.Co1Schreier

theorem unpack_TS_A₁ : Native.aR = unpack 24 24 (TS 0) := by
  have h := CertificateChecks.KernelSporSch.Co1Packed.rows_of ch1023013bindA
  rw [Array.toArray_toList] at h
  rw [CertificateChecks.KernelSporSch.Co1ThreeLocal.aR_eq, h]

theorem unpack_TS_A₂ : Native.bR = unpack 24 24 (TS 1) := by
  have h := CertificateChecks.KernelSporSch.Co1Packed.rows_of ch1023013bindB
  rw [Array.toArray_toList] at h
  rw [CertificateChecks.KernelSporSch.Co1ThreeLocal.bR_eq, h]

theorem mRep_TS {R : Native.Rows} {k : Nat} {g : GL24} (hR : R = unpack 24 24 (TS k))
    (h : MRep R g) : matK (TS k) = g := by
  rw [← mRep_iff, CFSG.KS.SporSch.M24.unpackR_eq_unpack, ← hR]
  exact h

theorem matK_TS_A₁ : matK (TS 0) = A₁ :=
  mRep_TS unpack_TS_A₁ rep_A₁

theorem matK_TS_A₂ : matK (TS 1) = A₂ :=
  mRep_TS unpack_TS_A₂ rep_A₂

theorem matK_TS_one : matK (TS 2) = 1 :=
  (congrArg matK (Nat.eq_of_beq_eq_true
    (@CFSG.KS.SporSch.M24.MatS.bAnd_split (canAllK TS 3) (Nat.beq (TS 2) oneK)
      ch1023013seeds).2)).trans matK_oneK

theorem nodeIn_seeds : ∀ k < 3, NodeIn GA TS k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact ⟨A₁, A₁_mem, matK_TS_A₁⟩
  · exact ⟨A₂, A₂_mem, matK_TS_A₂⟩
  · exact ⟨1, GA.one_mem, matK_TS_one.trans (Units.val_one).symm⟩

end CertificateChecks.KernelCo1Seven

end
