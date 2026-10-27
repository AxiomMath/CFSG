module

public import Certificates.Kernel.Co1SevenK.SylGlue
public import Certificates.Kernel.Co1SevenK.RepsK
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co1SevenOrderFourInputs

public section

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B
  CFSG.Sporadic.Co1Schreier.Native CertificateChecks.KernelSporSch.Co1Packed Timmesfeld.Co1Seven
  CFSG.HardMathSupport.Dickson.I271

local notation "U" => unpack 24 24

theorem sevenRepsOK_K : TabMSeven.sevenRepsOK aR bR = true := by
  unfold TabMSeven.sevenRepsOK
  dsimp only
  rw [rowAt_iS, rowAt_iT]
  exact kReps

theorem rowAt_lt {k : Nat} (hk : k < D.N) : rowAt (gDag aR bR).1 k = U (D.M k) := by
  rw [rowAt_eq, if_pos hk]

theorem rowsOrderFour_U {X : Nat} (h4 : Nat.beq (powWK X 4) idM = true)
    (h2 : (U (powWK X 2) != U idM) = true) : rowsOrderFour (U X) = true := by
  unfold rowsOrderFour
  rw [validRows_U, ← unpack_powWK, ← unpack_powWK, Nat.eq_of_beq_eq_true h4, ← MatL.unpack_idM]
  simp only [beq_self_eq_true, Bool.true_and, h2]

theorem orderFourOK_K : co1SevenOrderFourOK aR bR = true := by
  have h := kOrd4
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold co1SevenOrderFourOK
  dsimp only
  rw [rowAt_lt (by decide), rowAt_lt (by decide), rowAt_lt (by decide), ← unpack_powWK,
    ← unpack_powWK, mul_unpackW, Bool.and_eq_true]
  exact ⟨rowsOrderFour_U h1 h2, rowsOrderFour_U h3 h4⟩

end CertificateChecks.KernelCo1SevenK

end
