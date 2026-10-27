
module

public import CFSG.Sporadic.HNOddCore.InvFixBase

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.XCheck
public import CFSG.Sporadic.HNOddCore.DCheck
public import CFSG.Sporadic.HNOddCore.Restrict
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

theorem x_parts :
    row1OK hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) cRec
      (posArr hnsData.n InvData.f1Arr) = true ∧
    row4OK hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) cRec
      (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.t4Word)
      (pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
        (natTab (hnsData.orbit ()).beta) InvData.x4Root)
        (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.x4H))
      (posArr hnsData.n InvData.f4Arr) = true ∧
    row6Run hnsData.n (natTab (hnsData.orbit ()).alpha) hStrongArr (pinvs hnsData.n hStrongArr)
      (progRun hnsData.n (initRegs hnsData.n (natTab (hnsData.orbit ()).alpha)
        (natTab (hnsData.orbit ()).beta)) InvData.m2Prog)
      (pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
        (natTab (hnsData.orbit ()).beta) InvData.m2ConjRoot)
        (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.m2ConjH)) = true ∧
    row2OK hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
      (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.t2Word) = true := by
  have h := x_cert
  unfold xChecksO xChecksR xChecksS at h
  rw [← hRegs_eq, ← hStrongArr_eq, cTab_eq] at h
  unfold xChecksH at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem data_parts :
    InvData.f1Arr.size = 1156 ∧ InvData.f4Arr.size = 800 ∧
    InvData.f6Arr.size = 8800 ∧ InvData.f1Arr[0]! = 0 ∧ InvData.f4Arr[0]! = 0 ∧
    InvData.f6Arr[0]! = 0 ∧ (InvData.o1Lists[0]!)[0]! = 0 ∧ (InvData.o6Lists[0]!)[0]! = 0 := by
  have h := data_cert
  unfold dataChecks fixSizesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end CFSG.Sporadic.HNOddCore
