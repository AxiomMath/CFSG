module

public import Certificates.Data.Kernel.AS91K468.K46

public section

noncomputable section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

@[expose] def closL (fs : List (ℕ → ℕ)) : ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, fr, _, vis => fr ++ vis
  | fuel + 1, fr, S, vis =>
    let r := roundN fs fr (ofListP S)
    if r.1.isEmpty then fr ++ vis else closL fs fuel r.1 (r.1 ++ S) (fr ++ vis)

@[expose] def fsOf (PF : List (ℕ × ℕ)) : List (ℕ → ℕ) := PF.map fun rf F => F &&& rf.2

@[expose] def roundOK (PF : List (ℕ × ℕ)) (fr S fr' : List ℕ) : Bool :=
  (roundN (fsOf PF) fr (ofListP S)).1 == fr' && !fr'.isEmpty

@[expose] def roundEnd (PF : List (ℕ × ℕ)) (fr S : List ℕ) : Bool :=
  (roundN (fsOf PF) fr (ofListP S)).1.isEmpty

@[expose] def jAll1 (PF : List (ℕ × ℕ)) (L Fs : List ℕ) : Bool :=
  Fs.all fun F => PF.all fun rf => memP (ofListP L) (F &&& rf.2)

@[expose] def jAll2 (PF : List (ℕ × ℕ)) (Fs : List ℕ) : Bool := Fs.all (jFQ PF w1M)

end Certificates.Kernel.AS91K468

end

end
