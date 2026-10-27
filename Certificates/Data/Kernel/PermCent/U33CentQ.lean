module

public import Certificates.Data.Kernel.PermCent.U33Twin
public import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

@[expose] noncomputable def centQ (L : List (CV 28)) (s : CV 28) : List (CV 28) :=
  L.filter fun c => eq22C c s s c

@[expose] noncomputable def invCheckQ (L : List (CV 28)) (s : CV 28) : Bool :=
  let C := centQ L s
  let P := coreC C
  P.length == 16 &&
  C.all (fun t => !powOneC t 2 || P.any fun p => decide (p = t)) &&
  P.any fun q => eq22C q q s 1 && C.all (fun c => eq22C q c c q) &&
    P.all fun n => !(P.all fun m => eq22C n m m n) ||
      [1, q, q * q, q * q * q].any fun r => decide (r = n)

@[expose] noncomputable def centAtQ (s : CV 28) : Bool :=
  !powOneC s 2 || decide (s = 1) || invCheckQ (elemsC QP) s

@[expose] noncomputable def centBlkQ (j : Nat) : Bool :=
  (((elemsC QP).drop (j * 756)).take 756).all centAtQ

theorem centQ_eq (L : List (CV 28)) (s : CV 28) : centQ L s = centC L s := by
  simp only [centQ, centC, eq22C_eq]

theorem invCheckQ_eq (L : List (CV 28)) (s : CV 28) : invCheckQ L s = invCheckC L s := by
  simp only [invCheckQ, invCheckC, centQ_eq, eq22C_eq, mul_one, ← sq_fast]

theorem centAtQ_eq (s : CV 28) : centAtQ s = centAtC s := by
  simp only [centAtQ, centAtC, invCheckQ_eq, ← sq_fast]

theorem centBlkQ_eq (j : Nat) : centBlkQ j = centBlk j := by
  have h : centAtQ = centAtC := funext centAtQ_eq
  rw [centBlkQ, centBlk, h]

end CFSG.Certificates.Kernel.PkCV.U33T

end
