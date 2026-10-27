module

public import Certificates.Data.Kernel.Co2Smith.Rows
public import Certificates.Kernel.Co2Smith.LettersData
public import CFSG.Sporadic.Co2Smith.GlDataRoots

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def cjK (b a : Nat) : Nat := mulV (mulV b a) b

@[expose] noncomputable def zK : Nat := wK LP [0]
@[expose] noncomputable def alK : Nat := wK LP [9]
@[expose] noncomputable def gaK : Nat := wK LP [10]
@[expose] noncomputable def x61K : Nat := wK LP glX61Word
@[expose] noncomputable def d0K : Nat := wK LP glD0hWord
@[expose] noncomputable def d1K : Nat := wK LP glD1hWord
@[expose] noncomputable def w1K : Nat := cjK zK x61K
@[expose] noncomputable def w2K : Nat := cjK d1K w1K
@[expose] noncomputable def w3K : Nat := cjK d0K w2K
@[expose] noncomputable def x52K : Nat := cjK d1K x61K
@[expose] noncomputable def x43K : Nat := cjK d0K x52K
@[expose] noncomputable def x25K : Nat := cjK d1K zK
@[expose] noncomputable def x34K : Nat := cjK d0K x25K
@[expose] noncomputable def w0K : Nat := mulV (mulV w1K w2K) w3K
@[expose] noncomputable def uK : Nat := wK LP glUWord

@[expose] noncomputable def gdK : Nat := mulV gaK d1K
@[expose] noncomputable def dgK : Nat := mulV d1K gaK

@[expose] noncomputable def x24K (t : Nat) : Nat := mulV (mulV gdK (wK LP (glPosNF[1]!)[t]!)) dgK

@[expose] noncomputable def posK (i t : Nat) : Nat :=
  if t == 0 then IDP
  else if i < 4 then wK LP (glPosNF[i]!)[t]!
  else if i == 4 then x24K t
  else cjK w3K (x24K t)

@[expose] noncomputable def longK (k : Nat) : Nat :=
  if k == 0 then zK else if k == 1 then x25K else if k == 2 then x34K
  else if k == 3 then x61K else if k == 4 then x52K else x43K

@[expose] noncomputable def rootK (r t : Nat) : Nat :=
  if t == 0 then IDP
  else if r < 6 then posK r t
  else if r < 12 then cjK w0K (posK (r - 6) t)
  else longK (r - 12)

@[expose] noncomputable def prodK (l : List (Nat × Nat)) : Nat :=
  l.foldr (fun p acc => mulV (rootK p.1 p.2) acc) IDP

@[expose] noncomputable def comm4K (X Y : Nat) : Nat := mulV (mulV (mulV X Y) X) Y

@[expose] noncomputable def frameConjK (k : Nat) : Nat :=
  if k == 0 then IDP else if k == 1 then d1K else if k == 2 then mulV d1K d0K
  else if k == 3 then w1K else if k == 4 then mulV w1K d1K
  else mulV (mulV w1K d1K) d0K

end CertificateChecks.KernelCo2Smith
