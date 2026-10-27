module

public import CFSG.Quasithin.Vol2.F134TitsData
public import CFSG.Quasithin.Vol2.F134TitsMatCode

public section

namespace CFSG.Quasithin.F134

@[expose] def titsCode (l : List ℕ) : ℕ := ofDigs (2 ^ 169) l

@[expose] def titsRhoB : ℕ := ofDigs (2 ^ 676) (titsRhoR.map titsCode)

@[expose] def titsRC (i : ℕ) : ℕ := digW 676 titsRhoB i

@[expose] def titsOrd (i : ℕ) : ℕ := titsRhoOrd.getD i 1

@[expose] def titsOneC : ℕ := titsCode titsOneR

@[expose] def titsPow (n x : ℕ) : ℕ := powC26 titsOneC n x

@[expose] def titsRInvC (i : ℕ) : ℕ := titsPow (titsOrd i - 1) (titsRC i)

@[expose] def titsTGB : ℕ := ofDigs (2 ^ 676) (titsTGenR.map titsCode)

@[expose] def titsTG (k : ℕ) : ℕ := digW 676 titsTGB k

@[expose] def titsXB : ℕ := ofDigs (2 ^ 676) (titsXR.map titsCode)

@[expose] def titsXC (p : ℕ) : ℕ := digW 676 titsXB p

@[expose] def titsTAB : ℕ := ofDigs (2 ^ 676) (titsTAR.map titsCode)

@[expose] def titsTAC (a : ℕ) : ℕ := digW 676 titsTAB a

@[expose] def titsTBB : ℕ := ofDigs (2 ^ 676) (titsTBR.map titsCode)

@[expose] def titsTBC (b : ℕ) : ℕ := digW 676 titsTBB b

@[expose] def titsNFC (e : ℕ) : ℕ := mulF26 (titsTAC (e % 64)) (titsTBC (e / 64))

@[expose] def titsSq (p : ℕ) : ℕ := titsSqL.getD p 0

@[expose] def titsCj (i j : ℕ) : ℕ := titsCjL.getD (11 * i + j) 0

@[expose] def titsTnf (k : ℕ) : ℕ := titsTnfL.getD k 0

@[expose] def titsRnf (i : ℕ) : ℕ := titsRnfL.getD (i - 2) 0

@[expose] def titsDB : ℕ := ofDigs (2 ^ 676) (titsDR.map titsCode)

@[expose] def titsDC (j : ℕ) : ℕ := digW 676 titsDB j

@[expose] def titsM (c : ℕ) : ℕ := (titsGRL.getD c []).length

@[expose] def titsR (c s : ℕ) : ℕ := (titsGRL.getD c []).getD s 0

@[expose] def titsCL (c e : ℕ) : ℕ := (titsGCL.getD c []).getD e 0

@[expose] def titsDec (c e : ℕ) : ℕ := (titsGDecL.getD c []).getD e 0

@[expose] def titsBad (j : ℕ) : ℕ := titsBadL.getD (j - 2) 0

@[expose] def titsWordC : List ℕ → ℕ
  | [] => titsOneC
  | i :: w => mulF26 (titsRC i) (titsWordC w)

@[expose] def titsTWordC : List ℕ → ℕ
  | [] => titsOneC
  | k :: w => mulF26 (titsTG k) (titsTWordC w)

end CFSG.Quasithin.F134
