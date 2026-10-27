module

public import CFSG.Quasithin.Vol2.F134RuData
public import CFSG.Quasithin.Vol2.F134RuDataD
public import CFSG.Quasithin.Vol2.F134RuDataDec
public import CFSG.Quasithin.Vol2.F134RuBridge

public section

namespace CFSG.Quasithin.F134

@[expose] def ruTGB : ℕ := ofDigs (2 ^ 784) (ruTGenR.map (ofDigs (2 ^ 196)))

@[expose] def ruTG (k : ℕ) : ℕ := digW 784 ruTGB k

@[expose] def ruXB : ℕ := ofDigs (2 ^ 784) (ruXR.map (ofDigs (2 ^ 196)))

@[expose] def ruXC (p : ℕ) : ℕ := digW 784 ruXB p

@[expose] def ruTAB : ℕ := ofDigs (2 ^ 784) (ruTAR.map (ofDigs (2 ^ 196)))

@[expose] def ruTAC (a : ℕ) : ℕ := digW 784 ruTAB a

@[expose] def ruTBB : ℕ := ofDigs (2 ^ 784) (ruTBR.map (ofDigs (2 ^ 196)))

@[expose] def ruTBC (b : ℕ) : ℕ := digW 784 ruTBB b

@[expose] def ruNFC (e : ℕ) : ℕ := mulF28 (ruTAC (e % 128)) (ruTBC (e / 128))

@[expose] def ruSq (p : ℕ) : ℕ := ruSqL.getD p 0

@[expose] def ruCj (i j : ℕ) : ℕ := ruCjL.getD (14 * i + j) 0

@[expose] def ruTnf (k : ℕ) : ℕ := ruTnfL.getD k 0

@[expose] def ruGB : ℕ := ofDigs (2 ^ 784) (ruGR.map (ofDigs (2 ^ 196)))

@[expose] def ruG (c : ℕ) : ℕ := digW 784 ruGB c

@[expose] def ruDB : ℕ := ofDigs (2 ^ 784) (ruDR.map (ofDigs (2 ^ 196)))

@[expose] def ruD (j : ℕ) : ℕ := digW 784 ruDB j

@[expose] def ruM (c : ℕ) : ℕ := (ruGRL.getD c []).length

@[expose] def ruR (c s : ℕ) : ℕ := (ruGRL.getD c []).getD s 0

@[expose] def ruCL (c e : ℕ) : ℕ := (ruGCL.getD c []).getD e 0

@[expose] def ruDecB (c : ℕ) : ℕ := ofDigs (2 ^ 40) (ruGDecL.getD c [])

@[expose] def ruDec (c e : ℕ) : ℕ := digW 40 (ruDecB c) e

@[expose] def ruBadB : ℕ := ofDigs (2 ^ 24) ruBadL

@[expose] def ruBad (j : ℕ) : ℕ := digW 24 ruBadB (j - 3)

@[expose] def ruCR (j r : ℕ) : ℕ := (ruCosR.getD (j - 1) []).getD r 0

@[expose] def ruCosE (j e : ℕ) : ℕ := (ruCosL.getD (j - 1) []).getD e 0

@[expose] def ruWordC : List ℕ → ℕ
  | [] => ruOneC
  | c :: w => mulF28 (if c = 0 then ruAC else ruBC) (ruWordC w)

@[expose] def ruTWordC : List ℕ → ℕ
  | [] => ruOneC
  | k :: w => mulF28 (ruTG k) (ruTWordC w)

@[expose] def ruLet (l : ℕ) : ℕ := if l < 16384 then ruNFC l else ruG (l - 16384)

@[expose] def ruLWordC : List ℕ → ℕ
  | [] => ruOneC
  | l :: w => mulF28 (ruLet l) (ruLWordC w)

end CFSG.Quasithin.F134
