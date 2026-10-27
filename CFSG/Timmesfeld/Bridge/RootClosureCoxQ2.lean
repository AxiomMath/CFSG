module

public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure.CoxQ2

@[expose] noncomputable def edgeBlk0 : ℕ := 0x945209502803a88a1040ced90b49639c6fa283d266550292554475329e64449413210d442328ef088330250661462ac1148884219c004448000880
@[expose] noncomputable def edgeBlk (_b : ℕ) : ℕ :=
  edgeBlk0
@[expose] noncomputable def edge (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edgeBlk (Nat.shiftRight i 11))
    (Nat.mul 11 (Nat.land i 2047))) 2047
@[expose] noncomputable def fx (f : ℕ) : ℕ :=
  Nat.land (edge f) 15
@[expose] noncomputable def fc (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edge f) 4) 7
@[expose] noncomputable def fy (f : ℕ) : ℕ :=
  Nat.shiftRight (edge f) 7

@[expose] noncomputable def justBlk0 : ℕ := 0x34081aca205b1001abe005add00eb080caaa042a2e03a6a03e9520ea29836826039f392e6d4ea9a50825c829952092508218000004ce20904aa23d2218c209e2c8228000002862080000024421800000204228000001ca22850892102218000000c220800000080218000000402080000000022800000
@[expose] noncomputable def justBlk (_b : ℕ) : ℕ :=
  justBlk0
@[expose] noncomputable def just (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (justBlk (Nat.shiftRight i 11))
    (Nat.mul 22 (Nat.land i 2047))) 4194303
@[expose] noncomputable def kind (f : ℕ) : ℕ := Nat.land (just f) 3
@[expose] noncomputable def wi (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 2) 31
@[expose] noncomputable def ft (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 7) 15
@[expose] noncomputable def fs (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 11) 15
@[expose] noncomputable def fo (f : ℕ) : ℕ :=
  Nat.shiftRight (just f) 15

@[expose] noncomputable def refsBlk0 : ℕ := 0x13180098cc046380231f00e220f0114c008a6c02e861c026866403e8201faa7a7c0227ab400068e802e483000634d80364cb0e1a00c132a00c003000b001c082912800a06122c8802400900200070018005000a004001000300080010000
@[expose] noncomputable def refsBlk (_b : ℕ) : ℕ :=
  refsBlk0
@[expose] noncomputable def refs (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (refsBlk (Nat.shiftRight i 11))
    (Nat.mul 7 (Nat.land i 2047))) 127
@[expose] noncomputable def plBlk0 : ℕ := 0x80e1724385890808000
@[expose] noncomputable def plBlk (_b : ℕ) : ℕ :=
  plBlk0
@[expose] noncomputable def pl (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (plBlk (Nat.shiftRight i 11))
    (Nat.mul 7 (Nat.land i 2047))) 127
@[expose] noncomputable def ffiBlk0 : ℕ := 0x29d51a3a548000000000027d10a1a4cba94878c020a84e0e10180
@[expose] noncomputable def ffiBlk (_b : ℕ) : ℕ :=
  ffiBlk0
@[expose] noncomputable def ffi (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (ffiBlk (Nat.shiftRight i 11))
    (Nat.mul 7 (Nat.land i 2047))) 127
@[expose] noncomputable def liveMask : ℕ := 0x17
@[expose] noncomputable def live (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight liveMask x) 1) 1

@[expose] noncomputable def words : List (List ℕ) :=
  [[2, 2], [4, 4], [0, 0], [6, 3, 6, 2], [4, 0, 4, 0], [4, 5, 6], [5, 4, 6], [0, 4, 2, 0, 4, 2],
    [4, 2, 4, 2, 4, 2], [4, 2, 0, 4, 2, 0], [2, 0, 2, 0, 2, 0, 2, 0], [0, 0, 6], [1, 0, 6], [6, 5,
    6, 4, 6], [6, 6, 6], [6, 1, 6, 0], [0, 1, 6]]

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 11 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 43 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 11 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 43 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 11 6 43 fx fc fy (invLetter 3) ffi live 0 66 = true := by
  decide +kernel

theorem cover_all : coverOK 11 6 43 fx fc fy (invLetter 3) ffi live 0 66 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Bridge.RootClosure.CoxQ2
