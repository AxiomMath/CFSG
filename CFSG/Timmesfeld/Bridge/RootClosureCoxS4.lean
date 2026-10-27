module

public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure.CoxS4

@[expose] noncomputable def edgeBlk0 : ℕ := 0xb8a5e4212f4177abdd3eca368f7cb4559c2d60eac9d44a42b3956aad5368a735464a523162730b945ae494a524a885284532318980630412a1049407bc21d1088e3a7391da0e70d346b618c98c462a5ad14914a84204a4106908431439e0840c6022818c1430a5810a211041063800210900002100
@[expose] noncomputable def edgeBlk (_b : ℕ) : ℕ :=
  edgeBlk0
@[expose] noncomputable def edge (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edgeBlk (Nat.shiftRight i 11))
    (Nat.mul 13 (Nat.land i 2047))) 8191
@[expose] noncomputable def fx (f : ℕ) : ℕ :=
  Nat.land (edge f) 31
@[expose] noncomputable def fc (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edge f) 5) 7
@[expose] noncomputable def fy (f : ℕ) : ℕ :=
  Nat.shiftRight (edge f) 8

@[expose] noncomputable def justBlk0 : ℕ := 0x9ab99d31712a49e29453c568878840000021ac2142584a8070b4f0e199d9c2300000072a9b4e151199da3130b4525f6884000001768212a305e526094000001416230000004e909490a1491942100000044888c809138f92250000003c808c689158c922100000030408c000000b9c25141c5226388400000091a2310184e1e309400000070c210000001a28840000006082500000016208c00000050621000000121094000000404230000000e288c141138202250000000608840000001002500000002008400000000023000000
@[expose] noncomputable def justBlk (_b : ℕ) : ℕ :=
  justBlk0
@[expose] noncomputable def just (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (justBlk (Nat.shiftRight i 11))
    (Nat.mul 23 (Nat.land i 2047))) 8388607
@[expose] noncomputable def kind (f : ℕ) : ℕ := Nat.land (just f) 3
@[expose] noncomputable def wi (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 2) 15
@[expose] noncomputable def ft (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 6) 15
@[expose] noncomputable def fs (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 10) 31
@[expose] noncomputable def fo (f : ℕ) : ℕ :=
  Nat.shiftRight (just f) 15

@[expose] noncomputable def refsBlk0 : ℕ := 0x644c8a008a7e82504a00844420142e626800840084007c007e424600783c386e7458540078007800605c7200723418040a142e5c006c3432666a006c006c00684c4852565a5e62006400640060005c280c122e005800580054242a00500050004c240c00061a3200480048004400401c040a22003c003c0038181e003400340030002c002800240020001c00180014000a00100010000c000800040000
@[expose] noncomputable def refsBlk (_b : ℕ) : ℕ :=
  refsBlk0
@[expose] noncomputable def refs (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (refsBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def plBlk0 : ℕ := 0x6b625d584d48434138332e2c25201c17120e0b0904020000
@[expose] noncomputable def plBlk (_b : ℕ) : ℕ :=
  plBlk0
@[expose] noncomputable def pl (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (plBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def ffiBlk0 : ℕ := 0x8d8a85868f88817e837c797a77706d6e757265666b68898e7176696a61625f5c595a737451527d8257548b8c494a4f4c7f808784454643403d3e7b7835366f6c3b38676431324d4e5d5e2d2e6360292a5b58555653504b4825264142212247441d1e3f3c393a37343330191a11122f2c17142b280d0e2724090a232015161f1c05061b1813100f0c01020b0807040300
@[expose] noncomputable def ffiBlk (_b : ℕ) : ℕ :=
  ffiBlk0
@[expose] noncomputable def ffi (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (ffiBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def liveMask : ℕ := 0xffffff
@[expose] noncomputable def live (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight liveMask x) 1) 1

@[expose] noncomputable def words : List (List ℕ) :=
  [[2, 2], [0, 0], [4, 4], [4, 0, 4, 0], [2, 4, 2, 4, 2, 4], [2, 0, 2, 0, 2, 0, 2, 0], [0, 4, 0,
    4], [4, 2, 0, 4, 2, 0, 4, 2, 0], [2, 0, 4, 2, 0, 4, 2, 0, 4], [0, 2, 0, 2, 0, 2, 0, 2]]

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 24 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 72 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 24 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 72 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 24 6 72 fx fc fy (invLetter 3) ffi live 0 144 = true := by
  decide +kernel

theorem cover_all : coverOK 24 6 72 fx fc fy (invLetter 3) ffi live 0 144 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Bridge.RootClosure.CoxS4
