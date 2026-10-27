module

public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure.CoxA3

@[expose] noncomputable def edgeBlk0 : ℕ := 0xb8add5acaf517a4bde52c2731694b5a4aaa73558cad6468210147aa513dd2738e906b4498a524c885ac454a314a845ae412a10497c6323d21ef097042038e9ce476c42234c9ad463063018a96b455439e28a14a05244a6106908431839c0c50c6820c296048042040a211041063800210900002100
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

@[expose] noncomputable def justBlk0 : ℕ := 0x8abb3a22e4282a169f285e7aa1180000078b129ca45e709118000006ea909a225a6689180000064a12981e4e5e7908000005c7118000005a91295984e546108000005289293944e4c5108000004a81191125642490800000407918e925238492800000367128c8e4e303908000002e6918a0c5626310800000243128000002229080000020511868a5218292800000162118000001419080000012192800000101118000000e0918000000c21282024e06090800000040118000000201080000000012800000
@[expose] noncomputable def justBlk (_b : ℕ) : ℕ :=
  justBlk0
@[expose] noncomputable def just (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (justBlk (Nat.shiftRight i 11))
    (Nat.mul 22 (Nat.land i 2047))) 4194303
@[expose] noncomputable def kind (f : ℕ) : ℕ := Nat.land (just f) 3
@[expose] noncomputable def wi (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 2) 15
@[expose] noncomputable def ft (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 6) 7
@[expose] noncomputable def fs (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 9) 31
@[expose] noncomputable def fo (f : ℕ) : ℕ :=
  Nat.shiftRight (just f) 14

@[expose] noncomputable def refsBlk0 : ℕ := 0x7a808a008a6c4e627e008472565c76008400840080663e446a007c007c0078582e426a0074007400704852006c006c00680064343a00600060005c2832005800580054240c163200500050004c24121a360048004800441c2200400040003c18040a220038003800340030002c14000a1e0028002800240020001c0018001400100006000c000c000800040000
@[expose] noncomputable def refsBlk (_b : ℕ) : ℕ :=
  refsBlk0
@[expose] noncomputable def refs (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (refsBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def plBlk0 : ℕ := 0x90827b6b665648413f332c2a2523201715120b0904020000
@[expose] noncomputable def plBlk (_b : ℕ) : ℕ :=
  plBlk0
@[expose] noncomputable def pl (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (plBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def ffiBlk0 : ℕ := 0x85868d8a8f887d7e8b8c838075767b78898e87846d6e7370696a797a81827f7c616267647774595a5f5c5754515271724f4c6f6c494a6b68414247443f3c393a65664d4e63603536555631325d5e2f2c5b58292a252653504b483d3e212245462d2e43401d1e191a3b383734151633302b2827240d0e1310090a23201f1c1b180506111217140f0c01020b0807040300
@[expose] noncomputable def ffiBlk (_b : ℕ) : ℕ :=
  ffiBlk0
@[expose] noncomputable def ffi (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (ffiBlk (Nat.shiftRight i 11))
    (Nat.mul 8 (Nat.land i 2047))) 255
@[expose] noncomputable def liveMask : ℕ := 0xffffff
@[expose] noncomputable def live (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight liveMask x) 1) 1

@[expose] noncomputable def words : List (List ℕ) :=
  [[2, 2], [4, 4], [0, 0], [2, 0, 2, 0], [0, 4, 0, 4, 0, 4], [2, 4, 2, 4, 2, 4], [4, 2, 4, 2, 4,
    2], [4, 0, 4, 0, 4, 0]]

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

end CFSG.Timmesfeld.Bridge.RootClosure.CoxA3
