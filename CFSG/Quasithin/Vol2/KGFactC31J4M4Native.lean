module

public import CFSG.Sporadic.J4.QTNative

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4.Native

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def w1Word : List Int :=
  [-2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1,
    2, 2, 2, 1, 2, 2, 2]

@[expose] def w2Word : List Int :=
  [-2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2]

@[expose] def m4Mats (_ : Unit := ()) : Array (Array V2) :=
  #[wordRows baseMats baseInvs w1Word, wordRows baseMats baseInvs w2Word]

@[expose] def m4Invs (_ : Unit := ()) : Array (Array V2) :=
  #[wordRows baseMats baseInvs (invW w1Word), wordRows baseMats baseInvs (invW w2Word)]

@[expose] def fWords : List (List Int) := [
    [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1,
     -2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, -2],
    [1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1,
     2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2, -2],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, 1, 2, 1, 2, 2,
     1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2,
     1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, 2, 2, 2, 1, 2, 1, 2, 2, 1,
     2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1,
     2, 2, -2, -1, -2, -2, -2, -1],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, 2, 1, 2, 1, 2,
     1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2,
     1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1,
     2, 2, -2, -1, -2, -2, -2, -1],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, 2, 1, 2, 1, 2,
     2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2,
     -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, 2, 1, 2, 1,
     2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2],
    [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, 1,
     2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2,
     2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, -2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
     2, -2, -1, -2, -1, -2, -2],
    [2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2, -2],
    [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1,
     -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1,
     2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2,
     -2, -1, -2, -1, -2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, -2,
     1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2, -2, -1],
    [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
     2, -2, -1, -2, -2],
    [2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2,
     1, 2, 2, -2, -1, -2, -1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -2,
     -2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, -2, -1, -2, -1, -2, -2]]

@[expose] def fTab (_ : Unit := ()) : Array (Array V2) :=
  (fWords.map fun w => wordRows m4Mats m4Invs w).toArray

@[expose] def fRows (T : Array (Array V2)) (c : Nat) : Array V2 :=
  (List.range 10).foldl (fun acc j => if c.testBit j then mulRows acc (T[j]?.getD idRows) else acc)
    idRows

@[expose] def fVec (T : Array (Array V2)) (u : V2) (c : Nat) : V2 :=
  (List.range 10).foldl (fun acc j => if c.testBit j then frApply (T[j]?.getD #[]) acc else acc) u

@[expose] def cTab : List (List Nat) := [
    [549, 941, 4, 823, 132, 512, 208, 20, 800, 32],
    [800, 768, 532, 809, 528, 3, 164, 597, 514, 512]]

@[expose] def chkF (_ : Unit := ()) : Bool :=
  let T := fTab
  ((List.range 10).all fun i =>
      eqRows (mulRows (T[i]?.getD idRows) (T[i]?.getD idRows)) idRows &&
        (List.range 10).all fun j =>
          eqRows (mulRows (T[i]?.getD idRows) (T[j]?.getD idRows))
            (mulRows (T[j]?.getD idRows) (T[i]?.getD idRows))) &&
    ((List.range 1024).all fun c =>
      c == 0 || CFSG.Sporadic.J4.QT.differs (fVec (T.map frTable) rootV c) rootV) &&
    (List.range 2).all fun w => (List.range 10).all fun j =>
      eqRows (mulRows (mulRows (m4Mats[w]?.getD idRows) (T[j]?.getD idRows))
          (m4Invs[w]?.getD idRows))
        (fRows T ((cTab.getD w []).getD j 0))

@[expose] def gWord : List Int :=
  [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1]

@[expose] def kwVecs : List V2 := [
    ⟨0xBCA72C80F54F918F, 0x0000B2B1514B1302⟩,
    ⟨0x83197822B020C721, 0x0000318E3CC40132⟩,
    ⟨0x3236DA3EA40483E6, 0x0000F2EE76BD0DBE⟩,
    ⟨0x55AA540EC617F48D, 0x0000BA0C85ED2F4C⟩,
    ⟨0x8F7E2F50CA106862, 0x0000212160CBAD57⟩,
    ⟨0x32448706A374B3F3, 0x00006F748A6406E0⟩,
    ⟨0xE8E2A160A8031F09, 0x000069C3939B8FA5⟩,
    ⟨0xE4F7AB2AD543805F, 0x0000E4F6334D289E⟩,
    ⟨0x019D84D69C2B4A1E, 0x0000FCE4BBE4B8B5⟩,
    ⟨0x59BF5E44BB576BDB, 0x00003739253B8877⟩,
    ⟨0xBCD571B8F23FA19A, 0x00002F2BAD92185C⟩,
    ⟨0xB0C07BF28F7F3ECC, 0x0000A21E0D44BF67⟩,
    ⟨0xD75CF5C2ED6C49A7, 0x0000EAFCFE149D95⟩,
    ⟨0x6A665D9484089236, 0x0000A4A914BB3622⟩,
    ⟨0x0D888E9CE16BD548, 0x000071D11B321F8E⟩,
    ⟨0xD72EA8FAEA1C79B2, 0x0000776602CD96CB⟩,
    ⟨0x6A1400AC8378A223, 0x00003933E8623D7C⟩,
    ⟨0x66010AE6FE383D75, 0x0000B40648B49A47⟩,
    ⟨0xDB3BA2B0975CE6E4, 0x0000FA53A21B31F0⟩,
    ⟨0x836B251AB750F734, 0x0000AC14C01D0A6C⟩,
    ⟨0x59CD037CBC275BCE, 0x0000AAA3D9E28329⟩,
    ⟨0x3E518D4CDE342CA5, 0x0000E2412AB2A1DB⟩,
    ⟨0xDB49FF88902CD6F1, 0x000067C95EC23AAE⟩,
    ⟨0x55D80936C167C498, 0x0000279679342412⟩,
    ⟨0x01EFD9EE9B5B7A0B, 0x0000617E473DB3EB⟩,
    ⟨0x667357DEF9480D60, 0x0000299CB46D9119⟩,
    ⟨0x3E23D074D9441CB0, 0x00007FDBD66BAA85⟩,
    ⟨0xE890FC58AF732F1C, 0x0000F4596F4284FB⟩,
    ⟨0x0DFAD3A4E61BE55D, 0x0000EC4BE7EB14D0⟩,
    ⟨0xE485F612D233B04A, 0x0000796CCF9423C0⟩,
    ⟨0x8F0C7268CD605877, 0x0000BCBB9C12A609⟩]

@[expose] def kwSig : List (List Nat) := [
    [0, 2, 1, 3, 5, 4, 7, 6, 8, 9, 11, 10, 13, 12, 14, 17, 18, 15, 16, 21, 23, 19, 25, 20, 28, 22,
     30, 27, 24, 29, 26],
    [1, 0, 3, 4, 6, 5, 2, 8, 9, 10, 7, 12, 14, 15, 16, 13, 11, 19, 20, 22, 18, 24, 26, 27, 21, 29,
     17, 23, 28, 25, 30],
    [0, 2, 1, 3, 5, 4, 7, 6, 8, 9, 11, 10, 13, 12, 14, 17, 18, 15, 16, 21, 23, 19, 25, 20, 28, 22,
     30, 27, 24, 29, 26],
    [1, 0, 6, 2, 3, 5, 4, 10, 7, 8, 9, 16, 11, 15, 12, 13, 14, 26, 20, 17, 18, 24, 19, 27, 21, 29,
     22, 23, 28, 25, 30]]

@[expose] def letRows (_ : Unit := ()) : Array (Array V2) :=
  #[m4Invs[0]?.getD idRows, m4Invs[1]?.getD idRows, m4Mats[0]?.getD idRows,
    m4Mats[1]?.getD idRows]

@[expose] def chkKW (_ : Unit := ()) : Bool :=
  frApply (frTable (wordRows baseMats baseInvs gWord)) rootV == kwVecs.getD 0 V2.zero &&
    (List.range 4).all fun l => (List.range 31).all fun k =>
      frApply (frTable (letRows[l]?.getD idRows)) (kwVecs.getD k V2.zero) ==
        kwVecs.getD ((kwSig.getD l []).getD k 0) V2.zero

end CFSG.Quasithin.KGC31.J4M4

end
