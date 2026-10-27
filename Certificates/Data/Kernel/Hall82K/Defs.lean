module

public section

namespace CFSG.KC.Hall82K

@[expose] def fld (c s : Nat) : Nat := Nat.land (Nat.shiftRight c s) 63

@[expose] def bitN (v j : Nat) : Nat := Nat.land (Nat.shiftRight v j) 1

@[expose] def apL (c v : Nat) : Nat :=
  Nat.xor
    (Nat.xor (Nat.xor (Nat.mul (bitN v 0) (fld c 0)) (Nat.mul (bitN v 1) (fld c 6)))
      (Nat.xor (Nat.mul (bitN v 2) (fld c 12)) (Nat.mul (bitN v 3) (fld c 18))))
    (Nat.xor (Nat.mul (bitN v 4) (fld c 24)) (Nat.mul (bitN v 5) (fld c 30)))

@[expose] def compL (f g : Nat) : Nat :=
  Nat.lor
    (Nat.lor (Nat.lor (apL f (fld g 0)) (Nat.shiftLeft (apL f (fld g 6)) 6))
      (Nat.lor (Nat.shiftLeft (apL f (fld g 12)) 12) (Nat.shiftLeft (apL f (fld g 18)) 18)))
    (Nat.lor (Nat.shiftLeft (apL f (fld g 24)) 24) (Nat.shiftLeft (apL f (fld g 30)) 30))

@[expose] noncomputable def bor (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def band (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def allL (p : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => band (p h) ih) L

@[expose] noncomputable def memL (z : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => bor (Nat.beq z h) ih) L

@[expose] def s40K : List Nat :=
  [34630287489, 36794548353, 34697920641, 36862181505, 43354452097, 45518712961, 45603123329,
    43472416897, 8866762884, 11081355396, 8884064388, 11098656900, 43763396740, 45977989252,
    45961736324, 43881361540, 9003077767, 11268001927, 9020379271, 11251748999, 35175547015,
    37440471175, 37373886599, 35243180167]

@[expose] def q0K : Nat := 10837449240524681216

@[expose] def wK : Nat := 7566047373982433385

@[expose] def fullK : Nat := 18446744073709551615

@[expose] def qtK : Nat :=
  242231087471212044817800933629678066360622020181037517424150919167646548245624846858998635580437600547649342004698942382920450364589688058373494901363771673857915163454673878485145444601520595827030224922571493101753830866255484613561588655842076687027277502191808517843626920978593137513648682232026864072590758311137998157651447215379726268586193627095474556103180527640514876059767447964598195455487502184106479796886699453514702122992029913275319675765575460202309129508307810263789372476017555459295395016138363368297438396437350480258684927394992654867243942717980753097235390553050344093515772287599078839501068505913499505318250390266429702405028108863578948628450549563149419926793848562927585313353915768302639804743095529044694045298697683825054316191394731837361984237808985282091062932222753585281865362493041935970675428933679684842167968655191571206976870783123266255753278869992156820084956965223663509751074184346333547450691957241320659659932048521882045377067370686140846273501563742504955840938962645693895988541718399206612398169064884778040879824240112366452313459217241906504507916360238459504051181974724972283118166822187822755482788383246485752904281010556964690768821871704088758415349144974914600366080

@[expose] def idxK : Nat :=
  5411887561974193248464261195923263992272450351787024736029173753930981057104783371745078876169240094295938376184513695744

@[expose] def lowB (m : Nat) : Nat := Nat.sub m (Nat.land m (Nat.sub m 1))

@[expose] def idxB (b : Nat) : Nat := fld idxK (Nat.mul 6 (Nat.mod b 67))

@[expose] noncomputable def forBitsK (p : Nat → Bool) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun m => Nat.beq m 0)
    (fun _ ih m => bor (Nat.beq m 0)
      (band (p (idxB (lowB m))) (ih (Nat.sub m (lowB m))))) n

@[expose] def rowK (i j a : Nat) : Nat :=
  Nat.xor (Nat.land (Nat.shiftRight qtK (Nat.shiftLeft a 6)) fullK)
    (Nat.mul (Nat.sub 1 (bitN q0K (Nat.xor (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j)))) fullK)

@[expose] noncomputable def candK (i P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.xor fullK q0K) 1)
    (fun j ih => Nat.land ih (rowK i j (fld P (Nat.mul 6 j)))) i

@[expose] def noOrb3K (l0 l1 l2 : Nat) : Bool :=
  Nat.beq
    (Nat.lor (Nat.land 146 (Nat.shiftLeft 1 l0))
      (Nat.lor (Nat.land 146 (Nat.shiftLeft 1 l2))
        (Nat.land 146 (Nat.shiftLeft 1 (Nat.xor (Nat.xor l0 l1) l2)))))
    0

@[expose] noncomputable def goodK (z : Nat) : Bool :=
  bor (noOrb3K (fld z 0) (fld z 6) (fld z 12)) (memL z s40K)

@[expose] noncomputable def goodCK (a b : Nat) : Bool :=
  bor (noOrb3K (apL a (fld b 0)) (apL a (fld b 6)) (apL a (fld b 12))) (memL (compL a b) s40K)

@[expose] noncomputable def good2K (y : Nat) : Bool :=
  allL (fun t => goodCK y (compL t y)) s40K

@[expose] noncomputable def good3RowK (a y : Nat) : Bool :=
  allL (fun u => goodCK a (compL u y)) s40K

@[expose] noncomputable def good3K (y : Nat) : Bool :=
  allL (fun t => good3RowK (compL y (compL t y)) y) s40K

@[expose] def inWK (v : Nat) : Bool := Nat.blt 0 (Nat.land wK (Nat.shiftLeft 1 v))

@[expose] noncomputable def wInvK (y : Nat) : Bool :=
  band (inWK (apL y 3)) (band (inWK (apL y 5)) (inWK (apL y 56)))

@[expose] noncomputable def leafK (y : Nat) : Bool :=
  bor (wInvK y) (Bool.rec (motive := fun _ => Bool) true false
    (band (goodK y) (band (good2K y) (good3K y))))

@[expose] noncomputable def srchK (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) leafK
    (fun n ih P => forBitsK (fun x => ih (Nat.lor P (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n)))))
      64 (candK (Nat.sub 5 n) P)) n

end CFSG.KC.Hall82K
