module

public import Certificates.Data.Kernel.Hall82K.Defs

public section

namespace CFSG.KC.Hall82K

@[expose] def m36K : Nat := 68719476735

@[expose] def idK : Nat := 34630287489

@[expose] def apA (x v : Nat) : Nat := Nat.xor (apL x v) (Nat.shiftRight x 36)

@[expose] def compA (f g : Nat) : Nat :=
  Nat.lor (compL f g) (Nat.shiftLeft (apA f (Nat.shiftRight g 36)) 36)

@[expose] def trK (u : Nat) : Nat := Nat.lor idK (Nat.shiftLeft u 36)

@[expose] noncomputable def b2n (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def beqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

@[expose] noncomputable def xcodeK (x : Nat) : Nat :=
  Nat.lor
    (Nat.lor (Nat.xor (bitN (Nat.shiftRight x 36) 0) (bitN (Nat.shiftRight x 36) 2))
      (Nat.lor (Nat.shiftLeft (bitN (Nat.shiftRight x 36) 1) 1)
        (Nat.shiftLeft (bitN (Nat.shiftRight x 36) 4) 2)))
    (Nat.lor (Nat.shiftLeft (b2n (Nat.beq (fld x 24) 21)) 3)
      (Nat.lor (Nat.shiftLeft (b2n (bor (Nat.beq (fld x 6) 3) (Nat.beq (fld x 6) 12))) 4)
        (Nat.shiftLeft (b2n (Nat.beq (fld x 0) 4)) 5)))

@[expose] noncomputable def allN (p : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => band (p k) ih) n

@[expose] noncomputable def orL (f : Nat → Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun h _ ih => Nat.lor (f h) ih) L

@[expose] def rmK : List Nat :=
  [34630287489, 45451591809, 51811205313, 68001218753, 34628702724, 45450007044, 51808834308,
    67998847748]

@[expose] def u0K : List Nat := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31]

@[expose] def kK : List Nat :=
  [1, 2, 3, 4, 8, 12, 16, 21, 27, 30, 32, 39, 42, 45, 48, 54, 57, 63]

@[expose] def x1BasisK : List Nat :=
  [309508194433, 1065422438529, 1477739298945, 389048975489, 395408588993, 378226086404]

@[expose] def c5GensK : List Nat := [12968614928, 48773480577, 68013125019]

@[expose] def c5K : List Nat :=
  [595670153928214907541, 3352305471443187919707, 149489531645367769104, 2913042378187980782046,
    891196431846088970197, 4016766630835252739678, 4241586324233588698523, 223654880678728522768,
    595488646898791811733, 2912860871158556126043, 149308024615944673296, 3352123964413766384094,
    890924874817572245461, 4241314767205071175262, 4016495073806736813467, 223383323650211798032,
    2379666331274406531588, 2379775235495957643393, 2380341191101860670299,
    2380448406885868354014, 3351579159665729606148, 2912424970632072020097, 595618701978210732693,
    149545295479369717776, 3123300701756644135428, 3123409605978195247233, 3124082777368104397659,
    3123975561584099834334, 2912316066416913027588, 3351688063893672837249, 595725917768608975509,
    149438079701755713552, 3560275983999693492996, 3560438918222634303681, 3561257110592045039198,
    3561202236371885223323, 4015679978326025048836, 4240662605947301019841, 891090905929212825557,
    223494480541691763728, 4240499671727631766276, 4015842912552237416641, 891036031712323768277,
    223549354765123935248, 4672845235961490838276, 4673008170184431648961, 4673771488333681770078,
    4673826362553843183003]

@[expose] def s40WitK : List Nat :=
  [152298645201562018021632, 152298645201562018021634, 152298645201562018021664,
    152298645201562018021666, 214501066218606694793472, 214501066218606694793474,
    214501066218606694793504, 214501066218606694793506, 38122889851405754082624,
    38122889851405754082656, 38122889851405754082626, 38122889851405754082658,
    38119596926605486892352, 38119596926605486892384, 38119596926605486892354,
    38119596926605486892386, 214547550172364026861248, 214547550172364026861282,
    214547550172364026861250, 214547550172364026861280, 152341836230519082899136,
    152341836230519082899170, 152341836230519082899138, 152341836230519082899168]

@[expose] noncomputable def allX1 (p : Nat → Bool) : Bool :=
  allL (fun u => allL (fun r => p (Nat.lor r (Nat.shiftLeft u 36))) rmK) u0K

@[expose] noncomputable def x1MulK : Bool :=
  allX1 fun x => allX1 fun y => Nat.beq (xcodeK (compA x y)) (Nat.xor (xcodeK x) (xcodeK y))

@[expose] noncomputable def x1ZeroK : Bool :=
  allX1 fun x => beqB (Nat.beq (xcodeK x) 0) (bor (Nat.beq x idK) (Nat.beq x (trK 5)))

@[expose] noncomputable def x1SurjK : Bool :=
  Nat.beq (orL (fun u => orL (fun r => Nat.shiftLeft 1 (xcodeK (Nat.lor r (Nat.shiftLeft u 36))))
    rmK) u0K) fullK

@[expose] noncomputable def x1SqK : Bool :=
  allX1 fun x => beqB (Nat.beq (compA x x) (trK 5)) (Nat.beq (bitN q0K (xcodeK x)) 1)

@[expose] noncomputable def x1OrbK : Bool :=
  allX1 fun x => bor (Nat.beq (Nat.land 146 (Nat.shiftLeft 1 (xcodeK x))) 0)
    (band (Nat.beq (Nat.land x m36K) idK) (memL (Nat.shiftRight x 36) kK))

@[expose] noncomputable def c5InvK : Bool :=
  allL (fun w => Nat.beq (compL (Nat.land w m36K) (Nat.shiftRight w 36)) idK) c5K

@[expose] noncomputable def c5LinK : List Nat := List.map (fun w => Nat.land w m36K) c5K

@[expose] noncomputable def c5ClosK : Bool :=
  band (allL (fun g => memL g c5LinK) c5GensK)
    (allL (fun s => allL (fun g => memL (compL g s) c5LinK) c5GensK) c5LinK)

@[expose] noncomputable def conjXK (b w x : Nat) : Nat :=
  xcodeK (compA (compA (compA (trK b) (Nat.land w m36K)) x)
    (compA (Nat.shiftRight w 36) (trK b)))

@[expose] noncomputable def sigK (b w : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun h _ ih j => Nat.lor (Nat.shiftLeft (conjXK b w h) j) (ih (Nat.add j 6))) x1BasisK 0

@[expose] noncomputable def conjOkK (b w : Nat) : Bool :=
  band (memL (sigK b w) s40K) (allX1 fun x => Nat.beq (conjXK b w x) (apL (sigK b w) (xcodeK x)))

@[expose] noncomputable def conjRowK (b : Nat) : Bool := allL (fun w => conjOkK b w) c5K

@[expose] noncomputable def witOkK (σ e : Nat) : Bool :=
  band (memL (Nat.shiftRight e 6) c5K)
    (Nat.beq (sigK (Nat.land e 63) (Nat.shiftRight e 6)) σ)

@[expose] noncomputable def conjSurjK : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun σ _ ih W => List.rec (motive := fun _ => Bool) false
      (fun e W' _ => band (witOkK σ e) (ih W')) W) s40K s40WitK

@[expose] def xiK (r a : Nat) : Nat := Nat.lor r (Nat.shiftLeft a 36)

@[expose] def invIK (x : Nat) : Nat :=
  Nat.lor (Nat.land x m36K) (Nat.shiftLeft (apL x (Nat.shiftRight x 36)) 36)

@[expose] noncomputable def oneOr5 (z : Nat) : Bool := bor (Nat.beq z idK) (Nat.beq z (trK 5))

@[expose] noncomputable def sqOK (x : Nat) : Bool := oneOr5 (compA x x)

@[expose] noncomputable def commOK (x y : Nat) : Bool :=
  oneOr5 (compA (compA x y) (compA (invIK x) (invIK y)))

@[expose] noncomputable def inU (a : Nat) : Bool := memL a u0K

@[expose] noncomputable def liftInvK (r0 r1 r2 : Nat) : Bool :=
  band (Nat.beq (compL r0 r0) idK) (band (Nat.beq (compL r1 r1) idK) (Nat.beq (compL r2 r2) idK))

@[expose] noncomputable def liftK (r0 r1 r2 : Nat) : Bool :=
  allN (fun a0 => bor (Bool.rec (motive := fun _ => Bool) true false (sqOK (xiK r0 a0)))
    (allN (fun a1 => bor (Bool.rec (motive := fun _ => Bool) true false
        (band (sqOK (xiK r1 a1)) (commOK (xiK r0 a0) (xiK r1 a1))))
      (allN (fun a2 => bor (Bool.rec (motive := fun _ => Bool) true false
          (band (sqOK (xiK r2 a2)) (band (commOK (xiK r0 a0) (xiK r2 a2))
            (commOK (xiK r1 a1) (xiK r2 a2)))))
        (band (inU a0) (band (inU a1) (inU a2)))) 64)) 64)) 64

end CFSG.KC.Hall82K
