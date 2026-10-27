module

public import Certificates.Data.ONanF2Quot

public section

namespace CFSG.KC.ONanF2K

open CFSG.OddStandard.ONanRec.F2 CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def dmulT : Nat := 128103823123748519999582387378152396579918957627710293640

@[expose] def ckT : Nat := 3909509018843104314303156798357504

@[expose] def meT : Nat := 5493853585216064983003705484206433283408129

@[expose] def lane (T j w : Nat) : Nat := Nat.mod (Nat.shiftRight T (Nat.mul j w)) (Nat.pow 2 w)

@[expose] def rowK (r a b0 b1 b2 c : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.add a (Nat.mul (lane meT r 2) b0))
    (Nat.mul (lane meT (Nat.add r 1) 2) b1)) (Nat.mul (lane meT (Nat.add r 2) 2) b2)) c) 4

@[expose] def mulD (dx a0 a1 a2 dy b0 b1 b2 : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.mul (lane dmulT (Nat.add (Nat.mul dx 8) dy) 3) 64)
    (Nat.mul (rowK (Nat.mul dx 9) a0 b0 b1 b2 (lane ckT (Nat.add (Nat.mul dx 8) dy) 2)) 16))
    (Nat.mul (rowK (Nat.add (Nat.mul dx 9) 3) a1 b0 b1 b2 0) 4))
    (rowK (Nat.add (Nat.mul dx 9) 6) a2 b0 b1 b2 (lane ckT (Nat.add (Nat.mul dx 8) dy) 2))

@[expose] def mulK (x y : Nat) : Nat :=
  mulD (Nat.mod (Nat.div x 64) 8) (Nat.mod (Nat.div x 16) 4) (Nat.mod (Nat.div x 4) 4) (Nat.mod x 4)
    (Nat.mod (Nat.div y 64) 8) (Nat.mod (Nat.div y 16) 4) (Nat.mod (Nat.div y 4) 4) (Nat.mod y 4)

theorem mulK_eq (x y : Nat) : mulK x y =
    lane dmulT (x / 64 % 8 * 8 + y / 64 % 8) 3 * 64 +
      (x / 16 % 4 + lane meT (x / 64 % 8 * 9) 2 * (y / 16 % 4) +
        lane meT (x / 64 % 8 * 9 + 1) 2 * (y / 4 % 4) + lane meT (x / 64 % 8 * 9 + 2) 2 * (y % 4) +
        lane ckT (x / 64 % 8 * 8 + y / 64 % 8) 2) % 4 * 16 +
      (x / 4 % 4 + lane meT (x / 64 % 8 * 9 + 3) 2 * (y / 16 % 4) +
        lane meT (x / 64 % 8 * 9 + 3 + 1) 2 * (y / 4 % 4) +
        lane meT (x / 64 % 8 * 9 + 3 + 2) 2 * (y % 4) + 0) % 4 * 4 +
      (x % 4 + lane meT (x / 64 % 8 * 9 + 6) 2 * (y / 16 % 4) +
        lane meT (x / 64 % 8 * 9 + 6 + 1) 2 * (y / 4 % 4) +
        lane meT (x / 64 % 8 * 9 + 6 + 2) 2 * (y % 4) +
        lane ckT (x / 64 % 8 * 8 + y / 64 % 8) 2) % 4 := rfl

@[expose] noncomputable def powK (x n : Nat) : Nat := Nat.rec 0 (fun _ ih => mulK ih x) n

@[expose] noncomputable def invK (x : Nat) : Nat := powK x 15

@[expose] noncomputable def expK : Bool := (List.range 512).all fun x => Nat.beq (powK x 16) 0

@[expose] noncomputable def unpackL (P n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih P => Nat.mod P 512 :: ih (Nat.shiftRight P 9)) n P

@[expose] def decN (c : Nat) : AlpE :=
  ⟨Fin.ofNat 8 (c / 64), ((c / 16 : Nat) : ZMod 4), ((c / 4 : Nat) : ZMod 4), ((c : Nat) : ZMod 4)⟩

@[expose] def cdN (a : AlpE) : Nat := a.d.val * 64 + a.v0.val * 16 + a.v1.val * 4 + a.v2.val

@[expose] def f4D (m : Nat) : F4c := ⟨((m % 2 : Nat) : ZMod 2), ((m / 2 : Nat) : ZMod 2)⟩

@[expose] def tcDec (k : Nat) : TcM := ⟨f4D (k % 4), f4D (k / 4 % 4), f4D (k / 16 % 4)⟩

@[expose] def P0T : Nat :=
  1352938375151382073900745064004029800550728888332101201613736727829525233546948762066056975754883834540707476824032495005104320567660421742911093948771319989830639470087677475605254812397578240364511971474078830444370614637606472814635401755133793318777906742897585778798343236746791788615941020779817617540069494173123840506871744586871903340343744870475820344752640320741230864962969112732491800462062583028526183759767868815903334551992537013030116297038584339568204422471252743511069502141928777333270021396112958108760034617374156767710809493389781785609456861879658971804449262899626008614075075853681291624743943649030054652078706727666870280886724589958230520799532735034379450329341952

@[expose] def NT : Nat := 7659337216
@[expose] def Q8T : Nat :=
  137271840778495941526818277048652266157163307974703449908909095884042602736860188915712

@[expose] def fT : Nat :=
  135031226983654933729414168997345885001922049209761804822563327171262765405215922565519674178473750456108696740785899569629567994687524443559352825639032932539679756223679261708014424485279175362894299686975312410926953780851056062373394184659622748423879959632958619420792835796405755021478459779680569385449793531745425053779554257346932028074011835173269289996624990688088224675704906765292191656406226600232635695692058903151544656033394084214522476168034230978624651748315727432548677087519709319155210882449669083248148705987233106313809675091572373448358109151628553418531298233322496921368900759194896604508532493707262629416869633832857785140746682581242163491107147399612224025588651048415357184406825205108054118047093934489525811309818762803225533047659830349107086356001648767141790661664793101120

end CFSG.KC.ONanF2K
