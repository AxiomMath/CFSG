module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.T84

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.GL4

@[expose] noncomputable def S0L : List Nat := [
  4680, 4751, 4852, 4958, 5013, 5097, 5167, 5250, 5368, 5433, 5534, 5603, 6180, 6223, 6386, 6462,
  6483, 6629, 7733, 7769, 7827, 7976, 8002, 8068, 8527, 8580, 8696, 9066, 9133, 9174, 9240, 9359,
  9457, 9789, 9891, 9946, 10271, 10305, 10484, 10806, 10861, 10963, 11578, 11619, 11686, 12052,
  12104, 12161, 12633, 12702, 12773, 12909, 12966, 13018, 13598, 13713, 13801, 13866, 13997, 14034,
  14613, 14686, 14817, 14893, 14946, 15062, 15654, 15722, 15778, 15897, 15953, 16021, 16680, 16783,
  16882, 16927, 17025, 17144, 17771, 17852, 17862, 18012, 18101, 18123, 18450, 18479, 18673, 19286,
  19308, 19397, 19547, 19557, 19638, 20248, 20257, 20354, 20798, 20883, 20969, 21273, 21406, 21473,
  21612, 21686, 21707, 22091, 22204, 22212, 22814, 22833, 23011, 23372, 23396, 23494, 23622, 23659,
  23732, 24083, 24121, 24209, 25146, 25261, 25299, 25389, 25506, 25562, 25691, 25788, 25797, 25932,
  26036, 26059, 27171, 27197, 27346, 27461, 27484, 27588, 27723, 27732, 27829, 27946, 27954, 28067,
  30874, 30892, 30921, 31116, 31144, 31178, 31369, 31388, 31432, 31711, 31725, 31742, 31882, 31896,
  31913, 32190, 32239, 32251, 32447, 32475, 32509, 32701, 32734, 32747, 33071, 33090, 33268, 33300,
  33359, 33521, 33823, 33825, 34034, 34716, 34729, 34762, 35194, 35244, 35271, 35452, 35479, 35529,
  35961, 35994, 36007, 36626, 36644, 36673, 37173, 37214, 37347, 37662, 37713, 37861, 38163, 38206,
  38369, 38794, 38828, 38856, 39036, 39079, 39114, 39544, 39564, 39623, 40058, 40071, 40104, 40469,
  40497, 40531, 41533, 41571, 41686, 41766, 41837, 41938, 42541, 42546, 42707, 42892, 42904, 42953,
  43129, 43164, 43207, 43388, 43399, 43464, 44152, 44169, 44183, 44323, 44342, 44386, 46172, 46181,
  46278, 46406, 46444, 46532, 46668, 46676, 46789, 47070, 47087, 47101, 48197, 48214, 48228, 48511,
  48615, 48638, 48765, 48863, 48887, 49022, 49111, 49133, 50262, 50283, 50357, 50507, 50532, 50614,
  50757, 50779, 50868, 51081, 51098, 51112, 51322, 51351, 51369, 51576, 51594, 51623, 51833, 51847,
  51864, 52038, 52052, 52069, 53814, 53866, 53923, 54058, 54114, 54182, 54819, 54842, 54946, 55231,
  55275, 55294, 55846, 55858, 55907, 56190, 56303, 56311, 56959, 57015, 57083, 57211, 57278, 57319,
  57657, 57683, 57749, 58133, 58201, 58257, 58649, 58673, 58771, 59325, 59359, 59387, 59667, 59701,
  59729, 60287, 60375, 60413, 60795, 60863, 60919, 61309, 61367, 61403, 61732, 61768, 61826, 61976,
  62017, 62084, 62482, 62504, 62593, 63422, 63451, 63469, 63508, 63521, 63554, 64381, 64478, 64487,
  64894, 64951, 65003, 65147, 65213, 65239]

@[expose] noncomputable def D0c : List Nat := [33825, 32475, 48615, 4680, 8580, 56190, 59325, 18450]

@[expose] noncomputable def F0m : List Nat := [33825, 32475, 8580, 56190]

@[expose] noncomputable def mkT (u c : Nat) : Nat := Nat.add (colC u) (Nat.mul (nat_lit 65536) c)

@[expose] noncomputable def hiT (e : Nat) : Nat := Nat.shiftRight e (nat_lit 16)

@[expose] noncomputable def mulT (e f : Nat) : Nat :=
  letN (Nat.shiftRight e (nat_lit 16)) fun c =>
    Nat.add (Nat.xor (Nat.land e (nat_lit 65535)) (mul4F c (Nat.land f (nat_lit 65535))))
      (Nat.mul (nat_lit 65536) (mul4F c (Nat.shiftRight f (nat_lit 16))))

@[expose] noncomputable def oneT : Nat := nat_lit 2216755200

@[expose] noncomputable def commT (x y : Nat) : Bool := Nat.beq (mulT x y) (mulT y x)

@[expose] noncomputable def isInvT (x : Nat) : Bool :=
  andB (notB (Nat.beq x oneT)) (Nat.beq (mulT x x) oneT)

@[expose] noncomputable def span4T (a b c d : Nat) : List Nat :=
  let s1 := [oneT, a]
  let s2 := s1 ++ s1.map (mulT b)
  let s3 := s2 ++ s2.map (mulT c)
  s3 ++ s3.map (mulT d)

@[expose] noncomputable def P0K : List Nat := (List.range 16).flatMap fun u => D0c.map (mkT u)

@[expose] noncomputable def M0K : List Nat := (List.range 16).flatMap fun u => S0L.map (mkT u)

@[expose] noncomputable def VK : List Nat := (List.range 16).map fun u => mkT u id4

@[expose] noncomputable def F0K : List Nat :=
  span4T (mkT 0 32475) (mkT 0 8580) (mkT 5 id4) (mkT 10 id4)

@[expose] noncomputable def dedupN (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x t ih => Bool.rec (motive := fun _ => List Nat) (x :: ih) ih (memN x t)) l

@[expose] noncomputable def JK : List Nat := dedupN (VK.flatMap fun x => F0K.map (mulT x))

@[expose] noncomputable def IPK : List Nat := P0K.filter isInvT

@[expose] noncomputable def IMK : List Nat := M0K.filter isInvT

@[expose] noncomputable def memP (x : Nat) : Bool := memN (hiT x) D0c

@[expose] noncomputable def memJ (x : Nat) : Bool := memN (hiT x) F0m

@[expose] noncomputable def chP0 : Bool :=
  andB (nodupN P0K) (andB (Nat.beq (lenN P0K) (nat_lit 128)) (andB (memN oneT P0K)
    (andB (allL D0c fun m => memN m S0L)
      (allL P0K fun x => allL P0K fun y => memP (mulT x y)))))

@[expose] noncomputable def chNE (A : List Nat) : Bool :=
  andB (nodupN A) (andB (Nat.beq (lenN A) (nat_lit 16)) (andB (allL A memP)
    (andB (allL A fun x => allL A fun y => memN (mulT x y) A)
      (andB (allL A fun x => Nat.beq (mulT x x) oneT)
        (andB (allL A fun x => allL A fun y => commT x y)
          (allL P0K fun p => allL P0K fun q =>
            impB (Nat.beq (mulT p q) oneT) (allL A fun x => memN (mulT (mulT p x) q) A)))))))

@[expose] noncomputable def cntIn (l A : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (memN x A)) l

@[expose] noncomputable def chVF : Bool :=
  andB (chNE VK) (andB (chNE F0K) (andB (anyL F0K fun x => notB (memN x VK))
    (Nat.beq (cntIn VK F0K) (nat_lit 4))))

@[expose] noncomputable def chJ : Bool :=
  andB (nodupN JK) (andB (Nat.beq (lenN JK) (nat_lit 64)) (andB (allL JK memP)
    (andB (allL JK memJ) (andB (allN 16 fun u => allL F0m fun m => memN (mkT u m) JK)
      (allL JK fun x => allL JK fun y => memJ (mulT x y))))))

@[expose] noncomputable def chCent : Bool :=
  andB (allL P0K fun p => impB (allL VK (commT p)) (memN p VK))
    (allL P0K fun p => impB (allL F0K (commT p)) (memN p F0K))

@[expose] noncomputable def yT : Nat := mkT 0 5097

@[expose] noncomputable def sT : Nat := mkT 0 4680

@[expose] noncomputable def chY : Bool :=
  letB (mulT yT yT) fun y2 =>
  andB (memN (hiT yT) S0L) (andB (notB (Nat.beq yT oneT)) (andB (Nat.beq (mulT yT y2) oneT)
    (andB (allL JK fun j => memJ (mulT (mulT yT j) y2))
      (andB (allL JK fun j => impB (commT yT j) (Nat.beq j oneT))
        (andB (memP sT) (andB (notB (memJ sT)) (andB (Nat.beq (mulT sT sT) oneT)
          (andB (Nat.beq (mulT (mulT sT yT) sT) y2)
            (allL P0K fun p => orB (memJ p) (memJ (mulT sT p)))))))))))

@[expose] noncomputable def rankAt (IM : List Nat) (s j k l : Nat) : Bool :=
  letB (lAt IM j) fun a => letB (lAt IM k) fun b => letB (lAt IM l) fun c =>
    andB (Nat.blt j (lenN IM)) (andB (Nat.blt k (lenN IM)) (andB (Nat.blt l (lenN IM))
      (andB (commT s a) (andB (commT s b) (andB (commT s c) (andB (commT a b)
        (andB (commT a c) (andB (commT b c) (nodupN (span4T s a b c))))))))))

@[expose] noncomputable def chRankOn (IM : List Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun w _ ih l => List.rec (motive := fun _ => Bool) false
      (fun s t _ => andB (rankAt IM s w.1 w.2.1 w.2.2) (ih t)) l) W IM

@[expose] noncomputable def chOnly : Bool :=
  allL IPK fun a => impB (notB (memN a VK)) (allL IPK fun b => impB (commT a b)
    (allL IPK fun c => impB (andB (commT a c) (commT b c))
      (allL IPK fun d => impB (andB (commT a d) (andB (commT b d) (commT c d)))
        (orB (andB (memN a F0K) (andB (memN b F0K) (andB (memN c F0K) (memN d F0K))))
          (notB (nodupN (span4T a b c d)))))))

end CFSG.KC.Misc.T84

end
