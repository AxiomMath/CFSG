module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Monster.Existence.StdOdd.P5

abbrev E5 : Type := Fin 5 → ZMod 3

abbrev M5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 3)

@[expose] def gram : M5 :=
  !![2, 0, 2, 0, 0;
     0, 2, 0, 2, 0;
     2, 0, 2, 2, 0;
     0, 2, 2, 2, 2;
     0, 0, 0, 2, 2]

@[expose] def refl : Fin 6 → M5 := ![
  !![2, 0, 1, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0;
     0, 2, 0, 1, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     1, 0, 2, 1, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 1, 1, 2, 1;
     0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 1, 2],
  !![1, 0, 0, 0, 1;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 2;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 2]]

@[expose] def aMat : M5 :=
  !![1, 0, 0, 0, 0;
     0, 0, 1, 2, 1;
     0, 0, 1, 0, 0;
     0, 1, 1, 2, 1;
     0, 0, 0, 0, 1]

@[expose] def bMat : M5 :=
  !![0, 1, 0, 1, 1;
     0, 1, 0, 0, 0;
     0, 2, 0, 2, 0;
     1, 2, 0, 0, 2;
     0, 1, 1, 1, 1]

@[expose]
def dec (c : ℕ) : M5 := Matrix.of fun i j => (((c / 3 ^ (5 * i.val + j.val)) % 3 : ℕ) : ZMod 3)

@[expose] def pwList : List (List (Fin 2)) := [
  [], [0], [1], [0,0], [0,1], [1,0], [1,1], [0,0,1], [0,1,0], [0,1,1], [1,0,0], [1,0,1],
  [1,1,0], [0,0,1,0], [0,0,1,1], [0,1,0,0], [0,1,0,1], [0,1,1,0], [1,0,0,1], [1,0,1,0],
  [1,0,1,1], [1,1,0,0], [1,1,0,1], [0,0,1,0,0], [0,0,1,0,1], [0,0,1,1,0], [0,1,0,0,1],
  [0,1,0,1,0], [0,1,0,1,1], [0,1,1,0,0], [0,1,1,0,1], [1,0,0,1,0], [1,0,0,1,1], [1,0,1,0,0],
  [1,0,1,0,1], [1,1,0,0,1], [1,1,0,1,1], [0,0,1,0,0,1], [0,0,1,0,1,0], [0,0,1,0,1,1],
  [0,0,1,1,0,0], [0,0,1,1,0,1], [0,1,0,0,1,0], [0,1,0,0,1,1], [0,1,0,1,0,0], [0,1,0,1,0,1],
  [0,1,1,0,0,1], [0,1,1,0,1,1], [1,0,0,1,0,0], [1,0,0,1,0,1], [1,0,1,0,0,1], [1,0,1,0,1,1],
  [1,1,0,0,1,1], [0,0,1,0,0,1,0], [0,0,1,0,0,1,1], [0,0,1,0,1,0,0], [0,0,1,0,1,0,1],
  [0,0,1,1,0,0,1], [0,0,1,1,0,1,1], [0,1,0,0,1,0,0], [0,1,0,0,1,0,1], [0,1,0,1,0,0,1],
  [0,1,0,1,0,1,1], [0,1,1,0,0,1,1], [1,0,0,1,0,0,1], [1,0,0,1,0,1,1], [1,0,1,0,0,1,1],
  [0,0,1,0,0,1,0,0], [0,0,1,0,0,1,0,1], [0,0,1,0,1,0,0,1], [0,0,1,0,1,0,1,1],
  [0,0,1,1,0,0,1,1], [0,1,0,0,1,0,0,1], [0,1,0,0,1,0,1,1], [0,1,0,1,0,0,1,1],
  [1,0,0,1,0,0,1,1], [0,0,1,0,0,1,0,0,1], [0,0,1,0,0,1,0,1,1], [0,0,1,0,1,0,0,1,1],
  [0,1,0,0,1,0,0,1,1], [0,0,1,0,0,1,0,0,1,1]]

@[expose] def raList : List (Fin 81) := [
  1, 3, 5, 0, 8, 10, 12, 13, 15, 17, 2, 19, 21, 23, 25, 4, 27, 29, 31, 33, 28, 6, 30, 7, 38,
  40, 42, 44, 39, 9, 41, 48, 43, 11, 45, 46, 51, 53, 55, 20, 14, 22, 59, 54, 16, 56, 57, 62,
  18, 60, 61, 65, 66, 67, 32, 24, 34, 35, 70, 26, 68, 69, 73, 74, 72, 36, 75, 37, 49, 50, 77,
  78, 76, 47, 79, 52, 64, 58, 80, 63, 71]

@[expose] def rbList : List (Fin 81) := [
  2, 4, 6, 7, 9, 11, 0, 14, 16, 1, 18, 20, 22, 24, 3, 26, 28, 30, 32, 34, 5, 35, 36, 37, 39,
  41, 43, 45, 8, 46, 47, 49, 10, 50, 51, 52, 12, 54, 56, 13, 57, 58, 60, 15, 61, 62, 63, 17,
  64, 65, 66, 19, 21, 68, 23, 69, 70, 71, 25, 72, 73, 74, 27, 29, 75, 31, 33, 76, 77, 78, 38,
  40, 79, 42, 44, 48, 80, 53, 55, 59, 67]

@[expose] def pcodes : List ℕ := [
  282817489141, 284539392244, 420842637183, 283807571014, 420986168292, 106434735609,
  35217119614, 419795206581, 106190787180, 36379405138, 735395663730, 569747959780,
  37713863848, 104999825469, 36250245292, 735539194839, 570910179694, 35389358410,
  350214994597, 568757860348, 65609073622, 35948921251, 284252422060, 734348233128,
  570781078897, 35260198564, 351377221072, 569920139311, 63844185763, 37111206775,
  285586845625, 349224895138, 596766264355, 570479761174, 63169735771, 284008488121,
  419809539873, 351248120275, 570178399954, 63112371094, 36982046929, 284855083444,
  350387174101, 598488160897, 571641981088, 64891638874, 285730332175, 419953005372,
  350946796207, 597813769954, 63313228882, 105014211465, 420971781810, 350258014255,
  597756346228, 571512880291, 64159817644, 284998569994, 418762050222, 352109022682,
  599535614008, 65035125424, 105157683525, 421115306358, 597957263335, 734362566393,
  106176453159, 351979921885, 598803851827, 64303310755, 107453506215, 419924351208,
  599679100828, 734506031892, 106319925219, 735524808114, 598947345208, 733315076742,
  105128963508, 735668332662, 734477377512]

@[expose] def pwArr : Array (List (Fin 2)) := pwList.toArray

@[expose] def raArr : Array (Fin 81) := raList.toArray

@[expose] def rbArr : Array (Fin 81) := rbList.toArray

@[expose] def pcArr : Array ℕ := pcodes.toArray

@[expose] def pw (i : Fin 81) : List (Fin 2) := pwArr.getD i []

@[expose] def ra (i : Fin 81) : Fin 81 := raArr.getD i 0

@[expose] def rb (i : Fin 81) : Fin 81 := rbArr.getD i 0

@[expose] def pmat (i : Fin 81) : M5 := dec (pcArr.getD i 0)

@[expose] def step (c : Fin 2) (i : Fin 81) : Fin 81 := if c = 0 then ra i else rb i

@[expose] def walk : List (Fin 2) → Fin 81 → Fin 81
  | [], i => i
  | c :: w, i => walk w (step c i)

@[expose] def tbRaw (i j : Fin 81) : Fin 81 := walk (pw j) i

@[expose] def tbArr : Array (Fin 81) :=
  Array.ofFn (n := 6561) fun k => tbRaw ⟨k.val / 81, by omega⟩ ⟨k.val % 81, by omega⟩

@[expose] def tb (i j : Fin 81) : Fin 81 := tbArr.getD (81 * i.val + j.val) 0

@[expose] def extSet (S : Finset (Fin 81)) (x : Fin 81) : Finset (Fin 81) :=
  S ∪ S.image (tb x) ∪ S.image (fun s => tb x (tb x s))

@[expose] def sortFin (T : Finset (Fin 81)) : List (Fin 81) := T.sort (· ≤ ·)

@[expose] def closedL (l : List (Fin 81)) : Bool :=
  decide (l.length = 81) || l.all fun u => l.all fun v => l.contains (tb u v)

@[expose] def lattice : List (List (Fin 81)) := [
  [0], [0,1,3], [0,2,6], [0,13,25], [0,15,29], [0,20,32], [0,22,35], [0,24,66], [0,26,65],
  [0,27,80], [0,28,54], [0,30,57], [0,31,58], [0,33,63], [0,34,64], [0,39,43], [0,41,46],
  [0,45,76], [0,49,50], [0,56,72], [0,60,69], [0,61,68], [0,62,67], [0,1,3,20,28,32,39,43,54],
  [0,1,3,22,30,35,41,46,57], [0,1,3,34,45,56,64,72,76], [0,1,3,49,50,60,61,68,69],
  [0,2,6,27,45,62,67,76,80], [0,13,25,26,33,45,63,65,76], [0,15,24,29,31,45,58,66,76],
  [0,20,22,32,34,35,49,50,64], [0,20,30,32,45,57,60,69,76], [0,20,32,41,46,56,61,68,72],
  [0,22,28,35,45,54,61,68,76], [0,22,35,39,43,56,60,69,72], [0,28,30,49,50,54,56,57,72],
  [0,28,34,41,46,54,60,64,69], [0,30,34,39,43,57,61,64,68], [0,39,41,43,45,46,49,50,76],
  [0,4,16,21,45,53,70,75,76], [0,5,14,19,45,59,71,73,76], [0,7,12,37,44,45,51,76,79],
  [0,8,11,40,42,45,52,76,77], [0,9,10,38,45,47,48,76,78], [0,17,18,23,36,45,55,74,76],
  [0,1,3,20,22,28,30,32,34,35,39,41,43,45,46,49,50,54,56,57,60,61,64,68,69,72,76],
  [0,2,6,13,15,24,25,26,27,29,31,33,39,41,43,45,46,49,50,58,62,63,65,66,67,76,80],
  [0,4,5,14,16,17,18,19,21,23,36,39,41,43,45,46,49,50,53,55,59,70,71,73,74,75,76],
  [0,7,8,9,10,11,12,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,76,77,78,79],
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,
   35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,
   67,68,69,70,71,72,73,74,75,76,77,78,79,80]]

@[expose] def checkLat (l : List (Fin 81)) (x : Fin 81) : Bool :=
  let T := sortFin (extSet l.toFinset x)
  l.contains x || !(closedL T) || lattice.contains T

@[expose]
def latticeClosedB : Bool := lattice.all fun l => (List.finRange 81).all fun x => checkLat l x

@[expose] def elemAbL (l : List (Fin 81)) : Bool :=
  l.all fun i => decide (tb (tb i i) i = 0) && l.all fun j => decide (tb i j = tb j i)

@[expose] def fixedCardL (l : List (Fin 81)) : ℕ :=
  (Finset.univ.filter fun v : E5 => ∀ i ∈ l, (pmat i).mulVec v = v).card

@[expose] def elemCheckB : Bool :=
  lattice.all fun l => !(elemAbL l) || decide (l = [0]) || decide (l.length * fixedCardL l ≤ 81)

@[expose] def eA5 : E5 := ![0, 0, 0, 0, 1]

@[expose] def eA4 : E5 := ![0, 0, 0, 1, 0]

@[expose] def selT : Fin 5 → Fin 81 := ![0, 1, 2, 3, 5]

@[expose] def wsT (k : Fin 5) : E5 := (pmat (selT k)).mulVec eA5

@[expose] def e1 : E5 := ![0, 1, 0, 1, 0]

@[expose] def sel1 : Fin 4 → Fin 81 := ![0, 1, 2, 6]

@[expose] def ws1 (k : Fin 4) : E5 := (pmat (sel1 k)).mulVec e1

@[expose] def closureStep (gens : List (Fin 81)) (S : Finset (Fin 81)) : Finset (Fin 81) :=
  S ∪ S.biUnion fun s => (gens.map (tb s)).toFinset

@[expose] def closureFin (gens : List (Fin 81)) : Finset (Fin 81) := (closureStep gens)^[8] {0}

structure Cert27 where
  gens : List (Fin 81)
  mods : List E5
  sel : Fin 5 → Fin 81 × E5

@[expose] def Cert27.vec (c : Cert27) (k : Fin 5) : E5 := (pmat (c.sel k).1).mulVec (c.sel k).2

abbrev Cert27Ok (l : List (Fin 81)) (c : Cert27) : Prop :=
  closureFin c.gens = l.toFinset ∧ c.gens.length + c.mods.length ≤ 4 ∧ (∀ g ∈ c.gens, g ∈ l) ∧
    (∀ k : Fin 5, (c.sel k).1 ∈ l ∧ (c.sel k).2 ∈ c.mods) ∧
    (∀ x : Fin 5 → ZMod 3, ∑ i, x i • c.vec i = 0 → x = 0)

@[expose] def cert27 : List Cert27 := [
  ⟨[1, 20, 22],
   [eA5],
   ![(0, eA5), (1, eA5), (3, eA5), (20, eA5), (22, eA5)]⟩,
  ⟨[2, 13],
   [eA5, eA4],
   ![(0, eA5), (0, eA4), (2, eA5), (2, eA4), (13, eA4)]⟩,
  ⟨[4, 5],
   [eA5],
   ![(0, eA5), (4, eA5), (5, eA5), (14, eA5), (16, eA5)]⟩,
  ⟨[7, 8],
   [eA5],
   ![(0, eA5), (7, eA5), (8, eA5), (9, eA5), (10, eA5)]⟩]

@[expose] def cert27CheckB : Bool :=
  lattice.all fun l => decide (l.length ≠ 27) || cert27.any fun c => decide (Cert27Ok l c)

@[expose] def bil (u v : E5) : ZMod 3 := dotProduct u (gram.mulVec v)

@[expose] def alpha : Fin 6 → E5 :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1],
    ![1, 0, 2, 0, 1]]

@[expose] def rootVecs : Finset E5 := Finset.univ.filter fun α => bil α α = 2

@[expose] def rk (x : E5) : ℕ := (rootVecs.filter fun α => bil α x = 0).card

@[expose] def rkFibre (c : ℕ) : Finset E5 := Finset.univ.filter fun x => x ≠ 0 ∧ rk x = c

@[expose]
def encV (x : E5) : ℕ := (x 0).val + 3 * (x 1).val + 9 * (x 2).val + 27 * (x 3).val + 81 * (x 4).val

@[expose] def decV (n : ℕ) : E5 := ![((n % 3 : ℕ) : ZMod 3), ((n / 3 % 3 : ℕ) : ZMod 3),
  ((n / 9 % 3 : ℕ) : ZMod 3), ((n / 27 % 3 : ℕ) : ZMod 3), ((n / 81 % 3 : ℕ) : ZMod 3)]

@[expose] def vstep (S : Finset ℕ) : Finset ℕ :=
  S ∪ S.biUnion fun n =>
    (Finset.univ : Finset (Fin 6)).image fun i => encV ((refl i).mulVec (decV n))

@[expose] def orbitFin (n : ℕ) (v : E5) : Finset ℕ := vstep^[n] {encV v}

@[expose] def vRoot : E5 := ![0, 0, 0, 0, 1]

@[expose] def vSing : E5 := ![0, 0, 0, 1, 2]

@[expose] def vNorm : E5 := ![0, 0, 1, 0, 1]

end CFSG.Monster.Existence.StdOdd.P5
