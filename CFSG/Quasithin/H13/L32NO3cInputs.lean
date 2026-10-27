module

public import CFSG.Quasithin.H13.L32NO3Inputs

public section

namespace CFSG.Quasithin.H13.O3cCert

open Mat8Cert O3Cert

@[expose] def p0G : List (List ℕ) :=
  [[1, 2, 4, 8, 17, 34, 68, 136], [1, 2, 4, 8, 18, 35, 72, 140], [1, 2, 5, 10, 16, 32, 80, 160],
    [1, 2, 6, 11, 16, 32, 96, 176]]

@[expose] def p0E : List (List ℕ) := elemsOf p0G

@[expose] def fixS : List ℕ := [1, 2, 3]

@[expose] def tS : List ℕ := [1, 2, 12, 4, 32, 48, 64, 128]

@[expose] def tI : List ℕ := [1, 2, 8, 12, 48, 16, 64, 128]

@[expose] def p0B : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  subB p0G p0E && p0E.length == 16 && p0G.all h3.contains &&
    ((List.range 256).all fun v => !(p0G.all fun g => mv8 g v == v) || v == 0 || fixS.contains v) &&
    h3.contains tS && mul8 tS tI == one8 && fixS.all fun v => mv8 tS v == v

@[expose] def c4B : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  let hF : Std.HashSet (List ℕ) := Std.HashSet.ofList om3FE
  fixS.all fun v => omNE.all fun x =>
    !(mv8 x v == v) || !(mul8 x x == one8) || h3.contains x ||
      (let c := mul8 (mul8 tS x) (mul8 tI x)
       !(mul8 c c == one8)) ||
      (h3.contains (mul8 sfG x) && !(hF.contains x) && fullImgB x)

@[expose] def c5B : Bool :=
  let h3 : Std.HashSet (List ℕ) := Std.HashSet.ofList om3E
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList p0E
  fixS.all fun v => omNE.all fun x =>
    !(mv8 x v == v) || !(mul8 x x == one8) || !(h3.contains (mul8 sfG x)) ||
      !(p0E.all fun p => hP.contains (mul8 (mul8 x p) x)) ||
      decide ((p0E.filter fun p => mul8 p x == mul8 x p).length ≤ 4)

@[expose] def o3cCheck : Bool := p0B && c4B && c5B

end CFSG.Quasithin.H13.O3cCert
