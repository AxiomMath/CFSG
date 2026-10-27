module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import CFSG.Quasithin.H13.L32NM22Inputs

public section

namespace CFSG.Quasithin.H13.Q1447Cert

open Mat8Cert

@[expose] def invol8 (x : List ℕ) : Bool := !(x == one8) && mul8 x x == one8

@[expose] def bigImg8 (x : List ℕ) : Bool :=
  let S := spanN (O3Cert.imgBasis x)
  decide (4 < S.length) && decide ((S.mergeSort).IsChain (· < ·)) && S.all fun u => decide (u < 256)

@[expose] def invol12 (x : List ℕ) : Bool :=
  !(x == MatNCert.oneN 12) && MatNCert.mulN x x == MatNCert.oneN 12

@[expose] def imgBasis12 (x : List ℕ) : List ℕ :=
  (List.range 12).map fun j => MatNCert.mvN x (2 ^ j) ^^^ 2 ^ j

@[expose] def bigImg12 (x : List ℕ) : Bool :=
  let S := MatNCert.spanN (imgBasis12 x)
  decide (4 < S.length) && decide ((S.mergeSort).IsChain (· < ·)) &&
    S.all fun u => decide (u < 4096)

@[expose] def s7InvB : Bool := S7Cert.s7E.all fun x => !(invol8 x) || bigImg8 x

@[expose] def g5InvB : Bool := G5Cert.gSE.all fun x => !(invol8 x) || bigImg8 x

@[expose] def m22InvB : Bool := M22Cert.pE.all fun x => !(invol12 x) || bigImg12 x

@[expose] def o3InvB (c : ℕ) : Bool :=
  (O3Cert.gamE c).all fun x => !(invol8 x) || bigImg8 x ||
    !((List.range 256).any fun n => mv8 x n ^^^ n == O3Cert.vS c)

@[expose] def s7Conj : List (List ℕ × List ℕ × List ℕ) :=
  [([224, 80, 128, 112, 5, 6, 13, 7], [160, 144, 176, 80, 13, 10, 15, 4],
      [3, 2, 12, 8, 16, 48, 64, 192]),
    ([240, 128, 96, 160, 1, 15, 5, 6], [16, 208, 80, 176, 7, 10, 14, 2],
      [3, 2, 12, 8, 16, 48, 64, 192]),
    ([128, 224, 64, 176, 10, 3, 7, 1], [128, 160, 96, 176, 14, 7, 4, 1],
      [15, 10, 12, 8, 16, 48, 80, 240]),
    ([192, 224, 16, 160, 10, 14, 1, 12], [64, 160, 48, 176, 4, 3, 10, 11],
      [5, 10, 4, 8, 16, 32, 80, 160])]

@[expose] def g5Conj : List (List ℕ × List ℕ × List ℕ) :=
  [([13, 6, 9, 14, 208, 96, 144, 224], [14, 7, 5, 10, 224, 112, 80, 160],
      [1, 2, 5, 10, 17, 34, 85, 170]),
    ([136, 68, 51, 34, 128, 64, 48, 32], [204, 136, 34, 17, 192, 128, 32, 16],
      [1, 2, 5, 10, 17, 34, 85, 170]),
    ([176, 96, 80, 240, 11, 6, 5, 15], [208, 176, 144, 112, 13, 11, 9, 7],
      [1, 2, 5, 10, 16, 32, 80, 160]),
    ([96, 176, 192, 64, 6, 11, 12, 4], [112, 144, 128, 192, 7, 9, 8, 12],
      [1, 2, 5, 10, 17, 34, 85, 170])]

@[expose] def conjOf (L : List (List ℕ × List ℕ × List ℕ)) : List (List ℕ) :=
  L.map fun t => mul8 (mul8 t.1 t.2.2) t.2.1

@[expose] def conjB (L : List (List ℕ × List ℕ × List ℕ)) (Γ Y : List (List ℕ)) (m : ℕ) : Bool :=
  let hG : Std.HashSet (List ℕ) := Std.HashSet.ofList Γ
  let hY : Std.HashSet (List ℕ) := Std.HashSet.ofList Y
  let N := elemsOf (conjOf L)
  let hN : Std.HashSet (List ℕ) := Std.HashSet.ofList N
  (L.all fun t => hG.contains t.1 && mul8 t.1 t.2.1 == one8 && hY.contains t.2.2) &&
    subB (conjOf L) N && Γ.all fun x => !(O3Cert.pow8 x m == one8) || hN.contains x

@[expose] def s7KB : Bool := conjB s7Conj S7Cert.s7E (elemsOf S7Cert.n8G) 315

@[expose] def g5KB : Bool := conjB g5Conj G5Cert.gSE G5Cert.zPG 45

@[expose] def m22Words : List (List ℕ × List ℕ × List ℕ) :=
  [([1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
      [2648, 124, 4, 103, 2633, 1679, 3239, 2043, 197, 2456, 1028, 3856],
      M22Cert.gG.getD 0 []),
    ([0, 1, 1, 1, 0, 1, 0, 1, 0],
      [1809, 1359, 4, 254, 1796, 655, 1872, 1894, 498, 1506, 1028, 2048],
      MatNCert.mulN (M22Cert.gG.getD 1 []) (M22Cert.gG.getD 1 []))]

@[expose] def m22KB : Bool :=
  let hE : Std.HashSet (List ℕ) := Std.HashSet.ofList M22Cert.e0E
  m22Words.all fun t =>
    let X := MatNCert.evalW 12 M22Cert.gG t.1
    let Xi := MatNCert.evalW 12 M22Cert.gInv t.1.reverse
    hE.contains t.2.1 && MatNCert.mulN X Xi == MatNCert.oneN 12 &&
      MatNCert.mulN (MatNCert.mulN X t.2.1) Xi == t.2.2

@[expose] def q1447Check : Bool :=
  s7InvB && g5InvB && m22InvB && [0, 1].all o3InvB && s7KB && g5KB && m22KB

end CFSG.Quasithin.H13.Q1447Cert
