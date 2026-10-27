module

public import Certificates.Data.Item434SporGenMathieu
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen

@[expose] def m22E12 : Array ℕ :=
  #[0, 18, 17, 15, 1, 5, 21, 20, 12, 6, 10, 2, 16, 13, 3, 14, 8, 11, 4, 7, 19, 9]

@[expose] def m22EArr (j : ℕ) : Array ℕ :=
  if j = 0 then m22E1 else if j = 1 then m22E2 else m22E12

@[expose] def m22VArrs : Array (Array ℕ) :=
  #[
    #[8, 18, 2, 3, 10, 6, 5, 20, 0, 21, 4, 11, 16, 19, 14, 15, 12, 17, 1, 13, 7, 9],
    #[12, 10, 2, 3, 18, 21, 9, 13, 16, 6, 1, 11, 0, 7, 14, 15, 8, 17, 4, 20, 19, 5],
    #[2, 20, 0, 7, 9, 5, 15, 3, 8, 4, 10, 17, 12, 13, 18, 6, 16, 11, 14, 21, 1, 19],
    #[11, 15, 17, 9, 7, 5, 20, 4, 8, 3, 10, 0, 12, 13, 19, 1, 16, 2, 21, 14, 6, 18],
    #[5, 7, 2, 3, 19, 0, 8, 1, 6, 16, 13, 11, 21, 10, 14, 15, 9, 17, 20, 4, 18, 12],
    #[10, 12, 2, 3, 8, 13, 19, 21, 4, 20, 0, 11, 1, 5, 14, 15, 18, 17, 16, 6, 9, 7]]

@[expose] def m22VArr (k : ℕ) : Array ℕ := m22VArrs[k]!

@[expose] def m22VWordA : List ℕ := [3, 1, 2, 5, 3, 5, 2, 1, 3]

@[expose] def m22VWordB : List ℕ := [5, 3, 2, 0, 2, 5, 3, 1, 2, 4, 1]

@[expose] def m22VProd : List ℕ → Array ℕ
  | [] => idA 22
  | k :: w => compA 22 (m22VArr k) (m22VProd w)

@[expose] def m22VEltCheck : Bool :=
  eqA 22 (compA 22 m22E1 m22E2) m22E12 &&
    allLt 6 (fun k => isInvA 22 (m22VArr k) (invCand 22 (m22VArr k)) &&
      siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 (m22VArr k) &&
      eqA 22 (compA 22 (m22VArr k) (m22VArr k)) (idA 22)) &&
    allLt 3 fun j =>
      !(eqA 22 (m22EArr j) (idA 22)) &&
        eqA 22 (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))
          (compA 22 (m22VArr (2 * j + 1)) (m22VArr (2 * j))) &&
        eqA 22 (compA 22 (m22VArr (2 * j)) (m22EArr j)) (compA 22 (m22EArr j) (m22VArr (2 * j))) &&
        eqA 22 (compA 22 (m22VArr (2 * j + 1)) (m22EArr j))
          (compA 22 (m22EArr j) (m22VArr (2 * j + 1)))

@[expose] def m22Fn (t : Array ℕ) (x : Fin 22) : Fin 22 :=
  ⟨t[x.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

@[expose] def m22Intertw (g u w : Fin 22 → Fin 22) : Bool :=
  (List.finRange 22).all fun x => g (u x) == w (g x)

@[expose] def m22ConjIn (g u v v' v'' : Fin 22 → Fin 22) : Bool :=
  m22Intertw g u v || m22Intertw g u v' || m22Intertw g u v''

@[expose] def m22NormB (j : ℕ) (g : Fin 22 → Fin 22) : Bool :=
  m22ConjIn g (m22Fn (m22VArr (2 * j))) (m22Fn (m22VArr (2 * j))) (m22Fn (m22VArr (2 * j + 1)))
      (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))) &&
    m22ConjIn g (m22Fn (m22VArr (2 * j + 1))) (m22Fn (m22VArr (2 * j)))
      (m22Fn (m22VArr (2 * j + 1))) (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1))))

@[expose] def m22BadB (j : ℕ) (g : Fin 22 → Fin 22) : Bool :=
  m22Intertw g (m22Fn (m22EArr j)) (m22Fn (m22EArr j)) && !(m22NormB j g)

@[expose] def m22VGenCheck : Bool :=
  (m22VWordA ++ m22VWordB).all (fun k => decide (k < 6)) &&
    eqA 22 (m22VProd m22VWordA) m22GenA && eqA 22 (m22VProd m22VWordB) m22GenB

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
