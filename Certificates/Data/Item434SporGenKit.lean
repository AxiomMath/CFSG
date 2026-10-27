module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Monster.B.Co2.Native

@[expose] def powN (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => compA n t (powN n t k)

@[expose] def commN (n : ℕ) (t u : Array ℕ) : Bool := eqA n (compA n t u) (compA n u t)

@[expose] def pN (n : ℕ) (e₁ e₂ : Array ℕ) (ab : ℕ × ℕ) : Array ℕ :=
  compA n (powN n e₁ ab.1) (powN n e₂ ab.2)

@[expose] def e9Check (n : ℕ) (e₁ e₂ : Array ℕ) : Bool :=
  isInvA n e₁ (invCand n e₁) && isInvA n e₂ (invCand n e₂) &&
    eqA n (powN n e₁ 3) (idA n) && eqA n (powN n e₂ 3) (idA n) && commN n e₁ e₂ &&
    !eqA n e₁ (idA n) && !eqA n e₂ (idA n) && !eqA n e₂ e₁ && !eqA n e₂ (powN n e₁ 2)

@[expose] def sigCheck (n : ℕ) (σ : Array (Array ℕ)) (ords : List ℕ) (ps : List (ℕ × ℕ))
    (e₁ e₂ : Array ℕ) : Bool :=
  allLt σ.size fun i =>
    eqA n (powN n σ[i]! (ords.getD i 0)) (idA n) && !(ords.getD i 0 % 3 == 0) &&
      commN n σ[i]! (pN n e₁ e₂ (ps.getD i (0, 0))) &&
      !eqA n (pN n e₁ e₂ (ps.getD i (0, 0))) (idA n)

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
