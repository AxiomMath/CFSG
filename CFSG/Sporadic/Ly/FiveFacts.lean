module

public import CFSG.Sporadic.Schreier.LyData
public import CFSG.RankThree.Native.LyFiveProg
public import CFSG.RankThree.Native.LyFiveTheory

public noncomputable section

namespace CFSG.Sporadic.Ly.Omega

open CFSG.Sporadic.LySchreier CFSG.RankThree.Native CFSG.RankThree.PartOne.LyFive

@[expose] def fiveA [LySeed] : J := fiveSlpRun lyFiveProg (fiveInit a b) 1

@[expose] def fiveB [LySeed] : J := fiveSlpRun lyFiveProg (fiveInit a b) 2

@[expose] def fiveX [LySeed] : J := fiveA ^ 5

@[expose] def fiveV [LySeed] (i : Fin 4) : J := fiveWord fiveA fiveB (lyFiveVWords i)

@[expose] def fiveY [LySeed] : J := fiveV 0 * fiveV 1

@[expose] def fiveEl [LySeed] (n : ℕ) : J :=
  fiveA ^ (n / 3125) * fiveNF fiveX fiveV (fiveDigits (n % 3125)).1 (fiveDigits (n % 3125)).2

@[expose] def LyFiveFacts [LySeed] : Prop :=
  (evalWord seedFam xWord)⁻¹ * fiveX * evalWord seedFam xWord ∈ lyH ∧
    (evalWord seedFam y3Word)⁻¹ * fiveY * evalWord seedFam y3Word ∈ lyH ∧
    (evalWord seedFam y1Word)⁻¹ * fiveY * evalWord seedFam y1Word ∈ lyH ∧
    (∃ g : J, g * lyTA * g⁻¹ = fiveX) ∧ (∃ g : J, g * lyTB * g⁻¹ = fiveY) ∧
    ∀ n < 15625, fiveEl n ≠ 1 → fiveEl n ^ 5 = 1 →
      ∃ g : J, ∃ r ∈ ({fiveX, fiveY} : Set J), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ g * fiveEl n * g⁻¹ = r ^ m

end CFSG.Sporadic.Ly.Omega
