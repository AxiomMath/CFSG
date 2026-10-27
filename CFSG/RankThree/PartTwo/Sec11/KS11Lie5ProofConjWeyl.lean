module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofOutWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2Data

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.E6

abbrev Exp3 := Fin TwistTag.D4.tag.rank → ZMod 3

@[expose] def tup {L : Type} [Field L] (ζ : Lˣ) (β : Exp3) : Fin TwistTag.D4.tag.rank → Lˣ :=
  fun i => ζ ^ (β i).val

@[expose] def sExp (j : Fin TwistTag.D4.tag.rank) (β : Exp3) : Exp3 :=
  fun i => β i + ((-TwistTag.D4.tag.cartan j i : ℤ) : ZMod 3) * β j

@[expose] def wordExp (ω : List (Fin TwistTag.D4.tag.rank)) (β : Exp3) : Exp3 :=
  ω.foldr sExp β

@[expose] def tabExp (e : ℕ) (β : Exp3) : Exp3 :=
  fun i => ∑ j, ((colOf e i j : ℤ) : ZMod 3) * β j

@[expose] def rhoExp (β : Exp3) : Exp3 :=
  fun i => β (TwistTag.D4.perm.symm i)

@[expose] def gA : Exp3 := ![0, 1, 0, 1]

@[expose] def gB : Exp3 := ![0, 0, 1, 0]

@[expose] def typeWords : List (List (Fin TwistTag.D4.tag.rank)) :=
  [[], [1], [2], [3], [1, 2], [2, 0], [2, 1], [2, 3], [3, 1], [3, 2], [1, 2, 0], [1, 2, 3],
    [2, 1, 0], [2, 3, 0], [2, 3, 1], [3, 1, 2], [3, 2, 0], [3, 2, 1], [1, 2, 3, 0], [1, 2, 3, 2],
    [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 0], [2, 3, 1, 2], [3, 1, 2, 0], [3, 1, 2, 1],
    [3, 2, 1, 0], [1, 2, 3, 0, 2], [1, 2, 3, 2, 0], [1, 2, 3, 2, 1], [2, 1, 0, 2, 3],
    [2, 3, 0, 2, 1], [2, 3, 1, 0, 2], [2, 3, 1, 2, 0], [3, 1, 2, 1, 0], [3, 2, 1, 0, 2],
    [1, 2, 3, 0, 2, 0], [1, 2, 3, 0, 2, 1], [1, 2, 3, 2, 1, 0], [2, 1, 0, 2, 3, 2],
    [2, 3, 1, 0, 2, 0], [2, 3, 1, 0, 2, 1], [3, 2, 1, 0, 2, 0], [3, 2, 1, 0, 2, 3],
    [1, 2, 3, 0, 2, 1, 0], [1, 2, 3, 2, 1, 0, 2], [2, 1, 0, 2, 3, 2, 0], [2, 1, 0, 2, 3, 2, 1],
    [2, 3, 1, 0, 2, 1, 0], [3, 2, 1, 0, 2, 3, 0], [1, 2, 3, 2, 1, 0, 2, 1],
    [2, 1, 0, 2, 3, 2, 1, 0], [3, 2, 1, 0, 2, 3, 0, 2], [2, 1, 0, 2, 3, 2, 1, 0, 2],
    [3, 2, 1, 0, 2, 3, 0, 2, 1]]

theorem typeCheck_spec : ∀ β : Exp3, β = 0 ∨
    (d4WeylTab.all fun e => decide (tabExp e (rhoExp β) ≠ β ∧
      tabExp e (fun i => 2 * rhoExp β i) ≠ β)) ∨
    (typeWords.any fun ω => decide (wordExp ω β = gA ∨ wordExp ω β = gB)) := by
  decide +kernel

@[expose] def wordVec (ω : List (Fin TwistTag.D4.tag.rank)) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    Fin TwistTag.D4.tag.rank → ℤ :=
  ω.foldr (reflect TwistTag.D4.tag) v

@[expose] def wordsA : List (List (Fin TwistTag.D4.tag.rank)) :=
  [[], [0], [2], [0, 2], [2, 0], [0, 2, 0]]

@[expose] def wordsB : List (List (Fin TwistTag.D4.tag.rank)) :=
  [[], [0], [1], [3], [0, 1], [0, 3], [1, 3], [0, 1, 3]]

@[expose] def stabCheckA : Bool :=
  d4WeylTab.all fun e => !(decide (tabExp e gA = gA)) ||
    wordsA.any fun ω => decide (∀ i, colOf e i = wordVec ω (Pi.single i 1))

theorem stabCheckA_eq : stabCheckA = true := by decide +kernel

@[expose] def stabCheckB : Bool :=
  d4WeylTab.all fun e => !(decide (tabExp e gB = gB)) ||
    wordsB.any fun ω => decide (∀ i, colOf e i = wordVec ω (Pi.single i 1))

theorem stabCheckB_eq : stabCheckB = true := by decide +kernel

theorem kerCheckA_spec : ∀ k : Fin 24, (∑ j, ((d4RootVec k j : ℤ) : ZMod 3) * gA j = 0) →
    ∃ i j : Fin 3, i ≠ j ∧ d4RootVec k = chainRoot d4ChainA2 i j := by
  decide +kernel

theorem kerCheckB_spec : ∀ k : Fin 24, (∑ j, ((d4RootVec k j : ℤ) : ZMod 3) * gB j = 0) →
    k = 0 ∨ k = 4 ∨ k = 1 ∨ k = 6 ∨ k = 3 ∨ k = 10 := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
