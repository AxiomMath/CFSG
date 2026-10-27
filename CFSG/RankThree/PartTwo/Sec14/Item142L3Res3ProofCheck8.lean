module

public import CFSG.LieType.SeitzGeneration.OuterSmallCheck

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open CFSG.LieType.SeitzGeneration.HeisSmall

variable {L : Type} [Field L] [DecidableEq L] [Fintype L]

@[expose] def torusLineList (ω α : L) : List (M3 L) :=
  [cM3 α, cM3 α * dM3 ω, cM3 α * (dM3 ω * dM3 ω)]

@[expose] def TorusGenOk (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Prop :=
  G.det = 1 ∧ (G.map (· ^ q)).transpose * G = 1 ∧ ∃ M ∈ lines, G * M = M * G

instance (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Decidable (TorusGenOk q lines G) := by
  unfold TorusGenOk
  infer_instance

@[expose] def torusEntryOk (q : ℕ) (ω : L) (letters : List (M3 L)) (e : OuterEntry L) : Bool :=
  e.gens.all (fun G => decide (TorusGenOk q (torusLineList ω e.alpha) G)) &&
    decide (e.words.map (evalW e.gens) = letters)

@[expose] def torusCheck (q : ℕ) (ω : L) (letters : List (M3 L)) (table : List (OuterEntry L)) :
    Bool :=
  table.all (torusEntryOk q ω letters) && decide (AlphaCovered q table)

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
