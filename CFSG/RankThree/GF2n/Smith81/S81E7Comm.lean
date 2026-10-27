module

public import CFSG.RankThree.GF2n.Smith81.S81E7Lam

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

@[expose] def adjM (a b : Fin e7Data.d) : Prop := adjD a b ∧ pr a theta = -1

instance (a b : Fin e7Data.d) : Decidable (adjM a b) := by unfold adjM; infer_instance

end CFSG.RankThree.GF2n.Smith81.E7Model
