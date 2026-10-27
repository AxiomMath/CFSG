module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Alt
public import CFSG.Milestones.ASVolI.C61.CS

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin

@[expose] def C61Lin2Alternatives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), burnsideC56_CS G T M H S L →
    conjJoin S L = L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) → C61Six T H S L

end CFSG.QuasithinUnique.burnsideC56_P
