module

public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin

open CFSG.Open

structure quasithinQTFE14Cat (G : Type) [Group G] [Finite G] (T Mc : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  faithful_empty : ∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L
  mc_max : quasithinIsMaxTwoLocal Mc
  t_le_mc : T ≤ Mc
  centralizer_le_mc : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc
  mc_unique : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M → M = Mc
  two_maximal : ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ T ≤ M ∧ M ≠ Mc

end CFSG.Quasithin
