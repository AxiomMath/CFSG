module

public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Vocabulary

variable {G : Type} [Group G]

@[expose] noncomputable def secRank (N L : Subgroup G) : ℕ := rkIdx (L.subgroupOf N)

end Vocabulary

section Hyp319

variable {G : Type} [Group G] [Finite G]

structure Hyp319 (T M M₀ H V : Subgroup G) : Prop extends Hyp315Base T M M₀ H V where
  caseII : Hyp315.CaseII M H V
  q_eq : qInt M₀ V reduced.2.2.1 = 2
  unique : IsUniqueM M₀ M
  le_pCore : V ≤ pCoreOf 2 H
  not_dualFF : ¬ IsDualFFInt M₀ V reduced.2.2.1

end Hyp319

end CFSG.Quasithin
