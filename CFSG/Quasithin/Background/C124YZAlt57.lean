module

public import CFSG.Quasithin.Background.C124YZActOdd
public import CFSG.Quasithin.Background.C124YZStar
public import CFSG.Quasithin.Background.C124Interface

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem spec4bAlt5_holds : Spec4bAlt5 := by
  intro G _ _ X T V L R m hV E hcase
  obtain ⟨hm, π, hreal, hπ⟩ := hcase
  subst hm
  obtain ⟨ι, β, hι, hιπ, hβs, hβe⟩ := YZ.transport_odd E (by decide) (by norm_num) hreal hπ
  exact YZ.exists_starZ3 E (YZ.modelFactsOdd (by decide) _) le_rfl π hπ ι hι hιπ β hβs hβe

theorem spec4bAlt7_holds : Spec4bAlt7 := by
  intro G _ _ X T V L R m hV E hcase
  obtain ⟨hm, π, hreal, hπ⟩ := hcase
  subst hm
  obtain ⟨ι, β, hι, hιπ, hβs, hβe⟩ := YZ.transport_odd E (by decide) (by norm_num) hreal hπ
  exact YZ.exists_starZ3 E (YZ.modelFactsOdd (by decide) _) le_rfl π hπ ι hι hιπ β hβs hβe

end CFSG.Quasithin.C124
