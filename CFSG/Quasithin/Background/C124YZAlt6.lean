module

public import CFSG.Quasithin.Background.C124YZActSix
public import CFSG.Quasithin.Background.C124YZStar
public import CFSG.Quasithin.Background.C124Interface

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem spec4bAlt6c_holds : Spec4bAlt6c := by
  intro G _ _ X T V L R m hV E hcase hR
  obtain ⟨hm, π, hreal, hπ⟩ := hcase
  subst hm
  obtain ⟨ι, β, hι, hιπ, hβs, hβe⟩ := YZ.transport_six E hreal hπ
  exact YZ.exists_starZ3 E YZ.modelFactsSix hR.le π hπ ι hι hιπ β hβs hβe

end CFSG.Quasithin.C124
