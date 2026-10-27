module

public import CFSG.Quasithin.EmptyFaithful.SBc5FourRed
public import CFSG.Quasithin.EmptyFaithful.SBc5Orth
public import CFSG.Quasithin.EmptyFaithful.SBc5S8

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem s8ModelFact_holds : S8ModelFact := by
  intro T hT w hw hfix K hK
  have hKeq : K = alternatingGroup (Fin 8) ⊓ SBc5S8.s8Stab w := by
    ext σ
    rw [hK σ, Subgroup.mem_inf]
    rfl
  rw [hKeq]
  exact SBc5S8.s8_stab_isMaxParabolic2 hT hw hfix

namespace SBc5

theorem input32Four_holds (h113 : StageLemma14113) (hPre : Input32Preamble) : Input32Four :=
  input32Four_of_residue h113 hPre (orthoFixedParabolic_of_model s8ModelFact_holds)

end SBc5

end CFSG.Quasithin
