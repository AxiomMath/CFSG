module

public import CFSG.Sporadic.Schreier.TitsQTStrong
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvCore

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT

theorem zpUniq_titsD :
    ZPUniq titsD := by
  refine zpUniq_of_central_subset titsD_center (titsSylow : Subgroup titsD) titsSylow.isPGroup'
    titsSylow.not_dvd_index titsZD fun c hc hcc => ?_
  exact titsSylow_central_eq c hc fun p hp => (hcc p hp).symm

theorem zpUniq_tits
    {Q : Type} [Group Q] (h : CFSG.Blueprint.ReeTitsModel Q .Tits 2 1) : ZPUniq Q := by
  obtain ⟨e⟩ := titsModelEquiv Q 2 1 h
  refine ZPUniq.of_mulEquiv e ?_
  exact zpUniq_titsD

end CFSG.Quasithin.ZPInv
