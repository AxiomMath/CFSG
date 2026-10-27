module

public import CFSG.Quasithin.AppendixH.H16.SextetData

public section

namespace CFSG.ASVolI.H16

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU
  CFSG.Quasithin.H.LU24

theorem ctr_lt : ∀ i < 6, ctr i < 2 ^ 11 := by
  decide +kernel

theorem xorCtr_lt : ∀ J < 64, xorCtr J < 2 ^ 11 := by
  decide +kernel

theorem xorCtr_par : ∀ J < 64, popPar 11 (xorCtr J &&& 1192) = false := by
  decide +kernel

theorem xorCtr_zero : xorCtr 0 = 0 := by
  decide +kernel

theorem xorCtr_inj : ∀ J < 64, ∀ J' < 64, (xorCtr J ^^^ xorCtr J') ∈ uSMasks → J = J' := by
  decide +kernel

end CFSG.ASVolI.H16
