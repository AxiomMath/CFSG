
module


public import CFSG.Sporadic.Ly.Action

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th.Native (ap invT invOK allIn)
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose, instance_reducible] def lyXAction :
    MulAction J (Fin 8835156) := idxInst

@[expose] def lyAct : J →* Equiv.Perm (Fin 8835156) :=
  @MulAction.toPermHom J (Fin 8835156) _ lyXAction

theorem lyAct_apply (g : J) (i : Fin 8835156) :
    lyAct g i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem lyAct_eq_iff (g : J) (i j : Fin 8835156) :
    lyAct g i = j ↔ g • ptEquiv i = ptEquiv j :=
  smul_eq_iff g i j

theorem lyAct_zero (g : J) :
    lyAct g 0 = 0 ↔ g • CFSG.Sporadic.Ly.Omega.opE = CFSG.Sporadic.Ly.Omega.opE := by
  rw [lyAct_eq_iff, ptEquiv_zero]
  exact Subtype.ext_iff

end CFSG.Sporadic.LySchreier
