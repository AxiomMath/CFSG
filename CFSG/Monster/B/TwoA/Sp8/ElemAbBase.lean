
module

public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Base.PsiV
public import CFSG.Monster.B.TwoA.Census.PermClasses

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

theorem tauhat_conj_xhat' : tauhat * xhat * tauhat⁻¹ = xhat * yhat := by
  rw [tauhat_conj_xhat, ← xbar_mul_zbar, map_mul]
  rfl

theorem tauhat_conj_yhat : tauhat * yhat * tauhat⁻¹ = xhat := by
  rw [tauhat, yhat, ← map_inv, ← map_mul, ← map_mul, taubar_conj_zbar]
  rfl

theorem tauhat_conj_dhat (i j : Fin 24) : tauhat * dhat i j * tauhat⁻¹ = dhat i j := by
  rw [tauhat_mul_dhat, mul_inv_cancel_right]

def triRows : List ℕ := [3, 1, 4, 8, 16, 32, 128, 192]

theorem bvec_triRows : ∀ k : Fin 8, bvec 8 (triRows.getD k 0) =
    ![Pi.single 0 1 + Pi.single 1 1, Pi.single 0 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
      Pi.single 5 1, Pi.single 7 1, Pi.single 6 1 + Pi.single 7 1] k := by
  decide

theorem tauhat_pow_three : tauhat ^ 3 = 1 := by
  rw [tauhat, ← map_pow, taubar_pow_three, map_one]

end CFSG.Monster.B.TwoA.Sp8
