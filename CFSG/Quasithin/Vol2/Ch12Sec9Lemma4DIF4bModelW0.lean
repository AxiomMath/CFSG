module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelS

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def e0 : VM := mkV (ex 0) 0

@[expose] def f0 : VM := mkV 0 (ex 0)

@[expose] def inU (v : VM) : Prop := v (Sum.inl 0) = 0 ∧ v (Sum.inr 0) = 0

instance : DecidablePred inU := fun v => by unfold inU; infer_instance

@[expose] def Eev (c v : VM) : VM :=
  v + (v (Sum.inr 0)) • c + (bM v c + qM c * v (Sum.inr 0)) • e0

theorem bM_e0_right (v : VM) : bM v e0 = v (Sum.inr 0) := by
  simp [bM, e0, xp, yp, mkV, ex, dotProduct, Fin.sum_univ_three]

theorem qM_e0 : qM e0 = 0 := by
  simp [qM, e0, xp, yp, mkV, dotProduct, Fin.sum_univ_three]

theorem bM_e0_left (v : VM) : bM e0 v = v (Sum.inr 0) := by
  rw [bM_symm, bM_e0_right]

theorem Eev_add_left (c v w : VM) : Eev c (v + w) = Eev c v + Eev c w := by
  unfold Eev
  simp only [Pi.add_apply, bM, qM, xp, yp, mkV, dotProduct, Fin.sum_univ_three]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Eev_smul_right (c : VM) (a : ZMod 2) (v : VM) : Eev c (a • v) = a • Eev c v := by
  unfold Eev
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bM, qM, xp, yp, mkV, dotProduct,
    Fin.sum_univ_three]
  ring

end CFSG.Quasithin.H13.C1294.Model

end
