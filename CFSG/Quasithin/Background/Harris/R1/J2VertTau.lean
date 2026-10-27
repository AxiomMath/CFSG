module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.J2RecCzModel

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM Equiv

@[expose] def tauImg : Fin 4 → QM
  | 0 => (x 2)⁻¹ * (x 1)⁻¹ * (x 3)⁻¹ * (x 4)⁻¹
  | 1 => (x 2)⁻¹ * z⁻¹
  | 2 => z⁻¹ * (x 3)⁻¹
  | 3 => z⁻¹ * (x 4)⁻¹

theorem liftRel_tau : LiftRel z tauImg :=
  ⟨z_sq, by decide +kernel, by decide +kernel, by decide +kernel⟩

@[expose] def tauHom : QM →* QM := liftRel_tau.liftHom

theorem tauHom_x : ∀ j : Fin 4, tauHom (x j.succ) = tauImg j := by decide +kernel

theorem tauHom_tauHom (p : QM) : tauHom (tauHom p) = p := by
  revert p
  decide +kernel

@[expose] def tau : MulAut QM where
  toFun := tauHom
  invFun := tauHom
  left_inv := tauHom_tauHom
  right_inv := tauHom_tauHom
  map_mul' := map_mul tauHom

theorem tau_x (j : Fin 4) : tau (x j.succ) = tauImg j := tauHom_x j

theorem tau_mul_tau : tau * tau = 1 :=
  MulEquiv.ext fun p => tauHom_tauHom p

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_tau

theorem linePerm_tau : linePerm tau = swap 0 1 := by
  refine Equiv.ext fun j => linePerm_eq ?_
  revert j
  decide +kernel

theorem sign_linePerm_tau : Perm.sign (linePerm tau) = -1 := by
  rw [linePerm_tau, Perm.sign_swap (by decide)]

theorem tau_phiA : tau * phiA * tau⁻¹ = phiA⁻¹ := by
  rw [tau_inv]
  refine aut_ext fun j => ?_
  show tauHom (phiAHom (tauHom (x j.succ))) = phiAHom (x j.succ)
  revert j
  decide +kernel

theorem tau_phiB :
    tau * phiB * tau⁻¹ = phiA⁻¹ * phiB⁻¹ * phiA⁻¹ * phiB * phiA * phiB⁻¹ := by
  rw [tau_inv]
  refine aut_ext fun j => ?_
  show tauHom (phiBHom (tauHom (x j.succ))) =
    phiAHom (phiBHom (phiBHom (phiAHom (phiBHom (phiAHom (phiBHom (phiBHom (x j.succ))))))))
  revert j
  decide +kernel

end CFSG.Quasithin.Background.Harris.R1.J2Vert
