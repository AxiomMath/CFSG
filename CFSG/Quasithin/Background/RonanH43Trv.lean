module

public import CFSG.Quasithin.Background.HSL3Fix
public import CFSG.Quasithin.Background.RonanH43Base

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

theorem inv_pv (a : PV) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact pairMod_sq_eq_one a)

theorem mk_mul (v w v' w' : Fin 3 → ZMod 2) : mk v w * mk v' w' = mk (v + v') (w + w') := rfl

theorem mk_zero : mk 0 0 = 1 := rfl

theorem mk_inv (v w : Fin 3 → ZMod 2) : (mk v w)⁻¹ = mk v w := inv_pv _

theorem mk_inj {v w v' w' : Fin 3 → ZMod 2} : mk v w = mk v' w' ↔ v = v' ∧ w = w' := by
  simp [Prod.ext_iff]

abbrev e0 : Fin 3 → ZMod 2 := Pi.single 0 1

theorem dot_e0 {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) : φ ⬝ᵥ e0 = 0 := by
  rw [dotProduct_single, h, zero_mul]

abbrev b1R (i : Fin 3) : PV := (Multiplicative.ofAdd (Pi.single i 1), 1)

abbrev b2R (i : Fin 3) : PV := (1, Multiplicative.ofAdd (Pi.single i 1))

@[expose] noncomputable def trv0 (φ : Fin 3 → ZMod 2) (h : φ 0 = 0) : MulAut PV :=
  pairHom (trvGL (dot_e0 h))

theorem trv0_apply {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) (v w : Fin 3 → ZMod 2) :
    trv0 φ h (mk v w) = mk (v + (φ ⬝ᵥ v) • e0) (w + w 0 • φ) := by
  unfold trv0
  rw [pairHom_trvGL_apply]
  simp only [toAdd_ofAdd, single_dotProduct, one_mul]

theorem trv0_injective {φ ψ : Fin 3 → ZMod 2} (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (h : trv0 φ hφ = trv0 ψ hψ) : φ = ψ := by
  have h1 := congrArg (fun y : MulAut PV => Multiplicative.toAdd (y (mk 0 e0)).2) h
  simpa only [trv0_apply, toAdd_ofAdd, Pi.single_eq_same, one_smul, add_right_inj] using h1

end CFSG.Quasithin.RonanH43
