
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.MatrixWBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

theorem card_GL_of_finrank {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] {d : ℕ} (hd : Module.finrank (ZMod 2) M = d) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) M) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  let e : M ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearEquiv.ofFinrankEq M (Fin d → ZMod 2) (by simp [hd])
  rw [Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := ZMod 2)).toEquiv,
    Matrix.card_GL_field]
  simp [ZMod.card]

theorem not_dvd_card_GL {d : ℕ} (h1 : 1 ≤ d) (h11 : d ≤ 11) :
    ¬ 42305421312000 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
  interval_cases d <;> simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero,
    Fin.val_succ] <;> norm_num

section Invariant

variable (U : Submodule (ZMod 2) (Wv v0))
  (hU : ∀ (k : Kstab v0) (w : Wv v0), w ∈ U → wAct v0 k w ∈ U)

include hU

def restrictU (k : Kstab v0) : Module.End (ZMod 2) U :=
  (wAct v0 k).restrict fun w hw => hU k w hw

theorem restrictU_apply (k : Kstab v0) (w : U) : (restrictU U hU k w : Wv v0) = wAct v0 k w := rfl

def rhoU : Kstab v0 →* LinearMap.GeneralLinearGroup (ZMod 2) U :=
  MonoidHom.mk' (fun k => ⟨restrictU U hU k⁻¹, restrictU U hU k,
      LinearMap.ext fun w => Subtype.ext (wAct_inv_apply k w),
      LinearMap.ext fun w => Subtype.ext (by
        change wAct v0 k (wAct v0 k⁻¹ w) = w
        exact wAct_apply_inv k w)⟩)
    fun k k' => Units.ext (LinearMap.ext fun w => Subtype.ext (by
      change wAct v0 (k * k')⁻¹ w = wAct v0 k⁻¹ (wAct v0 k'⁻¹ w)
      rw [mul_inv_rev, wAct_mul, Module.End.mul_apply]))

def restrictQ (k : Kstab v0) : Module.End (ZMod 2) (Wv v0 ⧸ U) :=
  U.mapQ U (wAct v0 k) fun w hw => hU k w hw

theorem restrictQ_mk (k : Kstab v0) (w : Wv v0) :
    restrictQ U hU k (Submodule.Quotient.mk w) = Submodule.Quotient.mk (wAct v0 k w) := rfl

def rhoQ : Kstab v0 →* LinearMap.GeneralLinearGroup (ZMod 2) (Wv v0 ⧸ U) :=
  MonoidHom.mk' (fun k => ⟨restrictQ U hU k⁻¹, restrictQ U hU k,
      LinearMap.ext fun w => by
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          change Submodule.Quotient.mk (wAct v0 k⁻¹ (wAct v0 k w)) = Submodule.Quotient.mk w
          rw [wAct_inv_apply],
      LinearMap.ext fun w => by
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          change Submodule.Quotient.mk (wAct v0 k (wAct v0 k⁻¹ w)) = Submodule.Quotient.mk w
          rw [wAct_apply_inv]⟩)
    fun k k' => Units.ext (LinearMap.ext fun w => by
      induction w using Submodule.Quotient.induction_on with
      | H w =>
        change Submodule.Quotient.mk (wAct v0 (k * k')⁻¹ w) =
          Submodule.Quotient.mk (wAct v0 k⁻¹ (wAct v0 k'⁻¹ w))
        rw [mul_inv_rev, wAct_mul, Module.End.mul_apply])

end Invariant

end CFSG.Monster.B.Co2
