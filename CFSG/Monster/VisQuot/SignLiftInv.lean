module

public import CFSG.Monster.B.TwoA.Census.CosetEnumGroup
public import CFSG.Monster.Schur.GmatStructurePhi

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Model

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem add_self_zmod2 (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem A_smul_right (d e f : Fin 24 → ZMod 2) (c : ZMod 2) :
    A d e (c • f) = c * A d e f := by
  simp only [A_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem A_ΩC_right (d e : C) :
    A (d : Fin 24 → ZMod 2) e (CFSG.Monster.Spin.ΩC : Fin 24 → ZMod 2) = 0 := by
  rw [A_eq_dotProduct]
  have h : (CFSG.Monster.Spin.ΩC : Fin 24 → ZMod 2) = fun _ => 1 := rfl
  rw [h]
  trans (d : Fin 24 → ZMod 2) ⬝ᵥ e
  · rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.mul_apply]
  · exact dotProduct_eq_zero d.2 e.2

theorem A_pi0_pi0 (c a b : C) :
    A (c : Fin 24 → ZMod 2) ((π₀ a : C₀) : Fin 24 → ZMod 2) (b : Fin 24 → ZMod 2) =
      A (c : Fin 24 → ZMod 2) ((π₀ a : C₀) : Fin 24 → ZMod 2)
        ((π₀ b : C₀) : Fin 24 → ZMod 2) := by
  have hb : ((π₀ b : C) : Fin 24 → ZMod 2) +
      μ₀ b • (CFSG.Monster.Spin.ΩC : Fin 24 → ZMod 2) = (b : Fin 24 → ZMod 2) := by
    rw [← Submodule.coe_smul, ← Submodule.coe_add, π₀_add_μ₀]
  rw [← hb, A_add_right, A_smul_right, A_ΩC_right, mul_zero, add_zero]

theorem θ_shift_add (c : C₀) (a b : C) :
    θ (shift a c) b = θ c b + θ (π₀ a) b + A c (π₀ a) b := by
  rw [coe_shift_eq_add_π₀, θ_add_left]

theorem Ymat_mul_self {a : C} (h : θ (π₀ a : C) a = 0) : Ymat ⟨a, 0⟩ * Ymat ⟨a, 0⟩ = 1 := by
  simp only [Ymat]
  rw [spm_mul_spm]
  refine spm_eq_one (fun i => yPerm_involutive a i) (fun i => ?_)
  rcases i with ⟨η, c⟩
  rcases zmod2_cases η with rfl | rfl
  · simp only [yPerm_zero, ySign_zero, zero_add]
    rw [θ_shift_add c a a, A_pi0_pi0 c a a, A_self_right (c : C).2 ((π₀ a : C)).2, add_zero, h,
      add_zero]
    exact add_self_zmod2 _
  · simp only [yPerm_one, ySign_one]
    exact add_self_zmod2 _

theorem Ymat_mul_comm {a b : C} (h : θ (π₀ a : C) b = θ (π₀ b : C) a) :
    Ymat ⟨a, 0⟩ * Ymat ⟨b, 0⟩ = Ymat ⟨b, 0⟩ * Ymat ⟨a, 0⟩ := by
  simp only [Ymat]
  rw [spm_mul_spm, spm_mul_spm]
  refine spm_congr ?_ ?_
  · intro i
    rcases i with ⟨η, c⟩
    rcases zmod2_cases η with rfl | rfl
    · simp only [Function.comp_apply, yPerm_zero, ← shift_add a b, ← shift_add b a,
        add_comm b a]
    · simp only [Function.comp_apply, yPerm_one]
  · intro i
    rcases i with ⟨η, c⟩
    rcases zmod2_cases η with rfl | rfl
    · simp only [yPerm_zero, ySign_zero, zero_add]
      rw [θ_shift_add c a b, θ_shift_add c b a, A_pi0_pi0 c a b, A_pi0_pi0 c b a,
        A_comm₂₃ c (π₀ b) (π₀ a), h]
      abel
    · simp only [yPerm_one, ySign_one]
      exact add_comm _ _

@[expose] def signPair (a : ℕ) : Pvis :=
  ⟨(YU ⟨toC a, 0⟩, gO (toC a)), YU_gO_mem_Pvis ⟨toC a, 0⟩⟩

@[expose] def hS (a : ℕ) : Gvis := CFSG.Monster.B.TwoA.Census.thetaVis (signPair a)

theorem signPair_mul_self {a : ℕ} (h : thetaBit (pi0N a) a = false) :
    signPair a * signPair a = 1 := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show (YU ⟨toC a, 0⟩ : GL SpinIdx ℚ) * YU ⟨toC a, 0⟩ = 1
    refine Units.ext ?_
    simpa only [Units.val_mul, Units.val_one, coe_YU] using
      Ymat_mul_self (a := toC a) (by rw [coe_π₀_toC, θ_toC, h, boolZ_false])
  · show gO (toC a) * gO (toC a) = 1
    exact gO_mul_self _

theorem signPair_mul_comm {a b : ℕ} (h : thetaBit (pi0N a) b = thetaBit (pi0N b) a) :
    signPair a * signPair b = signPair b * signPair a := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show (YU ⟨toC a, 0⟩ : GL SpinIdx ℚ) * YU ⟨toC b, 0⟩ =
      YU ⟨toC b, 0⟩ * YU ⟨toC a, 0⟩
    refine Units.ext ?_
    simpa only [Units.val_mul, coe_YU] using
      Ymat_mul_comm (a := toC a) (b := toC b)
        (by rw [coe_π₀_toC, coe_π₀_toC, θ_toC, θ_toC, h])
  · show gO (toC a) * gO (toC b) = gO (toC b) * gO (toC a)
    calc gO (toC a) * gO (toC b) = gO (toC a + toC b) := (gO_add _ _).symm
      _ = gO (toC b + toC a) := by rw [add_comm]
      _ = gO (toC b) * gO (toC a) := gO_add _ _

theorem hS_mul_self {a : ℕ} (h : thetaBit (pi0N a) a = false) : hS a * hS a = 1 := by
  change CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) *
    CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) = 1
  rw [← thetaVis_mul (signPair a) (signPair a), signPair_mul_self h]
  exact Subtype.ext thetaEquiv_one

theorem hS_mul_comm {a b : ℕ} (h : thetaBit (pi0N a) b = thetaBit (pi0N b) a) :
    hS a * hS b = hS b * hS a := by
  change CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) *
    CFSG.Monster.B.TwoA.Census.thetaVis (signPair b) =
      CFSG.Monster.B.TwoA.Census.thetaVis (signPair b) *
        CFSG.Monster.B.TwoA.Census.thetaVis (signPair a)
  calc CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) *
        CFSG.Monster.B.TwoA.Census.thetaVis (signPair b)
      = CFSG.Monster.B.TwoA.Census.thetaVis (signPair b * signPair a) :=
        (thetaVis_mul (signPair b) (signPair a)).symm
    _ = CFSG.Monster.B.TwoA.Census.thetaVis (signPair a * signPair b) := by
        rw [signPair_mul_comm h]
    _ = CFSG.Monster.B.TwoA.Census.thetaVis (signPair b) *
        CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) :=
        thetaVis_mul (signPair a) (signPair b)

theorem hS_mul_rhoGvis {a : ℕ} {y : Pauli} (h : conjYN a y = y) :
    hS a * CFSG.Monster.B.TwoA.Census.rhoGvis (pauliQ y) =
      CFSG.Monster.B.TwoA.Census.rhoGvis (pauliQ y) * hS a := by
  have hc : conjQ (signPair a) (pauliQ y) = pauliQ y := by
    change conjQ ⟨(YU ⟨toC a, 0⟩, gO (toC a)), YU_gO_mem_Pvis ⟨toC a, 0⟩⟩ (pauliQ y) = _
    rw [conjQ_sign_toQ, h]
  calc hS a * CFSG.Monster.B.TwoA.Census.rhoGvis (pauliQ y)
      = CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) *
        CFSG.Monster.B.TwoA.Census.thetaVis (rhoPair (pauliQ y)) := rfl
    _ = CFSG.Monster.B.TwoA.Census.thetaVis (rhoPair (pauliQ y) * signPair a) :=
        (thetaVis_mul _ _).symm
    _ = CFSG.Monster.B.TwoA.Census.thetaVis
          (signPair a * rhoPair (conjQ (signPair a) (pauliQ y))) := by
        rw [rhoPair_mul_comm]
    _ = CFSG.Monster.B.TwoA.Census.thetaVis (signPair a * rhoPair (pauliQ y)) := by rw [hc]
    _ = CFSG.Monster.B.TwoA.Census.thetaVis (rhoPair (pauliQ y)) *
        CFSG.Monster.B.TwoA.Census.thetaVis (signPair a) := thetaVis_mul _ _
    _ = CFSG.Monster.B.TwoA.Census.rhoGvis (pauliQ y) * hS a := rfl

theorem PhiV_hS (a : ℕ) : CFSG.Monster.Schur.PhiV (hS a) =
    monoHom (SemidirectProduct.inl (Multiplicative.ofAdd (Submodule.Quotient.mk (toC a)))) := by
  have h1 : CFSG.Monster.Schur.PhiV (hS a) = CFSG.Monster.ScalarKernel.modTwoUnit (gO (toC a)) := by
    show CFSG.Monster.Schur.PhiV
      ⟨thetaEquiv (signPair a), thetaEquiv_mem_Gvis (signPair a)⟩ = _
    rw [CFSG.Monster.Schur.PhiV_thetaEquiv]
    rfl
  have h2 : monoHom
      (SemidirectProduct.inl (Multiplicative.ofAdd (Submodule.Quotient.mk (toC a)))) =
      CFSG.Monster.ScalarKernel.modTwoUnit (gO (toC a)) := by
    rw [show SemidirectProduct.inl
        (Multiplicative.ofAdd (Submodule.Quotient.mk (toC a))) =
        (⟨Multiplicative.ofAdd (Submodule.Quotient.mk (toC a)), (1 : AutPerm)⟩ : MonoSD)
        from rfl,
      monoHom_mk, PO_one, one_mul]
  rw [h1, h2]

theorem PhiV_rhoGvis (r : Q) :
    CFSG.Monster.Schur.PhiV (CFSG.Monster.B.TwoA.Census.rhoGvis r) = 1 := by
  show CFSG.Monster.Schur.PhiV
    ⟨thetaEquiv (rhoPair r), thetaEquiv_mem_Gvis (rhoPair r)⟩ = 1
  rw [CFSG.Monster.Schur.PhiV_thetaEquiv]
  exact modTwoUnit_one

end CFSG.Monster.VisQuot
