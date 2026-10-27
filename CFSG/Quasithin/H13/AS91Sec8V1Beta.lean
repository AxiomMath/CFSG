module

public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import CFSG.Quasithin.H13.AS91Sec8V1Cocycle

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Quasithin.H.Mathieu
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)
variable (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)

@[expose] noncomputable def betaCocycle (m : ↥c.G1) : W11 :=
  M24G.dBeta CFSG.Monster.Code.AutPerm ⟨r.φ m, r.φ_mem m⟩

@[expose] noncomputable def conjE (k : ↥c.G1) (e : ↥c.E) : ↥c.E :=
  ⟨(k : G)⁻¹ * (e : G) * (k : G), by
    have h := c.conj_mem_E k⁻¹ e.2
    simpa [Subgroup.coe_inv] using h⟩

@[expose] noncomputable def betaLift (m : ↥c.G1) : ↥c.E :=
  r.todd.symm (betaCocycle c r m)

theorem betaCocycle_mul (m k : ↥c.G1) :
    betaCocycle c r (m * k) =
      (rho11 CFSG.Monster.Code.AutPerm le_rfl ⟨r.φ k, r.φ_mem k⟩)⁻¹ (betaCocycle c r m) *
        betaCocycle c r k := by
  have h := M24G.isRightCocycle_dBeta (Γ := CFSG.Monster.Code.AutPerm) (hΓ := le_rfl)
    ⟨r.φ m, r.φ_mem m⟩ ⟨r.φ k, r.φ_mem k⟩
  simpa only [betaCocycle, M24G.dBeta, Subgroup.coe_mul, map_mul] using h

theorem todd_conjE (k : ↥c.G1) (e : ↥c.E) :
    r.todd (c.conjE k e) =
      (rho11 CFSG.Monster.Code.AutPerm le_rfl ⟨r.φ k, r.φ_mem k⟩)⁻¹ (r.todd e) := by
  have h := r.todd_equiv k⁻¹ e
  have harg : (⟨((k⁻¹ : ↥c.G1) : G) * (e : G) * (((k⁻¹ : ↥c.G1)) : G)⁻¹,
      c.conj_mem_E k⁻¹ e.2⟩ : ↥c.E) = c.conjE k e := by
    apply Subtype.ext
    simp [conjE, Subgroup.coe_inv]
  rw [harg] at h
  rw [h]
  have hphi : (⟨r.φ (k⁻¹), r.φ_mem (k⁻¹)⟩ : ↥CFSG.Monster.Code.AutPerm) =
      (⟨r.φ k, r.φ_mem k⟩ : ↥CFSG.Monster.Code.AutPerm)⁻¹ := by
    apply Subtype.ext
    simp [Subgroup.coe_inv]
  rw [hphi, map_inv]

theorem betaLift_mul (m k : ↥c.G1) :
    betaLift c r (m * k) = c.conjE k (betaLift c r m) * betaLift c r k := by
  apply r.todd.injective
  rw [betaLift, MulEquiv.apply_symm_apply, map_mul, todd_conjE,
    betaLift, MulEquiv.apply_symm_apply, betaLift, MulEquiv.apply_symm_apply]
  exact betaCocycle_mul c r m k

@[expose] noncomputable def betaFun (m : ↥c.G1) : ↥c.G1 :=
  ⟨(m : G) * (betaLift c r m : G), c.G1.mul_mem m.2 (c.E_le_G1 (betaLift c r m).2)⟩

theorem betaLift_one : betaLift c r 1 = 1 := by
  have hφ : (⟨r.φ (1 : ↥c.G1), r.φ_mem 1⟩ : ↥CFSG.Monster.Code.AutPerm) = 1 := by
    apply Subtype.ext
    exact map_one r.φ
  rw [betaLift, betaCocycle, hφ,
    (M24G.isRightCocycle_dBeta (Γ := CFSG.Monster.Code.AutPerm) (hΓ := le_rfl)).map_one]
  exact map_one r.todd.symm

theorem betaFun_mul (m k : ↥c.G1) : betaFun c r (m * k) = betaFun c r m * betaFun c r k := by
  apply Subtype.ext
  have h := congrArg (fun e : ↥c.E => (e : G)) (betaLift_mul c r m k)
  rw [Subgroup.coe_mul, conjE, Subgroup.coe_mk] at h
  show (m : G) * (k : G) * (betaLift c r (m * k) : G) =
    ((m : G) * (betaLift c r m : G)) * ((k : G) * (betaLift c r k : G))
  rw [h]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem betaFun_one : betaFun c r 1 = 1 := by
  apply Subtype.ext
  show (1 : G) * (betaLift c r 1 : G) = (1 : G)
  rw [betaLift_one]
  exact one_mul 1

@[expose] noncomputable def betaHom : ↥c.G1 →* ↥c.G1 where
  toFun := betaFun c r
  map_one' := betaFun_one c r
  map_mul' := betaFun_mul c r

theorem betaFun_inv (m : ↥c.G1) : betaFun c r m⁻¹ = (betaFun c r m)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← betaFun_mul, inv_mul_cancel, betaFun_one]

theorem betaFun_eq_one {m : ↥c.G1} (h : betaFun c r m = 1) : m = 1 := by
  have hval : (m : G) * (betaLift c r m : G) = 1 := by
    have := congrArg (fun x : ↥c.G1 => (x : G)) h
    simpa [betaFun] using this
  have hmE : (m : G) ∈ c.E := by
    have h1 : (m : G) = (betaLift c r m : G)⁻¹ := eq_inv_of_mul_eq_one_left hval
    rw [h1]
    exact c.E.inv_mem (betaLift c r m).2
  have hφ : r.φ m = 1 := by
    rw [← MonoidHom.mem_ker, r.ker_eq, Subgroup.mem_subgroupOf]
    exact hmE
  have hsub : (⟨r.φ m, r.φ_mem m⟩ : ↥CFSG.Monster.Code.AutPerm) = 1 := by
    apply Subtype.ext
    simpa using hφ
  have hdelta : betaCocycle c r m = 1 := by
    rw [betaCocycle, hsub]
    exact (M24G.isRightCocycle_dBeta (Γ := CFSG.Monster.Code.AutPerm) (hΓ := le_rfl)).map_one
  have hlift : (betaLift c r m : G) = 1 := by
    have h1 : betaLift c r m = 1 := by simp [betaLift, hdelta]
    simpa using congrArg (fun e : ↥c.E => (e : G)) h1
  apply Subtype.ext
  simpa [hlift] using hval

theorem betaFun_injective : Function.Injective (betaFun c r) := by
  intro m k h
  have h1 : betaFun c r (m * k⁻¹) = 1 := by
    rw [betaFun_mul, h, betaFun_inv, mul_inv_cancel]
  have h2 : m * k⁻¹ = 1 := betaFun_eq_one c r h1
  have := congrArg (fun x => x * k) h2
  simpa [mul_assoc] using this

theorem betaFun_surjective : Function.Surjective (betaFun c r) :=
  Finite.injective_iff_surjective.mp (betaFun_injective c r)

@[expose] noncomputable def betaEquiv : ↥c.G1 ≃* ↥c.G1 :=
  MulEquiv.ofBijective (betaHom c r) ⟨betaFun_injective c r, betaFun_surjective c r⟩

theorem coe_betaEquiv (m : ↥c.G1) : ((betaEquiv c r m : ↥c.G1) : G) = (betaFun c r m : G) := rfl

theorem betaFun_mem_G3 (m : ↥c.G1) :
    (m : G) ∈ c.G3 ↔ (betaFun c r m : G) ∈ c.G3 := by
  have he : (betaLift c r m : G) ∈ c.G3 := c.E_le_G3 (betaLift c r m).2
  have h : (m : G) * (betaLift c r m : G) ∈ c.G3 ↔ (m : G) ∈ c.G3 :=
    c.G3.mul_mem_cancel_right he
  simpa [betaFun] using h.symm

theorem betaCocycle_inclusion (h : ↥(c.G3 ⊓ c.G1)) :
    betaCocycle c r (Subgroup.inclusion inf_le_right h) =
      M24G.dBeta M24G.sextStab (c.phiS r hU h) := by
  simp only [betaCocycle, M24G.dBeta, Subgroup.coe_mk, c.coe_phiS r hU h]

theorem hasBetaTwist : c.HasBetaTwist r hU := by
  refine ⟨betaEquiv c r, betaFun_mem_G3 c r, ?_⟩
  intro h
  have hlift : betaLift c r (Subgroup.inclusion inf_le_right h) =
      r.todd.symm (M24G.dBeta M24G.sextStab (c.phiS r hU h)) := by
    rw [betaLift, betaCocycle_inclusion c r hU h]
  rw [coe_betaEquiv]
  change (Subgroup.inclusion inf_le_right h : G) *
    (betaLift c r (Subgroup.inclusion inf_le_right h) : G) = _
  rw [hlift]
  rfl

end Loc49

end CFSG.Quasithin.H13.AS91

