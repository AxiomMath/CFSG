module

public import CFSG.Monster.Existence.TwoPointTwoB
public import CFSG.Monster.B.TwoA.Triality.PermLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

@[expose] noncomputable def rTwo : Q := DQ (deltaPair 0 2)

@[expose] noncomputable def rOneTwo : Q := DQ (deltaPair 1 2)

theorem deltaPair_add : deltaPair 0 1 + deltaPair 0 2 = deltaPair 1 2 := by
  rw [deltaPair, deltaPair, deltaPair, ← Submodule.Quotient.mk_add]
  congr 1
  have h : (Pi.single 0 1 : Fin 24 → ZMod 2) + Pi.single 0 1 = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  calc (Pi.single 0 1 + Pi.single 1 1 + (Pi.single 0 1 + Pi.single 2 1) : Fin 24 → ZMod 2)
      = (Pi.single 0 1 + Pi.single 0 1) + (Pi.single 1 1 + Pi.single 2 1) := by abel
    _ = Pi.single 1 1 + Pi.single 2 1 := by rw [h, zero_add]

theorem rStar_mul_rTwo : rStar * rTwo = rOneTwo := by
  rw [rStar, rTwo, rOneTwo, ← TwoA.DQ_add, deltaPair_add]

theorem rTwo_mul_rStar : rTwo * rStar = rOneTwo := by
  rw [rTwo, rStar, TwoA.DQ_comm]
  exact rStar_mul_rTwo

theorem isShortCoord_rTwo : IsShortCoord (coordOf rTwo) :=
  isShortCoord_rMinus (by decide : (0 : Fin 24) < 2)

theorem isShortCoord_rOneTwo : IsShortCoord (coordOf rOneTwo) :=
  isShortCoord_rMinus (by decide : (1 : Fin 24) < 2)

theorem isShortCoord_mul_zQ {r : Q} (hr : IsShortCoord (coordOf r)) :
    IsShortCoord (coordOf (r * zQ)) := by
  have hc : r * zQ = zQ * r := Subgroup.mem_center_iff.1 Short.zQ_mem_center r
  rw [hc, coordOf_zQ_mul]
  exact hr

@[expose] noncomputable def uStar : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv rTwo

@[expose] noncomputable def uGriess : MGriess :=
  ⟨uStar, Gmat_le_AutO (Hmat_le_Gmat (rhoEquiv_mem_Gvis rTwo))⟩

theorem rhoEquiv_mul_self_DQ (δ : Cocode) : rhoEquiv (DQ δ) * rhoEquiv (DQ δ) = 1 := by
  rw [← rhoEquiv_mul, Generated.OddCocode.DQ_mul_self, Short.rhoEquiv_one]

theorem tGriess_mul_self : tGriess * tGriess = 1 :=
  Subtype.ext (rhoEquiv_mul_self_DQ (deltaPair 0 1))

theorem uGriess_mul_self : uGriess * uGriess = 1 :=
  Subtype.ext (rhoEquiv_mul_self_DQ (deltaPair 0 2))

theorem tStar_mul_uStar : tStar * uStar = rhoEquiv rOneTwo := by
  rw [tStar, uStar, ← rhoEquiv_mul, rTwo_mul_rStar]

theorem uStar_mul_tStar : uStar * tStar = rhoEquiv rOneTwo := by
  rw [tStar, uStar, ← rhoEquiv_mul, rStar_mul_rTwo]

theorem tGriess_mul_uGriess : tGriess * uGriess = uGriess * tGriess :=
  Subtype.ext ((tStar_mul_uStar).trans uStar_mul_tStar.symm)

@[expose] noncomputable def FE : Subgroup MGriess :=
  kleinSubgroup tGriess uGriess tGriess_mul_self uGriess_mul_self tGriess_mul_uGriess

theorem mem_FE {g : MGriess} :
    g ∈ FE ↔ g = 1 ∨ g = tGriess ∨ g = uGriess ∨ g = tGriess * uGriess := Iff.rfl

theorem trace_rhoEquiv_short
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    LinearMap.trace ℚ SpaceB (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) = 4372 :=
  trace_rho_short hr

theorem trace_of_mem_FE {g : MGriess} (hg : g ∈ FE) (h1 : g ≠ 1) :
    LinearMap.trace ℚ SpaceB ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 4372 := by
  rcases mem_FE.1 hg with rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · exact trace_rhoEquiv_short isShortCoord_rStar
  · exact trace_rhoEquiv_short isShortCoord_rTwo
  · change LinearMap.trace ℚ SpaceB ((tStar * uStar : SpaceB ≃ₗ[ℚ] SpaceB) :
      SpaceB →ₗ[ℚ] SpaceB) = 4372
    rw [tStar_mul_uStar]
    exact trace_rhoEquiv_short isShortCoord_rOneTwo

theorem trace_x_mul_of_mem_FE
    {g : MGriess} (hg : g ∈ FE) (h1 : g ≠ 1) :
    LinearMap.trace ℚ SpaceB (((xGriess * g : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) :
      SpaceB →ₗ[ℚ] SpaceB) = 4372 := by
  have key : ∀ r : Q, IsShortCoord (coordOf r) →
      LinearMap.trace ℚ SpaceB ((xmat * rhoEquiv r : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) = 4372 := fun r hr => by
    rw [xmat, ← rhoEquiv_mul]
    exact trace_rhoEquiv_short (isShortCoord_mul_zQ hr)
  rcases mem_FE.1 hg with rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · exact key rStar isShortCoord_rStar
  · exact key rTwo isShortCoord_rTwo
  · change LinearMap.trace ℚ SpaceB ((xmat * (tStar * uStar) : SpaceB ≃ₗ[ℚ] SpaceB) :
      SpaceB →ₗ[ℚ] SpaceB) = 4372
    rw [tStar_mul_uStar]
    exact key rOneTwo isShortCoord_rOneTwo

theorem trace_xGriess :
    LinearMap.trace ℚ SpaceB (((xGriess : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) :
      SpaceB →ₗ[ℚ] SpaceB) = 276 := trace_xmat

theorem trace_eq_of_isConj_MGriess {a b : MGriess} (h : IsConj a b) :
    LinearMap.trace ℚ SpaceB (((a : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      LinearMap.trace ℚ SpaceB (((b : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (trace_conj (c : SpaceB ≃ₗ[ℚ] SpaceB) a).symm

theorem xGriess_not_mem_FE : xGriess ∉ FE := by
  intro h
  have hx1 : xGriess ≠ 1 := by
    intro h1
    have := orderOf_xGriess
    rw [h1, orderOf_one] at this
    norm_num at this
  have := trace_of_mem_FE h hx1
  rw [trace_xGriess] at this
  norm_num at this

theorem not_isConj_x_mul
    {f : MGriess} (hf : f ∈ FE) (hc : IsConj xGriess (xGriess * f)) :
    f = 1 := by
  by_contra h1
  have := trace_eq_of_isConj_MGriess hc
  rw [trace_xGriess, trace_x_mul_of_mem_FE hf h1] at this
  norm_num at this

theorem xGriess_mem_centralizer_FE : xGriess ∈ Subgroup.centralizer (FE : Set MGriess) := by
  rw [Subgroup.mem_centralizer_iff]
  have hcomm : ∀ r : Q, rhoEquiv r * xmat = xmat * rhoEquiv r := fun r => by
    rw [xmat, ← rhoEquiv_mul, ← rhoEquiv_mul]
    exact congrArg rhoEquiv (Subgroup.mem_center_iff.1 Short.zQ_mem_center r).symm
  intro g hg
  rcases mem_FE.1 hg with rfl | rfl | rfl | rfl
  · simp
  · exact Subtype.ext (hcomm rStar)
  · exact Subtype.ext (hcomm rTwo)
  · apply Subtype.ext
    change tStar * uStar * xmat = xmat * (tStar * uStar)
    rw [tStar_mul_uStar]
    exact hcomm rOneTwo

theorem FE_le_GmatGriess : FE ≤ GmatGriess := by
  intro g hg
  have hmem : ∀ r : Q, (rhoEquiv r : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := fun r =>
    Hmat_le_Gmat (rhoEquiv_mem_Gvis r)
  rcases mem_FE.1 hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hmem rStar
  · exact hmem rTwo
  · change tStar * uStar ∈ Gmat
    rw [tStar_mul_uStar]
    exact hmem rOneTwo

theorem FE_comm : ∀ a ∈ FE, ∀ b ∈ FE, a * b = b * a := by
  intro a ha b hb
  have h1 := mul_self_of_mem_kleinSubgroup ha
  have h2 := mul_self_of_mem_kleinSubgroup hb
  have h3 := mul_self_of_mem_kleinSubgroup (FE.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h1]

end CFSG.Monster.Existence
