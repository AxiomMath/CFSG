module

public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.B.TwoA.Census.CosetEnumGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def rhoGriess (q : Q) : MGriess :=
  ⟨rhoEquiv q, Gmat_le_AutO (Hmat_le_Gmat (rhoEquiv_mem_Gvis q))⟩

@[simp] theorem coe_rhoGriess (q : Q) : ((rhoGriess q : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) =
    rhoEquiv q := rfl

theorem rhoGriess_mul (q q' : Q) : rhoGriess (q * q') = rhoGriess q' * rhoGriess q :=
  Subtype.ext (rhoEquiv_mul q q')

theorem rhoGriess_one : rhoGriess 1 = 1 := Subtype.ext Short.rhoEquiv_one

theorem rhoGriess_inv (q : Q) : rhoGriess q⁻¹ = (rhoGriess q)⁻¹ :=
  Subtype.ext (Short.rhoEquiv_inv q)

theorem rhoGriess_injective : Function.Injective rhoGriess := fun _ _ h =>
  rhoEquiv_injective (congrArg Subtype.val h)

theorem rhoGriess_zQ : rhoGriess zQ = xGriess := Subtype.ext rfl

theorem rhoGriess_rStar : rhoGriess rStar = tGriess := Subtype.ext rfl

theorem rhoGriess_rTwo : rhoGriess rTwo = uGriess := Subtype.ext rfl

@[expose] noncomputable def RQ : Subgroup Q :=
  Subgroup.centralizer {rStar} ⊓ Subgroup.centralizer {rTwo}

@[expose] noncomputable def RE : Subgroup MGriess :=
  (RQ.map CFSG.Monster.B.Short.rhoHom).comap AutO.subtype

theorem mem_RQ_iff {q : Q} : q ∈ RQ ↔ q * rStar = rStar * q ∧ q * rTwo = rTwo * q :=
  Subgroup.mem_inf.trans (and_congr Subgroup.mem_centralizer_singleton_iff
    Subgroup.mem_centralizer_singleton_iff)

theorem mem_RE_iff {g : MGriess} : g ∈ RE ↔ ∃ q ∈ RQ, g = rhoGriess q := by
  rw [RE, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqg⟩
    refine ⟨q⁻¹, inv_mem hq, Subtype.ext ?_⟩
    have h : rhoEquiv q⁻¹ = (g : SpaceB ≃ₗ[ℚ] SpaceB) := hqg
    exact h.symm
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q⁻¹, inv_mem hq, ?_⟩
    change rhoEquiv q⁻¹⁻¹ = rhoEquiv q
    rw [inv_inv]

theorem rhoGriess_mem_RE {q : Q} (hq : q ∈ RQ) : rhoGriess q ∈ RE :=
  mem_RE_iff.2 ⟨q, hq, rfl⟩

theorem mem_Gvis_of_mem_cent_xGriess {h : MGriess} (hh : h ∈ Subgroup.centralizer {xGriess}) :
    (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
  have : (h : SpaceB ≃ₗ[ℚ] SpaceB) ∈ (Subgroup.centralizer {xGriess}).map AutO.subtype :=
    ⟨h, hh, rfl⟩
  rwa [map_cent_xGriess] at this

@[expose] def RankSpec : Prop :=
  ∀ u : GLV, u ∈ OLvis → u * u = 1 → u ≠ 1 →
    5 ≤ Module.finrank (ZMod 2) (LinearMap.range ((u : Module.End (ZMod 2) L2) - 1))

@[expose] def CheckSpec
    (i : ℕ) : Prop :=
  ∃ (Fb : List L2) (cs : L2 → ZMod 2),
    (∀ f ∈ Fb, modTwoEnd (cosetPair i).1.2 f = f) ∧
    (∀ q' : Q, modTwoEnd (cosetPair i).1.2 (phi0 (coordOf q')) = phi0 (coordOf q') →
      conjQ (cosetPair i) q' = zQ ^ (cs (phi0 (coordOf q'))).val * q') ∧
    (∀ S v : L2, S ∈ shortSet → v ∈ shortSet → S + v ∈ shortSet →
      modTwoEnd (cosetPair i).1.2 v = v → bL S v = 0 →
      (∀ f ∈ Fb, bL f (S + phi0 (coordOf (cosetW i))) = 0) →
      ∃ u : L2, modTwoEnd (cosetPair i).1.2 u + u = v ∧
        bL (S + phi0 (coordOf (cosetW i))) u ≠ cs v)

@[expose] def NoConfig
    (i : ℕ) : Prop :=
  ∀ q q' : Q,
    IsShortCoord (coordOf (q * cosetW i * conjQ (cosetPair i) q)) →
    IsShortCoord (coordOf q') →
    IsShortCoord (coordOf (q' * (q * cosetW i * conjQ (cosetPair i) q))) →
    q' * (q * cosetW i * conjQ (cosetPair i) q) = (q * cosetW i * conjQ (cosetPair i) q) * q' →
    conjQ (cosetPair i) (q⁻¹ * q' * q) = q' → False

end CFSG.Monster.Existence
