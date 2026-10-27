module

public import CFSG.Monster.B.Cbar.EvenCocode
public import CFSG.Monster.B.Short.AxisAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

@[expose] noncomputable def Jstar : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Gvis ⊓ Subgroup.centralizer {tStar}

@[expose] noncomputable def Cgen : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Subgroup.closure (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)))

@[expose] noncomputable def rhoCQ : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  ((Subgroup.centralizer {rStar} : Subgroup Q).map rho).unop

theorem mem_rhoCQ {f : SpaceB ≃ₗ[ℚ] SpaceB} :
    f ∈ rhoCQ ↔ ∃ q ∈ Subgroup.centralizer {rStar}, rhoEquiv q = f := by
  rw [rhoCQ, Subgroup.mem_unop, Subgroup.mem_map]
  simp only [rho_apply, MulOpposite.op_inj]

theorem tStar_mem_Jstar : tStar ∈ Jstar :=
  ⟨tStar_mem_Gvis, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem Jstar_le_Cgen : Jstar ≤ Cgen := fun _ hg =>
  Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)

theorem tauB_mem_Cgen : tauB ∈ Cgen := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tStar_mem_Cgen : tStar ∈ Cgen := Jstar_le_Cgen tStar_mem_Jstar

theorem Cgen_le : Cgen ≤ Gmat ⊓ Subgroup.centralizer {tStar} := closure_le_centralizer_tStar

theorem Cgen_le_Gmat : Cgen ≤ Gmat := fun _ hg => (Cgen_le hg).1

theorem commute_tStar_of_mem_Cgen {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Cgen) :
    g * tStar = tStar * g :=
  Subgroup.mem_centralizer_singleton_iff.1 (Cgen_le hg).2

theorem rho_commute {q r : Q} (h : q * r = r * q) : rhoEquiv q * rhoEquiv r = rhoEquiv r * rhoEquiv q := by
  rw [← rhoEquiv_mul, ← rhoEquiv_mul, h]

theorem rhoCQ_le_Jstar : rhoCQ ≤ Jstar := by
  intro f hf
  obtain ⟨q, hq, rfl⟩ := mem_rhoCQ.1 hf
  refine ⟨rhoEquiv_mem_Gvis q, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h := Subgroup.mem_centralizer_singleton_iff.1 hq
  exact rho_commute h

theorem zQ_mem_centralizer_rStar : zQ ∈ Subgroup.centralizer {rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_center_iff.1 Short.zQ_mem_center rStar).symm

theorem xmat_mem_rhoCQ : xmat ∈ rhoCQ := mem_rhoCQ.2 ⟨zQ, zQ_mem_centralizer_rStar, rfl⟩

theorem xmat_mem_Jstar : xmat ∈ Jstar := rhoCQ_le_Jstar xmat_mem_rhoCQ

theorem xmat_mem_Cgen : xmat ∈ Cgen := Jstar_le_Cgen xmat_mem_Jstar

theorem rStar_mem_centralizer : rStar ∈ Subgroup.centralizer {rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2 rfl

theorem tStar_mem_rhoCQ : tStar ∈ rhoCQ := mem_rhoCQ.2 ⟨rStar, rStar_mem_centralizer, rfl⟩

instance : Finite Cgen :=
  Finite.of_injective (Subgroup.inclusion Cgen_le_Gmat) (Subgroup.inclusion_injective _)

theorem rhoEquiv_one' : rhoEquiv 1 = 1 :=
  (congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one

theorem tStar_ne_one : tStar ≠ 1 := by
  intro h
  have h1 : rStar = 1 := rhoEquiv_injective (h.trans rhoEquiv_one'.symm)
  have hc : rStar ∈ Subgroup.center Q := by rw [h1]; exact Subgroup.one_mem _
  exact Short.not_mem_center_of_isShortCoord isShortCoord_rStar hc

theorem tStar_mul_self : tStar * tStar = 1 := by
  have h : rStar * rStar = 1 := by
    have := sq_eq_one_of_isShort isShortCoord_rStar
    rwa [pow_two] at this
  change rhoEquiv rStar * rhoEquiv rStar = 1
  rw [← rhoEquiv_mul, h, rhoEquiv_one']

theorem orderOf_tStar : orderOf tStar = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact tStar_mul_self) tStar_ne_one

@[expose] noncomputable def tStarC : Cgen := ⟨tStar, tStar_mem_Cgen⟩

@[expose] noncomputable def Zstar : Subgroup Cgen := Subgroup.zpowers tStarC

theorem tStarC_mem_center : tStarC ∈ Subgroup.center Cgen := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_tStar_of_mem_Cgen g.2)

theorem Zstar_le_center : Zstar ≤ Subgroup.center Cgen :=
  (Subgroup.zpowers_le).2 tStarC_mem_center

instance Zstar_normal : Zstar.Normal := Subgroup.normal_of_le_center Zstar_le_center

theorem natCard_Zstar : Nat.card Zstar = 2 := by
  rw [Zstar, Nat.card_zpowers]
  have h := orderOf_injective Cgen.subtype Subtype.coe_injective tStarC
  rw [Subgroup.coe_subtype] at h
  change orderOf tStarC = 2
  rw [← h]
  exact orderOf_tStar

abbrev Cbar : Type := Cgen ⧸ Zstar

@[expose] noncomputable def kappa : Cgen →* Cbar := QuotientGroup.mk' Zstar

theorem kappa_surjective : Function.Surjective kappa := QuotientGroup.mk'_surjective Zstar

theorem ker_kappa : kappa.ker = Zstar := QuotientGroup.ker_mk' Zstar

instance : Finite Cbar := Finite.of_surjective kappa kappa_surjective

@[expose] noncomputable def Jbar : Subgroup Cbar := (Jstar.subgroupOf Cgen).map kappa

@[expose] noncomputable def Ebar : Subgroup Cbar := (rhoCQ.subgroupOf Cgen).map kappa

@[expose] noncomputable def xC : Cgen := ⟨xmat, xmat_mem_Cgen⟩

@[expose] noncomputable def tauC : Cgen := ⟨tauB, tauB_mem_Cgen⟩

@[expose] noncomputable def xbar : Cbar := kappa xC

@[expose] noncomputable def taubar : Cbar := kappa tauC

theorem rhoCQ_le_Cgen : rhoCQ ≤ Cgen := rhoCQ_le_Jstar.trans Jstar_le_Cgen

theorem Ebar_le_Jbar : Ebar ≤ Jbar :=
  Subgroup.map_mono fun _ hx => rhoCQ_le_Jstar hx

theorem xbar_mem_Ebar : xbar ∈ Ebar := ⟨xC, xmat_mem_rhoCQ, rfl⟩

theorem xbar_mem_Jbar : xbar ∈ Jbar := Ebar_le_Jbar xbar_mem_Ebar

theorem short_centralizer_generated_subgroup_data :
    Jstar = Gvis ⊓ Subgroup.centralizer {tStar} ∧
    Cgen = Subgroup.closure (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB))) ∧
    (∀ f, f ∈ rhoCQ ↔ ∃ q ∈ Subgroup.centralizer {rStar}, rhoEquiv q = f) ∧
    tStar ∈ Jstar ∧ xmat ∈ Jstar ∧ rhoCQ ≤ Jstar ∧ Jstar ≤ Cgen ∧ tauB ∈ Cgen ∧
    Cgen ≤ Gmat ⊓ Subgroup.centralizer {tStar} ∧ Finite Cgen ∧
    Zstar = Subgroup.zpowers tStarC ∧ Nat.card Zstar = 2 ∧ Zstar ≤ Subgroup.center Cgen ∧
    Finite Cbar ∧ kappa = QuotientGroup.mk' Zstar ∧ kappa.ker = Zstar ∧
    Jbar = (Jstar.subgroupOf Cgen).map kappa ∧ Ebar = (rhoCQ.subgroupOf Cgen).map kappa ∧
    xbar = kappa ⟨xmat, xmat_mem_Cgen⟩ ∧ taubar = kappa ⟨tauB, tauB_mem_Cgen⟩ ∧
    Ebar ≤ Jbar ∧ xbar ∈ Ebar :=
  ⟨rfl, rfl, fun _ => mem_rhoCQ, tStar_mem_Jstar, xmat_mem_Jstar, rhoCQ_le_Jstar, Jstar_le_Cgen,
    tauB_mem_Cgen, Cgen_le, inferInstance, rfl, natCard_Zstar, Zstar_le_center, inferInstance, rfl,
    ker_kappa, rfl, rfl, rfl, rfl, Ebar_le_Jbar, xbar_mem_Ebar⟩

end CFSG.Monster.B
