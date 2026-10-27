module

public import CFSG.Monster.B.Cbar.GenData
public import CFSG.Monster.B.Short.ParityJ

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

theorem Jstar_eq_Jmat : Jstar = Jmat rStar := by
  ext f
  rw [mem_Jmat_iff, Jstar, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact Iff.rfl

theorem Jmat_le_Cgen : Jmat rStar ≤ Cgen := Jstar_eq_Jmat ▸ Jstar_le_Cgen

@[expose] noncomputable def jHom : Jmat rStar →* Cbar :=
  kappa.comp (Subgroup.inclusion Jmat_le_Cgen)

theorem jHom_apply (g : Jmat rStar) : jHom g = kappa ⟨g, Jmat_le_Cgen g.2⟩ := rfl

theorem range_jHom : jHom.range = Jbar := by
  ext c
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨g, Jmat_le_Cgen g.2⟩, ?_, rfl⟩
    show (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar
    rw [Jstar_eq_Jmat]
    exact g.2
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jmat rStar := Jstar_eq_Jmat ▸ hg
    exact ⟨⟨g, hg'⟩, rfl⟩

theorem tJ_eq : ((tJ rStar : Jmat rStar) : SpaceB ≃ₗ[ℚ] SpaceB) = tStar := rfl

theorem mem_zpowers_tJ_iff (g : Jmat rStar) :
    g ∈ Subgroup.zpowers (tJ rStar) ↔
      (⟨g, Jmat_le_Cgen g.2⟩ : Cgen) ∈ Subgroup.zpowers tStarC := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [← hk]; rfl)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by
      have := congrArg Subtype.val hk
      rw [SubgroupClass.coe_zpow] at this ⊢
      exact this)⟩

theorem ker_jHom : jHom.ker = Subgroup.zpowers (tJ rStar) := by
  ext g
  rw [MonoidHom.mem_ker, jHom_apply, mem_zpowers_tJ_iff]
  exact (QuotientGroup.eq_one_iff _)

@[expose] noncomputable def jEquiv : Jmat rStar ⧸ Subgroup.zpowers (tJ rStar) ≃* Jbar :=
  (QuotientGroup.quotientMulEquivOfEq ker_jHom.symm).trans
    ((QuotientGroup.quotientKerEquivRange jHom).trans (MulEquiv.subgroupCongr range_jHom))

theorem coe_jEquiv_mk (g : Jmat rStar) :
    ((jEquiv (QuotientGroup.mk g) : Jbar) : Cbar) = kappa ⟨g, Jmat_le_Cgen g.2⟩ := rfl

@[expose] noncomputable def jEmb : Jmat rStar ⧸ Subgroup.zpowers (tJ rStar) →* Cbar :=
  Jbar.subtype.comp jEquiv.toMonoidHom

theorem jEmb_mk (g : Jmat rStar) : jEmb (QuotientGroup.mk g) = kappa ⟨g, Jmat_le_Cgen g.2⟩ := rfl

theorem jEmb_injective : Function.Injective jEmb :=
  Subtype.coe_injective.comp jEquiv.injective

theorem range_jEmb : jEmb.range = Jbar := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact (jEquiv y).2
  · intro hc
    exact ⟨jEquiv.symm ⟨c, hc⟩, by rw [jEmb, MonoidHom.comp_apply]; simp⟩

theorem jEmb_mk_xJ : jEmb (QuotientGroup.mk (xJ rStar)) = xbar := rfl

theorem rhoCent_eq_rhoCQ : rhoCent rStar = rhoCQ := by
  ext f
  rw [mem_rhoCQ]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    rfl
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    rw [rhoHom_apply, inv_inv]

theorem map_Equot_eq_Ebar : (Equot rStar).map jEmb = Ebar := by
  ext c
  constructor
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨⟨g, Jmat_le_Cgen g.2⟩, ?_, rfl⟩
    show (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoCQ
    rw [← rhoCent_eq_rhoCQ]
    exact hg
  · rintro ⟨g, hg, rfl⟩
    have hgJ : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jmat rStar := Jstar_eq_Jmat ▸ rhoCQ_le_Jstar hg
    refine ⟨QuotientGroup.mk ⟨g, hgJ⟩, ⟨⟨g, hgJ⟩, ?_, rfl⟩, rfl⟩
    show (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoCent rStar
    rw [rhoCent_eq_rhoCQ]
    exact hg

@[expose] noncomputable def eEquiv : Equot rStar ≃* Ebar :=
  (Subgroup.equivMapOfInjective (Equot rStar) jEmb jEmb_injective).trans
    (MulEquiv.subgroupCongr map_Equot_eq_Ebar)

theorem coe_eEquiv (y : Equot rStar) : ((eEquiv y : Ebar) : Cbar) = jEmb y := rfl

end CFSG.Monster.B
