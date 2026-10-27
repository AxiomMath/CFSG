module

public import CFSG.Monster.Visible.SignCompat.Triality
public import CFSG.Monster.Visible.Kernel
public import CFSG.Monster.Generated.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Generated Matrix

theorem rhoEquiv_XQ_conj_mem_Hmat (e : Parker) : tauB * rhoEquiv (XQ e) * tauB⁻¹ ∈ Hmat :=
  (thetaEquiv_signLiftPair e) ▸ thetaEquiv_mem_Gvis (signLiftPair e)

theorem piVis_rhoEquiv_XQ_conj (e : Parker) :
    piVis ⟨tauB * rhoEquiv (XQ e) * tauB⁻¹, rhoEquiv_XQ_conj_mem_Hmat e⟩ =
      MulOpposite.op (QuotientGroup.mk (gO e.code)) := by
  have h : (⟨tauB * rhoEquiv (XQ e) * tauB⁻¹, rhoEquiv_XQ_conj_mem_Hmat e⟩ : Gvis) =
      ⟨thetaEquiv (signLiftPair e), thetaEquiv_mem_Gvis (signLiftPair e)⟩ :=
    Subtype.ext (thetaEquiv_signLiftPair e).symm
  rw [h, piVis_thetaEquiv]
  rfl

theorem gO_mem_range_piVis (a : C) :
    (QuotientGroup.mk (gO a) : latticeO ⧸ Subgroup.zpowers negOneO) ∈ piVis.range.unop :=
  mem_unop_range_piVis.2 ⟨signLiftPair ⟨a, 0⟩, rfl⟩

theorem code_sign_compatible_spin_lift :
    (∀ a : C, (fun x => x ᵥ* gmat a) '' latticeQ = latticeQ ∧ gU a ∈ latticeO ∧
      mat (gO a) = gmat a) ∧
    (∀ e : Parker, (YU e, gO e.code) ∈ Pvis) ∧
    (∀ (e : Parker) (h : (YU e, gO e.code) ∈ Pvis),
      thetaEquiv ⟨(YU e, gO e.code), h⟩ = tauB * rhoEquiv (XQ e) * tauB⁻¹) ∧
    (∀ e : Parker, tauB * rhoEquiv (XQ e) * tauB⁻¹ ∈ Hmat ∧
      tauB * rhoEquiv (XQ e) * tauB⁻¹ ∈ Gmat) ∧
    (∀ e : Parker, piVis ⟨tauB * rhoEquiv (XQ e) * tauB⁻¹, rhoEquiv_XQ_conj_mem_Hmat e⟩ =
      MulOpposite.op (QuotientGroup.mk (gO e.code))) ∧
    (∀ a : C,
      (QuotientGroup.mk (gO a) : latticeO ⧸ Subgroup.zpowers negOneO) ∈ piVis.range.unop) :=
  ⟨fun a => ⟨image_latticeQ_gmat a, gU_mem_latticeO a, mat_gO a⟩, YU_gO_mem_Pvis,
    fun e _ => thetaEquiv_signLiftPair e,
    fun e => ⟨rhoEquiv_XQ_conj_mem_Hmat e, Hmat_le_Gmat (rhoEquiv_XQ_conj_mem_Hmat e)⟩,
    piVis_rhoEquiv_XQ_conj, gO_mem_range_piVis⟩

end CFSG.Monster.Visible
