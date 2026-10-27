module

public import CFSG.Monster.B.Short.ParityCentralizer
public import CFSG.Monster.B.Cbar.GenData
public import CFSG.Monster.Visible.Irreducible

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short

namespace Overgroup

@[expose] def piImage (K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Subgroup OLq :=
  ((K'.subgroupOf Gvis).map piVis).unop

theorem mem_piImage {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} {x : OLq} :
    x ∈ piImage K' ↔ ∃ f : Gvis, (f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ K' ∧ piVis f = MulOpposite.op x := by
  rw [piImage, Subgroup.mem_unop, Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem mem_Gvis_of_mem_Gmat_of_comm {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat)
    (h : g * xmat = xmat * g) : g ∈ Gvis := by
  have h1 : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
    ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 h⟩
  rw [Gmat_inf_centralizer_xmat] at h1
  exact h1

theorem Kstab_le_piImage
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hC : Cgen ≤ K') :
    Kstab (classOf (vMinus 0 1)) ≤ piImage K' := by
  intro k hk
  rw [mem_piImage]
  have hk' : MulOpposite.op k ∈ (piJ rStar).range := by
    rw [range_piJ isShortCoord_rStar, phi0_coordOf_rStar]
    exact hk
  obtain ⟨f, hf⟩ := hk'
  obtain ⟨hfV, hfc⟩ := mem_Jmat_iff.1 f.2
  exact ⟨⟨f.1, Jmat_le_Gvis rStar f.2⟩,
    hC (Jstar_le_Cgen ⟨hfV, Subgroup.mem_centralizer_singleton_iff.2 hfc⟩), hf⟩

theorem xmat_mul_tStar : xmat * tStar = tStar * xmat :=
  Subgroup.mem_centralizer_singleton_iff.1 xmat_mem_Jstar.2

theorem piVis_not_mem_Kstab {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis)
    (hg1 : g * tStar * g⁻¹ ≠ tStar) (hg2 : g * tStar * g⁻¹ ≠ xmat * tStar) :
    (piVis ⟨g, hg⟩).unop ∉ Kstab (classOf (vMinus 0 1)) := by
  intro hk
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  rw [piVis_thetaEquiv, MulOpposite.unop_op, mk_mem_Kstab_iff] at hk
  have h1 : phi0 (coordOf (conjQ p rStar)) = phi0 (coordOf rStar) := by
    rw [← toAdd_phi_mk, phi_conjQ, toAdd_phi_mk, phi0_coordOf_rStar]
    exact hk
  have h3 : thetaEquiv p * tStar * (thetaEquiv p)⁻¹ = rhoEquiv (conjQ p rStar) :=
    Short.thetaEquiv_conj_rhoEquiv p rStar
  rcases eq_or_eq_zQ_mul_of_coordOf_eq (phi0_injective h1) with h2 | h2
  · exact hg1 (h3.trans (congrArg rhoEquiv h2))
  · refine hg2 (h3.trans ((congrArg rhoEquiv h2).trans ?_))
    rw [rhoEquiv_mul, xmat_mul_tStar]
    rfl

theorem piImage_eq_top
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hC : Cgen ≤ K')
    (hmax : ∀ X : Subgroup OLq, Kstab (classOf (vMinus 0 1)) ≤ X →
      X = Kstab (classOf (vMinus 0 1)) ∨ X = ⊤)
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hgK : g ∈ K') (hgV : g ∈ Gvis)
    (hg1 : g * tStar * g⁻¹ ≠ tStar) (hg2 : g * tStar * g⁻¹ ≠ xmat * tStar) :
    piImage K' = ⊤ := by
  rcases hmax _ (Kstab_le_piImage hC) with h | h
  · exfalso
    have hmem : (piVis ⟨g, hgV⟩).unop ∈ piImage K' :=
      mem_piImage.2 ⟨⟨g, hgV⟩, hgK, (MulOpposite.op_unop _).symm⟩
    rw [h] at hmem
    exact piVis_not_mem_Kstab hgV hg1 hg2 hmem
  · exact h

@[expose] def rhoSub (K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Submodule (ZMod 2) L2 :=
  have h0 : ∃ q : Q, rhoEquiv q ∈ K' ∧ phi0 (coordOf q) = 0 :=
    ⟨1, by rw [rhoEquiv_one]; exact K'.one_mem, by
      rw [(mem_zpowers_zQ_iff 1).1 (Subgroup.one_mem _), map_zero]⟩
  { carrier := {w | ∃ q : Q, rhoEquiv q ∈ K' ∧ phi0 (coordOf q) = w}
    zero_mem' := h0
    add_mem' := by
      rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩
      exact ⟨q₁ * q₂, by rw [rhoEquiv_mul]; exact K'.mul_mem h₂ h₁, by
        rw [coordOf_mul, map_add]⟩
    smul_mem' := by
      intro c w hw
      rcases Visible.zmod_two_cases c with rfl | rfl
      · rw [zero_smul]
        exact h0
      · rw [one_smul]
        exact hw }

theorem exists_mem_of_piImage_eq_top {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)}
    (hX : piImage K' = ⊤) (p : Pvis) :
    ∃ p' : Pvis, thetaEquiv p' ∈ K' ∧ modTwoEnd p'.1.2 = modTwoEnd p.1.2 := by
  have hmem : (QuotientGroup.mk p.1.2 : OLq) ∈ piImage K' := hX ▸ Subgroup.mem_top _
  obtain ⟨f, hfK, hf⟩ := mem_piImage.1 hmem
  obtain ⟨p', hp'⟩ := mem_Gvis.1 f.2
  have hf' : f = ⟨thetaEquiv p', thetaEquiv_mem_Gvis p'⟩ := Subtype.ext hp'.symm
  rw [hf', piVis_thetaEquiv] at hf
  have h2 : (QuotientGroup.mk p'.1.2 : OLq) = QuotientGroup.mk p.1.2 :=
    MulOpposite.op_injective hf
  refine ⟨p', hp' ▸ hfK, ?_⟩
  rw [← kOp_mk, h2, kOp_mk]

theorem rhoSub_invariant {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hX : piImage K' = ⊤)
    (p : Pvis) (w : L2) (hw : w ∈ rhoSub K') : modTwoEnd p.1.2 w ∈ rhoSub K' := by
  obtain ⟨q, hq, rfl⟩ := hw
  obtain ⟨p', hp'K, hp'⟩ := exists_mem_of_piImage_eq_top hX p
  refine ⟨conjQ p' q, ?_, ?_⟩
  · rw [← Short.thetaEquiv_conj_rhoEquiv]
    exact K'.mul_mem (K'.mul_mem hp'K hq) (K'.inv_mem hp'K)
  · calc phi0 (coordOf (conjQ p' q))
        = Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p' q))) := (toAdd_phi_mk _).symm
      _ = modTwoEnd p'.1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk q))) := phi_conjQ p' q
      _ = modTwoEnd p'.1.2 (phi0 (coordOf q)) := congrArg (modTwoEnd p'.1.2) (toAdd_phi_mk q)
      _ = modTwoEnd p.1.2 (phi0 (coordOf q)) := LinearMap.congr_fun hp' _

theorem rhoQ_le_of_piImage_eq_top {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hC : Cgen ≤ K')
    (hX : piImage K' = ⊤) : rhoQ ≤ K' := by
  have hne : rhoSub K' ≠ ⊥ := by
    intro h
    have hmem : phi0 (coordOf rStar) ∈ rhoSub K' := ⟨rStar, hC tStar_mem_Cgen, rfl⟩
    rw [h, Submodule.mem_bot, phi0_coordOf_rStar] at hmem
    exact classOf_ne_zero_of_mem_minVecs vMinus_zero_one_mem hmem
  have htop : rhoSub K' = ⊤ :=
    (eq_bot_or_eq_top_of_invariant (rhoSub_invariant hX)).resolve_left hne
  intro f hf
  obtain ⟨q, rfl⟩ := mem_rhoQ.1 hf
  have hmem : phi0 (coordOf q) ∈ rhoSub K' := htop ▸ Submodule.mem_top
  obtain ⟨q', hq', hq'q⟩ := hmem
  rcases eq_or_eq_zQ_mul_of_coordOf_eq (phi0_injective hq'q) with h | h
  · exact h ▸ hq'
  · rw [h, rhoEquiv_mul] at hq'
    have e : rhoEquiv q = rhoEquiv q * rhoEquiv zQ * (rhoEquiv zQ)⁻¹ := by group
    rw [e]
    exact K'.mul_mem hq' (K'.inv_mem (hC xmat_mem_Cgen))

theorem Gvis_le_of_piImage_eq_top {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hX : piImage K' = ⊤)
    (hρ : rhoQ ≤ K') : Gvis ≤ K' := by
  intro h hh
  have hmem : (piVis ⟨h, hh⟩).unop ∈ piImage K' := hX ▸ Subgroup.mem_top _
  obtain ⟨f, hfK, hf⟩ := mem_piImage.1 hmem
  have hker : (⟨h, hh⟩ * f⁻¹ : Gvis) ∈ piVis.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hf, MulOpposite.op_unop, mul_inv_cancel]
  rw [ker_piVis, Subgroup.mem_subgroupOf] at hker
  have e : h = h * (f : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * f := by group
  rw [e]
  exact K'.mul_mem (hρ hker) hfK

end Overgroup

open Overgroup

theorem eq_Gmat_of_Cgen_le
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hK : K' ≤ Gmat) (hC : Cgen ≤ K')
    (hmax : ∀ X : Subgroup OLq, Kstab (classOf (vMinus 0 1)) ≤ X →
      X = Kstab (classOf (vMinus 0 1)) ∨ X = ⊤)
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hgK : g ∈ K') (hgx : g * xmat = xmat * g)
    (hg1 : g * tStar * g⁻¹ ≠ tStar) (hg2 : g * tStar * g⁻¹ ≠ xmat * tStar) : K' = Gmat := by
  have hgV : g ∈ Gvis := mem_Gvis_of_mem_Gmat_of_comm (hK hgK) hgx
  have hX : piImage K' = ⊤ := piImage_eq_top hC hmax hgK hgV hg1 hg2
  have hV : Gvis ≤ K' := Gvis_le_of_piImage_eq_top hX (rhoQ_le_of_piImage_eq_top hC hX)
  refine le_antisymm hK ?_
  rw [Gmat, Subgroup.closure_le]
  rintro f (hf | hf)
  · exact hV hf
  · rw [Set.mem_singleton_iff.1 hf]
    exact hC tauB_mem_Cgen

theorem eq_Gmat_of_Cgen_le'
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hK : K' ≤ Gmat) (hC : Cgen ≤ K')
    (hmax : ∀ X : Subgroup OLq, Kstab (classOf (vMinus 0 1)) ≤ X →
      X = Kstab (classOf (vMinus 0 1)) ∨ X = ⊤)
    {g : SpaceB ≃ₗ[ℚ] SpaceB} (hgK : g ∈ K') (hgx : g * xmat = xmat * g)
    (hg1 : g * tStar * g⁻¹ ≠ tStar) (hg2 : g * tStar * g⁻¹ ≠ tStar * xmat) : K' = Gmat :=
  eq_Gmat_of_Cgen_le hK hC hmax hgK hgx hg1 fun h => hg2 (h.trans xmat_mul_tStar)

end CFSG.YGroups.Y443
