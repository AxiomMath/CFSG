module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ltrb1r0_relIndex_inf_eq_of_sup {A : Type} [Group A] {H G M : Subgroup A}
    (hHG : H ≤ G) (hsup : G ≤ H ⊔ (G ⊓ M)) (hN : (H.subgroupOf G).Normal) :
    (H ⊓ M).relIndex (G ⊓ M) = H.relIndex G := by
  let H' : Subgroup G := H.subgroupOf G
  let M' : Subgroup G := (G ⊓ M).subgroupOf G
  have hHM : (H ⊓ M).subgroupOf G = H' ⊓ M' := by
    ext x
    simp only [H', M', Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    tauto
  have hTop : H' ⊔ M' = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hHG,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left : G ⊓ M ≤ G)]
    exact le_antisymm (sup_le hHG inf_le_left) hsup
  have h1 : H'.relIndex ⊤ = H.relIndex G := by
    have h := Subgroup.relIndex_subgroupOf (H := H) (K := G) (L := G) le_rfl
    simpa [H', Subgroup.subgroupOf_self] using h
  have h2 : H'.relIndex M' = (H' ⊓ M').relIndex M' :=
    (Subgroup.inf_relIndex_right H' M').symm
  have h3 : H'.relIndex M' = H'.relIndex ⊤ := by
    haveI : H'.Normal := hN
    have h := Subgroup.relIndex_sup_left (K := H') (H := M')
    rw [hTop] at h
    exact h.symm
  have h4 : (H' ⊓ M').relIndex M' = H.relIndex G :=
    ((h2.symm.trans h3).trans h1)
  have h5 : (H' ⊓ M').relIndex M' = (H ⊓ M).relIndex (G ⊓ M) := by
    have h := Subgroup.relIndex_subgroupOf (H := H ⊓ M) (K := G ⊓ M) (L := G) inf_le_left
    rw [hHM] at h
    simpa [M'] using h
  exact h5.symm.trans h4

theorem fixedCosetRepresentativeAt_of_lang {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hL : LangOnConnectedAt ρ)
    (hHG : connectedCentralizer ρ ≤ geomCentralizer ρ) : FixedCosetRepresentativeAt ρ := by
  intro x hxG hxH
  obtain ⟨y, hyG, hyfix, hyH⟩ :=
    fixed_representative_of_lang ρ.setup.D.step (connectedCentralizer ρ) (geomCentralizer ρ)
      hHG hL hxG hxH
  refine ⟨y, hyG, ?_, hyH⟩
  rw [LangDatum.mem_model]
  refine ⟨(inf_le_left : geomCentralizer ρ ≤ adjointGroup ρ.tau Omega) hyG, ?_⟩
  have h : ρ.setup.D.n * ρ.setup.D.Φ y * ρ.setup.D.n⁻¹ = ρ.setup.D.step y := by
    simp [LangDatum.step, MulAut.conj_apply]
  rw [h, hyfix]

theorem b1RatOn_of_frobenius_trivial {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {row : LargeEvenLabel → LargeEvenLabel → Prop} {g : ℕ}
    (ha : B1aOn Omega) (hb : B1bOn Omega) (hg : B1GeomOn Omega row g)
    (hF : FrobeniusTrivialOn Omega row) (hL : LangOnConnectedOn Omega row) :
    B1RatOn Omega row g := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  have hHG : connectedCentralizer ρ ≤ geomCentralizer ρ :=
    (hb lab R I phi ρ j hΛ hj hqs).1
  have hNorm : ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal :=
    (hb lab R I phi ρ j hΛ hj hqs).2.1
  have hFr : ∀ x ∈ geomCentralizer ρ, ρ.setup.D.step x * x⁻¹ ∈ connectedCentralizer ρ :=
    hF lab R I phi ρ j hΛ hj hqs hrow
  have hLang : LangOnConnectedAt ρ := hL lab R I phi ρ j hΛ hj hqs hrow
  have hge : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = g :=
    hg lab R I phi ρ j hΛ hj hqs hrow
  have hC : centralizerGroup ρ =
      ((geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction :=
    (ha lab R I phi ρ j hΛ hj hqs).1
  have hC1 : conn ρ =
      ((connectedCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map
        ρ.modelAction := rfl
  have hL1 : FixedCosetRepresentativeAt ρ :=
    fixedCosetRepresentativeAt_of_lang ρ hLang hHG
  have hsup : geomCentralizer ρ ≤
      connectedCentralizer ρ ⊔ (geomCentralizer ρ ⊓ ρ.setup.D.model) := by
    intro x hxG
    obtain ⟨y, hyG, hyM, hyH⟩ := hL1 x hxG (hFr x hxG)
    have hx_eq : x = (y * x⁻¹)⁻¹ * y := by group
    rw [hx_eq]
    exact (connectedCentralizer ρ ⊔ (geomCentralizer ρ ⊓ ρ.setup.D.model)).mul_mem
      (Subgroup.mem_sup_left ((connectedCentralizer ρ).inv_mem hyH))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hyG, hyM⟩))
  have hrel : (conn ρ).relIndex (centralizerGroup ρ) =
      (connectedCentralizer ρ).relIndex (geomCentralizer ρ) := by
    rw [hC1, hC]
    rw [Subgroup.relIndex_map_map_of_injective (f := ρ.modelAction)
      ((connectedCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model)
      ((geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model) ρ.modelAction_inj]
    rw [Subgroup.relIndex_subgroupOf (H := connectedCentralizer ρ ⊓ ρ.setup.D.model)
      (K := geomCentralizer ρ ⊓ ρ.setup.D.model) (L := ρ.setup.D.model) inf_le_right]
    exact ltrb1r0_relIndex_inf_eq_of_sup hHG hsup hNorm
  rw [hrel, hge]

end CFSG.StandardType.S2MathAs1E6Companion1625

end
