
module

public import CFSG.Monster.B.Short.TransitivityBase

public import CFSG.Monster.B.Short.OrbitCert
public import CFSG.Monster.B.Short.OrbitSpec
public import CFSG.Monster.B.Short.AxisAction
public import CFSG.Monster.VisCert.FrameOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.Generated

theorem shortFacts : ShortFacts Native.shortTables :=
  shortFacts_of_check (by norm_num) shortCertOK_eq_true

theorem orbit_Kvis_short :
    MulAction.orbit Kvis (classOf (vMinus 0 1)) = shortSet := by
  have hsub := shortFacts.image_shortFound_subset_orbit kGenN_smul_dec
  rw [closure_kGenN_Iio, dec_shortSeed] at hsub
  have hcard := shortFacts.ncard_image_shortFound dec_inj
  have horb : MulAction.orbit Kvis (classOf (vMinus 0 1)) ⊆ shortSet := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact smul_mem_shortSet_of_mem_Hvis (Kvis_le_Hvis hu) classOf_vMinus_mem_shortSet
  have heq : dec '' (shortFound Native.shortTables : Set ℕ) = shortSet :=
    Set.eq_of_subset_of_ncard_le (hsub.trans horb) (by rw [ncard_shortSet, hcard]; rfl)
  exact Set.Subset.antisymm horb (heq ▸ hsub)

theorem exists_Kvis_smul_eq_of_short
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    ∃ k ∈ Kvis, k • x = y := by
  rw [← orbit_Kvis_short] at hx hy
  obtain ⟨⟨a, ha⟩, rfl⟩ := hx
  obtain ⟨⟨b, hb⟩, rfl⟩ := hy
  refine ⟨b * a⁻¹, Kvis.mul_mem hb (Kvis.inv_mem ha), ?_⟩
  change (b * a⁻¹) • a • classOf (vMinus 0 1) = b • classOf (vMinus 0 1)
  rw [smul_smul, inv_mul_cancel_right]

theorem exists_Hvis_smul_eq_of_short
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    ∃ u ∈ Hvis, u • x = y := by
  obtain ⟨k, hk, hkx⟩ := exists_Kvis_smul_eq_of_short hx hy
  exact ⟨k, Kvis_le_Hvis hk, hkx⟩

theorem exists_Pvis_of_short
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    ∃ p : Pvis, modTwoEnd p.1.2 x = y := by
  obtain ⟨u, hu, hux⟩ := exists_Hvis_smul_eq_of_short hx hy
  obtain ⟨g, hg, rfl⟩ := mem_Hvis.1 hu
  obtain ⟨s₀, hs₀⟩ := mem_PvisLat.1 hg
  exact ⟨⟨(s₀, g), hs₀⟩, hux⟩

theorem exists_Gvis_conj_short
    {r s : Q} (hr : IsShortCoord (coordOf r))
    (hs : IsShortCoord (coordOf s)) :
    ∃ g ∈ Gvis, g * rhoEquiv r * g⁻¹ = rhoEquiv s ∧ g (axis r) = axis s := by
  obtain ⟨p, hp⟩ := exists_Pvis_of_short (phi0_mem_shortSet hr) (phi0_mem_shortSet hs)
  exact exists_Gvis_conj_rho_axis hr hs p hp

theorem axis_mem_axisOrbit
    {r : Q} (hr : IsShortCoord (coordOf r)) : axis r ∈ axisOrbit := by
  obtain ⟨g, hg, -, hga⟩ := exists_Gvis_conj_short isShortCoord_rStar hr
  exact ⟨g, Hmat_le_Gmat hg, hga⟩

theorem short_label_visible_transitivity :
    {c : L2 | ∃ u ∈ minVecs, classOf u = c}.ncard = 98280 ∧
    (∀ x ∈ {c : L2 | ∃ u ∈ minVecs, classOf u = c}, ∀ y ∈ {c : L2 | ∃ u ∈ minVecs, classOf u = c},
      ∃ k ∈ Hvis, k • x = y) ∧
    (∀ x ∈ {c : L2 | ∃ u ∈ minVecs, classOf u = c}, ∀ y ∈ {c : L2 | ∃ u ∈ minVecs, classOf u = c},
      ∃ p : Pvis, modTwoEnd p.1.2 x = y) ∧
    (∀ r s : Q, IsShortCoord (coordOf r) → IsShortCoord (coordOf s) →
      ∃ g ∈ Gvis, g * rhoEquiv r * g⁻¹ = rhoEquiv s ∧ g (axis r) = axis s) ∧
    (∀ r : Q, IsShortCoord (coordOf r) → axis r ∈ axisOrbit) :=
  ⟨ncard_shortSet, fun _ hx _ hy => exists_Hvis_smul_eq_of_short hx hy,
    fun _ hx _ hy => exists_Pvis_of_short hx hy, fun _ _ hr hs => exists_Gvis_conj_short hr hs,
    fun _ hr => axis_mem_axisOrbit hr⟩

end CFSG.Monster.B.Short
