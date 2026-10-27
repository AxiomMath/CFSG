module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_exists_natural_normalizer_embedding
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L))) :
    ∃ ρ : ↥(Mbar D.M V₀ V hV) →*
        MulAut (Multiplicative (ι → K)),
      Function.Injective ρ ∧
      ∀ a : ↥(Mbar D.M V₀ V hV), ρ a ∈ s16gNorm Γ := by
  have hHA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hHn : ∀ a ∈ Mbar D.M V₀ V hV, ∀ h ∈ lBar V₀ V hV L,
      a * h * a⁻¹ ∈ lBar V₀ V hV L := by
    intro a ha h hh
    exact (Subgroup.mem_normalizer_iff.mp (s15_Three_le_normalizer hs ha) h).1 hh
  have hR' := s16g_realizes_top c.conc hs Γ hR
  exact s16g_exists_embedding hHA hHn hR' (wTil_eq_top_of_case163_2 c.conc hs)

theorem s168e3_exists_matrix_elem_of_natural_of_coprime
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)))
    (hΓ : AddCommutantScalar Γ)
    {p : ℕ} (hpσ : p ∈ D.sig)
    (hpK : ¬ p ∣ Nat.card (RingAut K)) :
    ∃ F : Subgroup (Matrix.GeneralLinearGroup ι K),
      F ≤ Subgroup.normalizer (Γ : Set (Matrix.GeneralLinearGroup ι K)) ∧
      IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  have hp : p.Prime := (D.sig_prime p hpσ).1
  obtain ⟨E₀, hE₀el, hE₀card⟩ :=
    exists_isElemAbelian_subgroupOf_of_le_pRank (M := Mbar D.M V₀ V hV) hp
      (c.two_le_pRank_mbar hpσ)
  obtain ⟨ρ, hρinj, hρN⟩ := s168e3_exists_natural_normalizer_embedding c hs Γ hR
  let E : Subgroup (MulAut (Multiplicative (ι → K))) := E₀.map ρ
  have hEel : IsElemAbelian p E := hE₀el.map ρ
  have hEcard : Nat.card E = p ^ 2 := by
    rw [show Nat.card E = Nat.card E₀ from Subgroup.card_map_of_injective hρinj, hE₀card]
  have hEN : E ≤ s16gNorm Γ := by
    rintro _ ⟨x, -, rfl⟩
    exact hρN x
  have hEL : E ≤ s16gLin ι K :=
    s16g_le_lin_of_coprime hΓ hp hpK hEN hEel.isPGroup
  obtain ⟨F, hFN, hFel, hFcard⟩ :=
    s16g_exists_matrix_elem_of_lin (Γ := Γ) (p := p) (E := E) hEN hEL hEel
  exact ⟨F, hFN, hFel, by rw [hFcard, hEcard]⟩

theorem s168e3_false_of_natural_fixNc
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)))
    (hne : ∃ a : Multiplicative (ι → K), a ≠ 1)
    {p : ℕ} (hpσ : p ∈ D.sig) (hfix : FixNc Γ p) : False := by
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hR' := s16g_realizes_top c.conc hs Γ hR
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hZ : ∀ h ∈ lBar V₀ V hV L, ∀ z ∈ fixV (lBar V₀ V hV L), h z = z :=
    fun h hh z hz => (mem_fixV.1 hz) h hh
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hfixM : S168e3Fix (Mbar D.M V₀ V hV) p := by
    intro x hx1
    obtain ⟨B, hBH, hBp, hBc, hBfix⟩ :=
      s16g_transport_fix Γ hR' hW hZ hne hp hp2 hfix hx1
    exact ⟨B, hBH.trans hle, hBp, hBc, hBfix⟩
  exact s168e3_false_of_fix c hp hpσ hfixM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
