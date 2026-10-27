module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettled
public import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo
public import CFSG.LocalAnalysis.StandardType.GGCentreTwoKnownHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResF4_exists_hasLabel_F4
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
    (hF4 : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs L) :
    ∃ f : ℕ, GGHasLabel ⟨.F4, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨-, lab, -, hraw⟩ := hF4
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀'⟩ := hP₀
  obtain ⟨htag, -, -⟩ := hP₀'
  cases htag
  change LargeEvenRawDatum ⟨.F4, 4, n⟩ _ at hraw
  refine ⟨n, ?_⟩
  have hLabel4 : GGHasLabel ⟨.F4, 4, n⟩ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  simpa [GGHasLabel, LargeEvenRawDatum] using hLabel4

section Cert

theorem GGResHyp.not_exactThree_K_of_f4Three_L_residual_K
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L)
    (hK : GGInnerDiagOnLabel
      (fun p lab => ggThreeResidualLabelK p lab ∧ 2 ≤ lab.n) 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  intro h3
  have hCfg : GGConfig 3 B Bs x L D J := hH.1
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hLperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K :=
    hK.mono_label (fun lab h => ⟨h.1.1, h.1.2.1, h.2, h.1.2.2.2⟩)
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨-, _, _, -, -, -, -, -, -, -, -, -, -, -, hBs5, hAJ6, -, -⟩ :=
    hH.relativeF4_K3_classification (Or.inl hL) hU hN h3
  have hFmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) 3 Bs L :=
    hL.mono_label (fun lab h => h.1)
  obtain ⟨f, hLabel⟩ := ggResF4_exists_hasLabel_F4 hFmark
  haveI : Finite ↥L := Finite.of_injective (Subgroup.subtype L) Subtype.coe_injective
  haveI : Fintype ↥L := Fintype.ofFinite _
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLperf
  haveI : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
  have hZcard : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L) :=
    not_three_dvd_card_center_of_ggHasLabel_F4 hLabel
  have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3dvd
    apply hZcard
    have hdvd : orderOf g ∣ Nat.card ↥(Subgroup.center ↥L) := by
      rw [Nat.card_eq_fintype_card]
      have h := orderOf_dvd_card (x := (⟨g, hg⟩ : ↥(Subgroup.center ↥L)))
      simpa using h
    exact dvd_trans h3dvd hdvd
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
    ggResF4_innerOnL_of_label (p := 3)
      (hF4 := hL.mono_label (fun lab h => ⟨h.2.1, h.1⟩)) hLperf
  have h48 := ggResF4_automizerJ_card_ge_48 ggCentreTwoKnown_holds hCfg hBs5 hLabel
    hLperf hZL hInnL
  omega

end Cert

end CFSG.StandardType

end
