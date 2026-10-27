module

public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTBJNaWeylQFourOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGInnerDiagOnLabel S p Bs L →
        ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          ∃ a ∈ ggTorusReflSetIn p J (ggGamma L hN).range,
            ∃ b ∈ ggTorusReflSetIn p J (ggGamma L hN).range, a * b ≠ b * a

theorem exists_noncomm_reflections_of_weylReflSetIn {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs K J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hnc : ∃ a ∈ ggTorusReflSetIn p J (ggGamma K hN).range,
      ∃ b ∈ ggTorusReflSetIn p J (ggGamma K hN).range, a * b ≠ b * a) :
    ∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs,
      GGIsReflection p a ∧ GGIsReflection p b ∧ a * b ≠ b * a := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  simp only [ggTorusReflSetIn, Set.mem_setOf_eq] at ha hb
  obtain ⟨na, hna, hnaJ, hnaW, rfl, hrefla⟩ := ha
  obtain ⟨nb, hnb, hnbJ, hnbW, rfl, hreflb⟩ := hb
  obtain ⟨ga, hgaJ, hga, hrefla', haover⟩ :=
    exists_isReflection_overGamma_of_weylElt_mem (n := na) hp hp2 hBs hSC hN
      hnaJ hnaW hna hrefla
  obtain ⟨gb, hgbJ, hgb, hreflb', hbover⟩ :=
    exists_isReflection_overGamma_of_weylElt_mem (n := nb) hp hp2 hBs hSC hN
      hnbJ hnbW hnb hreflb
  refine ⟨ggConjAut Bs hga, ggConjAut_mem_ggAutomizer hgaJ hga,
    ggConjAut Bs hgb, ggConjAut_mem_ggAutomizer hgbJ hgb, hrefla', hreflb', ?_⟩
  intro hcd
  have h1 := haover.mul hbover
  have h2 := hbover.mul haover
  rw [← hcd] at h2
  exact hab (GGOverGamma.unique h1 h2)

theorem ggTBJNoncommReflOn_of_naWeyl {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBJNaWeylQFourOn S) : GGTBJNoncommReflOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  have hcfg := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  exact exists_noncomm_reflections_of_weylReflSetIn hp hp2 hBs hSC hBsN
    (h G p B Bs x L D J hHyp hq hN hL hBsN)

end CFSG.StandardType

end
