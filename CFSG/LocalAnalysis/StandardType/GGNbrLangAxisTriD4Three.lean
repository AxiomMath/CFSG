module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylResidualTriD4
public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangAxisTriD4ThreeAux_lieModel {G : Type} [Group G] {K : Subgroup G}
    {lab : LargeEvenLabel} {R : Type} [Group R] (ht : lab.tag = .triD4)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hMM : MarkedModel lab R) :
    CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .trialityD4 0 2 lab.n := by
  have hX : MarkedModel lab (↥K ⧸ Subgroup.center ↥K) := MarkedModel.of_mulEquiv θ.symm hMM
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  exact hX

private theorem ggNbrLangAxisTriD4ThreeAux_not_clauseFive
    {G : Type} [Group G]
    {p : ℕ} {x : G} {K : Subgroup G} (h5 : GGNbrClauseFiveMarking p x K)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsTriD4ThreeLabel p lab)
    {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hMM : MarkedModel lab R) : False := by
  have hX : MarkedModel lab (↥K ⧸ Subgroup.center ↥K) := MarkedModel.of_mulEquiv θ.symm hMM
  rcases largeEvenMarking_or h5 with hHS | hPF
  · obtain ⟨lab', hlab', R', _, I', F', θ', -, -, hHS', hMM'⟩ :=
      largeEvenMarking_exists_markedModel hHS
    have hX' : MarkedModel lab' (↥K ⧸ Subgroup.center ↥K) := MarkedModel.of_mulEquiv θ'.symm hMM'
    by_cases hc' : markChar lab' = 2
    · exact NbrInnerMore.not_halfSplit_of_markedModel_triD4Three hlab h hX hlab' hc' hX'
        (Subgroup.center ↥K = ⊥) hHS'
    · exact NbrInnerMore.not_markedModel_char_ne_two_triD4 h.1 hX hc' hX'
  · obtain ⟨lab', hlab', R', _, I', F', θ', -, -, hPF', hMM'⟩ :=
      largeEvenMarking_exists_markedModel hPF
    have hX' : MarkedModel lab' (↥K ⧸ Subgroup.center ↥K) := MarkedModel.of_mulEquiv θ'.symm hMM'
    have hn : 2 ≤ lab.n := h.2.2.1
    have hL := ggNbrLangAxisTriD4ThreeAux_lieModel h.1 θ hMM
    by_cases hc' : markChar lab' = 2
    · obtain ⟨ht', -⟩ := NbrInnerMore.eq_of_markedModel_triD4 (by omega : 1 ≤ lab.n) hL hlab'
        hc' hX'
      rcases hPF'.1 with hne | hp3
      · exact hne ht'
      · exact hp3 h.2.1
    · exact NbrInnerMore.not_markedModel_char_ne_two_triD4 h.1 hX hc' hX'

theorem ggNbrLangAxisOn_nsTriD4Three :
    GGNbrLangAxisOn GGNbrNsTriD4ThreeLabel := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hP
  by_cases hSl : GGNbrNsTriD4ThreeLabel p lab
  · exfalso
    obtain ⟨R, _, I, F, -, -, θ, -, hMM⟩ := largeEvenRawDatum_exists hraw
    have h5 : GGNbrClauseFiveMarking p x K :=
      (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hcfg.2.2, hnb.2⟩).2
    exact ggNbrLangAxisTriD4ThreeAux_not_clauseFive h5 hlab hSl θ hMM
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end CFSG.StandardType
