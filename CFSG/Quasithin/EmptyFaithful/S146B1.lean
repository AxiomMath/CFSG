module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.EmptyFaithful.S146T11
public import CFSG.Quasithin.EmptyFaithful.S146G1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stage146BranchBCore_of_parts (h19 : Stage14619) (h20 : Stage14620) (h21 : Stage14621)
    (h22 : Stage14622) (h23 : Stage14623) (hD4 : Stage146D4) (h24 : Stage14624)
    (hF1 : Stage146FRank) (hF2 : Stage146FH2) (hF3 : Stage146FFour) : Stage146BranchBCore := by
  intro G _ _ T M S hB
  have hB' : HypB146 T M := hB
  have c19 := h19 G T M S hB'
  have c20 := h20 G T M S hB' c19
  have hG1 : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hnsolv : ¬ Group.IsSolvable ↥(mcOf T) := fun hs => hG1.2 (S.theorem_14_6_18 hB' hG1.1 hs)
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable (H := mcOf T) (X := mcOf T) le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hnsolv
  have c21 : ∀ K' ∈ cComp (mcOf T), Conc14621 T K' := h21 G T M S hB' c19 c20
  have c22 : ∀ K' ∈ cComp (mcOf T), Conc14622 T M K' := fun K' hK' =>
    h22 G T M S hB' c19 c20 K' hK' (c21 K' hK')
  have c23 : Conc14623 T M :=
    h23 G T M S hB' c19 c20 fun K' hK' => ⟨c21 K' hK', c22 K' hK'⟩
  obtain ⟨⟨U₁, U₂, s, hdec⟩, -⟩ := c22 K hK
  obtain ⟨u, hu⟩ := hD4 G T M S hB' K hK (c21 K hK) (c22 K hK) c23 U₁ U₂ s hdec
  have c24 : Conc14624 T M K u :=
    h24 G T M S hB' c19 c20 c23 K hK (c21 K hK) (c22 K hK) U₁ U₂ s hdec u hu
  have hdata : BData146 T M K U₁ U₂ s u :=
    ⟨hK, c19, c20, c21 K hK, c22 K hK, c23, hdec, hu, c24⟩
  obtain ⟨hr1, hr2⟩ := hF1 G T M S hB' K U₁ U₂ s u hdata
  obtain ⟨hS3, hnM⟩ := hF2 G T M S hB' K U₁ U₂ s u hdata
  have hfour := hF3 G T M S hB' K U₁ U₂ s u hdata
  exact ⟨mcOf T, u, centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (Subgroup.zpowers u),
    hG1, c24.1, c24.2.2.2, hr1, hr2, centralizerMod_mono_left _ hG1.1.1, le_rfl, hS3, hnM, hfour⟩

end CFSG.Quasithin
