module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFrame
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRM_witness_zero_realized
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hFix : GGSecFiveFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    (hxBs : x ∈ Bs) (hfix : ∀ φ ∈ ggAInf p B Bs x L D J, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩)
    (hreal : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ∀ t ∈ ggAutomizer K Bs,
      GGIsReflection p t → GGRealized p Bs t) :
    GGSecFiveInfWitness p B Bs x L D J := by
  have hP3 : GGFixedRealizedInL p Bs L x :=
    ggFixedRealizedInL_of_config hL hP hcfg.1.1 hcfg.1.2.2.1.1
  have hle : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    intro y K hnbr
    rw [hcfg.2.1 y K hnbr]
    refine (Subgroup.closure_le (K := ggAutomizer L Bs)).mpr ?_
    rintro t ⟨htK, htr⟩
    have htA : t ∈ ggAInf p B Bs x L D J := by
      rw [ggAInf]
      refine Subgroup.mem_sup_right ?_
      exact Subgroup.mem_iSup_of_mem (S := fun y : G =>
          ⨆ (K : Subgroup G) (_ : GGNbr p B x D J y K), ggAutomizer K Bs) y
        (Subgroup.mem_iSup_of_mem (S := fun K : Subgroup G =>
            ⨆ (_ : GGNbr p B x D J y K), ggAutomizer K Bs) K
          (Subgroup.mem_iSup_of_mem (S := fun _ : GGNbr p B x D J y K =>
              ggAutomizer K Bs) hnbr htK))
    have htx : t ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := hfix t htA
    have htxE : x ∈ ggFixG Bs t := Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, htx, rfl⟩
    have htR : GGRealized p Bs t := hreal y K hnbr t htK htr
    exact hP3 t htr htR.mem_ggInduced_top htxE htR
  have hAeq : ggAInf p B Bs x L D J = ggAutomizer L Bs := by
    rw [ggAInf]
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    exact iSup_le fun y => iSup_le fun K => iSup_le fun hnbr => hle y K hnbr
  have hweylL : GGWeylReflectionGroup p (ggAutomizer L Bs) := by
    obtain ⟨ιL, -, ML, hADE, hW, -, -⟩ := ggRM_frame_L hFix hcfg hsplit
    rcases hADE with hAD | hE
    · exact ⟨ιL, ML, hAD.isWeylMatrix, hW⟩
    · exact ⟨ιL, ML, hE.isWeylMatrix, hW⟩
  refine ⟨?_, ⟨∅, ?_, ?_⟩⟩
  · rw [hAeq]; exact hweylL
  · constructor
    · simp
    · intro K hK; simp at hK
  · rw [hAeq, ggAutomizerJoin]
    simp

end CFSG.StandardType

end
