module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthExclOfCited
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFamily
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxSat
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRM_witness_main
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hFix : GGSecFiveFixInput) (hRootGenL : GGSecFiveRootGenLInput)
    (hLev2 : GGSecFiveLevTwoInput') (hWeyl : GGSecFiveWeylBranchInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    GGSecFiveInfWitness p B Bs x L D J := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs_ea, hxBs, hLx, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hW : GGWeylReflectionGroup p (ggAInf p B Bs x L D J) :=
    hWeyl G p B Bs x L D J 𝒦 hcfg hsplit hC
  refine ⟨hW, ?_⟩
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  obtain ⟨ιL, instL, ML, hML, hWeylL, hcardBs, -⟩ := ggRM_frame_L hFix hcfg hsplit
  obtain ⟨𝒮', h𝒮'sub, hcard', heq⟩ :=
    hLev2 G p Bs hp hp2 hBs_ea hNT (ggAInf p B Bs x L D J) (ggRM_ainf_le_induced)
      ι M hM (ggRM_not_G2 hML hWeylL le_sup_left f) f hf
      ⟨x, hxBs⟩ (ggAutomizer L Bs) ιL ML le_sup_left (ggRM_AL_fixes_x hcfg hxBs)
      hML hWeylL hcardBs (ggRM_saturated hL hP hRootGenL hcfg hsplit hxBs)
      (GGSecFiveNbrAutFamily p B Bs x D J) (by
        intro K hK
        obtain ⟨y, K₀, hNK, rfl⟩ := hK
        refine ⟨?_, ?_⟩
        · exact (le_iSup_of_le y (le_iSup_of_le K₀ (le_iSup_of_le hNK
            (le_rfl : ggAutomizer K₀ Bs ≤ ggAutomizer K₀ Bs)))).trans le_sup_right
        · exact hcfg.2.1 y K₀ hNK)
  obtain ⟨𝒦', h𝒦', hjoin'⟩ := ggRM_nbrs_of_family 𝒮' h𝒮'sub hcard'
  refine ⟨𝒦', h𝒦', ?_⟩
  calc ggAutomizerJoin L Bs 𝒦'
      = ggAutomizer L Bs ⊔ ⨆ S ∈ 𝒮', S := hjoin'
    _ = ggAutomizer L Bs ⊔ ⨆ S ∈ GGSecFiveNbrAutFamily p B Bs x D J, S := heq.symm
    _ = ggAInf p B Bs x L D J := ggRM_ainf_eq_sup.symm

end CFSG.StandardType

end
