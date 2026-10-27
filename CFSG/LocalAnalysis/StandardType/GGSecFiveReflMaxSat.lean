module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
public import CFSG.LocalAnalysis.StandardType.GGCellWitness

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRM_saturated
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRootGenL : GGSecFiveRootGenLInput) (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) (hxBs : x ∈ Bs) :
    ∀ a ∈ ggAInf p B Bs x L D J, GGIsReflection p a → a ⟨x, hxBs⟩ = ⟨x, hxBs⟩ →
      (∃ g ∈ ggAInf p B Bs x L D J, ∃ r ∈ ggAutomizer L Bs, GGIsReflection p r ∧ a = g * r * g⁻¹) →
        a ∈ ggAutomizer L Bs := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, -, -, -, -⟩ := hconf.tableB_facts
  have hAInf_le : ggAInf p B Bs x L D J ≤ ggAutomizer ⊤ Bs := by
    rw [ggAInf]
    refine sup_le (ggAutomizer_mono Bs le_top) ?_
    refine iSup_le fun y => iSup_le fun K => iSup_le fun _ =>
      ggAutomizer_mono Bs le_top
  have hInn : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  have hP3 : GGFixedRealizedInL p Bs L x :=
    ggFixedRealizedInL_of_config hL hP hconf hInn
  rintro a haAInf haRefl haFixx ⟨g, hgAInf, r, hrL, hrRefl, haeq⟩
  have hrR : GGRealized p Bs r :=
    hRootGenL G p B Bs x L D J 𝒦 hcfg hsplit r hrL hrRefl
  obtain ⟨g₀, -, hg₀N, hg₀eq⟩ :=
    eq_ggConjAut_of_mem_ggAutomizer (hAInf_le hgAInf)
  have haR : GGRealized p Bs a := by
    rw [haeq, hg₀eq]
    exact hrR.conj hp hg₀N
  have haInd : a ∈ ggInduced ⊤ Bs := haR.mem_ggInduced_top
  have haFix : x ∈ ggFixG Bs a :=
    Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, haFixx, rfl⟩
  exact hP3 a haRefl haInd haFix haR

end CFSG.StandardType

end
