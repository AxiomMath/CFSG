module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom
public import CFSG.LocalAnalysis.StandardType.GGHLAutomizerK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggHL58Nbr_of_inputs_from {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hRig : GGLabelRigidInput)
    (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀) (hW : GGTBWNormLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (h : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs K) : GGTWHLAt p Bs K y := by
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyB : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  obtain ⟨lab, hlabΛ, hlab, hP, hdat⟩ :=
    ggResXDatumA_compat_from_K hr₀ hRig hT hLift hW hH h hyB
  obtain ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, hv, α, e, hMeq, hMw, hMC, hlin, hrefl, hpair,
    hIso, hgen, S, hN, hWn, hMi, ψ, hcompat, hA⟩ := hdat
  refine ⟨hyB, ?_⟩
  intro Λ₂ iF₂ iD₂ M₂ C₂ hMw₂ hMC₂ V₂ iV₂add iV₂mod ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂
    t ht htr hty
  exact ggHL_lines_of_automizer_K hWn hH hCent hMi hN hyB φ ψ hcompat hA hgen hMw₂ hMC₂
    ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂ t ht htr hty

end CFSG.StandardType

end
