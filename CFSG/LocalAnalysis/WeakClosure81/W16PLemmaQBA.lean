module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBAOdd
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBAIdx
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBASz
public import CFSG.RepresentationTheory.SzMartineau.MartineauInput

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

section Certified


theorem exists_mem_mul_inv_mem_centralizer_core (q : CfgLemmaQ M V₀ V h C) {τ : G} (hτ : τ ∈ V)
    (hτY : τ ∈ centralizer ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G))
    (hτX : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h) :
    ∃ y ∈ nVSub V₀ h ⊔ bSub V₀ h,
      ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  obtain ⟨s, hs, hsM, hsW, hbranch⟩ := q.prop24Setup.tim77_2_4_two
    CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
    CFSG.RepresentationTheory.SzMartineau.martineauSzInput_holds
  rcases hbranch with
    ⟨f, hf, hrel, F, hF, hFin, hchar, ψ, hcard, hψs, hψk, -⟩ | ⟨a, ha, hrel, ψ, hψr, hψk, hθ⟩ |
      ⟨m, hm, -, hrel, hN, ⟨e⟩⟩
  · exact q.exists_coboundary_of_odd_relIndex hτ hτY hτX
      (q.odd_relIndex_of_surjective_sl hf hrel ψ hcard hψs hψk)
  · exact q.exists_coboundary_of_sz hτ hτY hτX hs hsM (fun W hW => (hsW W hW).2.1) ha hrel ψ hψr
      hψk hθ
  · exact q.exists_coboundary_of_odd_relIndex hτ hτY hτX
      (q.odd_relIndex_of_dihedral hm hrel e)

end Certified

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
