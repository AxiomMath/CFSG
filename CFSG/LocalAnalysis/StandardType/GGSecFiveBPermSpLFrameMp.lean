module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameCore
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear Matrix

open scoped MatrixGroups

section Certs


theorem exists_ggSecFiveBPermSpLFrame (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOn Bs X)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {f : ℕ} (hf : 1 ≤ f) {ψ : SL(n, GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f)) (hrange : ψ.range = X)
    (r : ℕ) (π : Fin (r + 2) ≃ Fin n) :
    ∃ (σ : SL(r + 2, GaloisField 2 f) →* G) (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpLFrame Bs X eta π σ χ := by
  have hrn : r + 2 = n := by simpa using Fintype.card_congr π
  subst hrn
  obtain ⟨σ, χ, h1, h2, h3, h4⟩ := exists_lFrame_of_innerDiagOn hMp hp hp2 hBs hBsC hmark hC
    (m := r + 1) (by omega) eta hA hf hker hrange π
  exact ⟨σ, χ, h1, h2, h3, fun b u => h4 b u⟩

theorem ggSecFiveBPermSpLFrameInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermSpLFrameInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ hn eta _ hA _ _ f K i0 hcell r π
  have hcfg := hR.1.1
  obtain ⟨hf, -, ⟨ψ, hker, hrange⟩, -, -⟩ := hcell
  exact exists_ggSecFiveBPermSpLFrame hMp hcfg.tableB_facts.1 hcfg.1.2.2.2.2.2.1.2.1
    hcfg.2.1.2.1 hcfg.2.1.2.2.2 hR.1.2.2.1.1 hcfg.card_bstar_inf_centralizer_L.le hn eta hA
    (by omega) hker hrange r π

end Certs

end CFSG.StandardType

end
