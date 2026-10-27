module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrthNbr_pump
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) :
    GGWeylReflectionGroup 3 (ggAutomizer K Bs) ∧ ¬ GGWeylOfType 3 CoxeterMatrix.G₂ (ggAutomizer K Bs) ∧
      ggAutomizer J Bs ≤ ggAutomizer K Bs ∧ ggAutomizer J Bs ≤ ggAutomizer L Bs ∧ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J := by
  have hconf : GGConfig 3 B Bs x L D J := S.cfg.1.1
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hconf.1 hconf.2.2
  obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ
  have hJK : J ≤ K := le_of_ggNbr hL hconf.1 hconf.2.2 hpJ hnb
  obtain ⟨hW, hG2⟩ := hPump.2 G 3 B Bs x L D J 𝒦 S.cfg S.split y K hnb
  have hAutoK : ggAutomizer J Bs ≤ ggAutomizer K Bs := ggAutomizer_mono Bs hJK
  have hKinf : ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J := by
    rw [ggAInf]
    exact (le_iSup_of_le y (le_iSup_of_le K
      (le_iSup (fun _ : GGNbr 3 B x D J y K => ggAutomizer K Bs) hnb))).trans le_sup_right
  exact ⟨hW, hG2, hAutoK, ggAutomizer_mono Bs hJL, hKinf⟩

end CFSG.StandardType.OrthF3

end
