module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShape
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo


theorem ggQTwoD_B_lt_Bs_of_not_three_dvd (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m) (hm3 : ¬ 3 ∣ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') : B < Bs := by
  by_cases hL : qtwoOrthL G L 𝒦
  · obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hL
    obtain ⟨-, -, -, -, -, hlt⟩ :=
      qtwoOrthFrameCore_of_cfg hcfg (qtwo_label_le_three e' hM) hΛ hhas hn htag
    exact hlt
  · obtain ⟨F0, _, _, _, ψ, ε, hbase⟩ :=
      ggQTwoDUnit_base_of_ne_six ggLabelRigidInput_holds hTBF hWI hcfg e' hm (by omega) hM hL
    exact ggQTwoDUnit_B_lt_Bs hcfg.1 hm hm3 hbase

theorem ggQTwoDL1InvFixInputOn_of_not_three_dvd {R : ℕ → Prop}
    (hR : ∀ m, R m → 5 ≤ m ∧ ¬ 3 ∣ m) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDL1InvFixInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hB
  exact absurd hB
    (ggQTwoD_B_lt_Bs_of_not_three_dvd hTBF hWI hcfg e' (hR m hm).1 (hR m hm).2 hM).ne

theorem ggQTwoL1InputOn_of_not_three_dvd {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m ∧ ¬ 3 ∣ m)
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoL1InputOn R :=
  ggQTwoL1Input_of_invFix ggLNoncyclicInput_holds hL hP
    (ggQTwoDL1InvFixInputOn_of_not_three_dvd hR hTBF hWI)

theorem ggQTwoL1InputOn_five (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGQTwoL1InputOn fun m => m = 5 :=
  ggQTwoL1InputOn_of_not_three_dvd (fun _ hm => ⟨by omega, by omega⟩) hL hP hTBF hWI

end CFSG.StandardType.QTwo

end
