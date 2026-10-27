module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAutomizer
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2_ajOfSetting {G : Type} [Group G] [Finite G] (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) : ggAutomizer J Bs ≠ ⊥ := by
  obtain ⟨hcfg, -, hIDAll, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBstar.1 hStdSub.1 hBsL
  exact ggQ2_automizer_ne_bot hBsabel hBsJ hJJ hpJ
    (fun j hj hjC hjp => h5 G p B Bs x L D J hS j hj hjC hjp)

end CFSG.StandardType

end
