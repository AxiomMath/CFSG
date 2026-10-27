module

public import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate8080
public import Certificates.Certificate13604
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate830101
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6Pat
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG.Assembly



theorem ggPairConcl_of_selected_E8_plus
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (_hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (_hXns : ¬ GGSplitLie p X)
    (_hXnu : ¬ GGMemberUnitary p Bs X)
    (hE8 : GGInnerDiagOnLabel (fun p lab => lab.tag = .E8 ∧ p ∣ 2 ^ lab.n + 1) p Bs X)
    {r : MulAut ↥Bs} (_hr : r ∈ ggAutomizer X Bs) (_hrC : r ∈ ggCoxRefl M e)
    {r' : MulAut ↥Bs} (_hr' : r' ∈ ggAutomizer X Bs) (_hr'C : r' ∈ ggCoxRefl M e)
    (_hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  exfalso
  have hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X :=
    hX.imp_right (GGSecFiveWeakNbr.of_mem hcfg)
  have hrow : GGInnerDiagOnLabel ggRowP_EE8 p Bs X := hE8
  have hXn : X = L ∨ ∃ y, GGNbr p B x D J y X := hXw.imp_right fun hw => hw.1
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with rfl | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hw.2
  by_cases hA : GGIsWeylMatrixA M
  · obtain ⟨m, σ, -, hM⟩ := hA
    exact ggX_row_absurd_of_noReflFork ggLabelRigidInput_holds ggRowFork_EE8 hcfg hXn
      (ggX_noReflFork_typeA hcfg hpres hM hle3 hXA) hrow
  by_cases hD : NSJoin.NSTypeD M
  · exact ggX_row_absurd_of_noReflE6Pat ggLabelRigidInput_holds ggRowE6Pat_EE8 hcfg hXn
      (ggX_noReflE6Pat_typeD hcfg hpres hD hXA) hrow
  have hge : 696729600 ≤ Nat.card ↥(ggAutomizer X Bs) :=
    ggX_card_automizer_ge_of_EE8 ggLabelRigidInput_holds hcfg hXn hrow
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have hle : Nat.card ↥(ggAutomizer X Bs) ≤ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) :=
    Subgroup.card_le_of_le hXA
  rcases GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hA hD with hE6 | ⟨f, rfl⟩ | hE8M
  · have := card_ggAutomizerJoin_le_of_E6 e hE6
    omega
  · have hJ : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) ≤ 2903040 := by
      rw [← Nat.card_congr e.toEquiv]
      exact ((card_coxeterGroup_reindex _ f).trans card_coxeterE7_group).le
    omega
  · exact ggRouteCfg_false_of_card_join_le ggTBFixInput_holds ggTBFixNbrXInput_holds hcfg hXn hXA
      ((card_ggAutomizerJoin_le_of_weylE e (Or.inr (Or.inr hE8M))).trans hge)

end CFSG.StandardType

end
