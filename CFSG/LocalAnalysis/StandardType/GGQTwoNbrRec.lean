module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrA
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabel
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbr_recognition
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (hG : QTwoJoinGuard 3 B Bs x L D J 𝒦) (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hEn : GGSecFiveNSEnnolaInput)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hTCJ : GGTCJKnown) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    Nonempty (QTwoNbrModel 3 B Bs x L D J y K) := by
  have hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hG.1
  obtain ⟨t, ht4, -, hpJ, hJ⟩ := qTwoNbr_stdComp hcfg hm hL hFrameL hFm
  have hJK : J ≤ K := qTwoNbr_le hcfg hLB hPJ hpJ hnbr
  have hcomp := qTwoNbr_component hcfg hnbr hJK
  obtain ⟨-, hmark, d, hd, hKd⟩ := qTwoNbr_label hG hEn hTCJ hnbr hA hJK ht4 hJ
  exact qTwoNbrRec_core hcfg.1.1 hLB hPJ hnbr hJK hcomp hd hmark hKd

end CFSG.StandardType.QTwo

end
