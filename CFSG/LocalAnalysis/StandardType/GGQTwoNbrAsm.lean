module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRec
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG1
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG2
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG3
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG4
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

theorem qTwo_gen2
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hG : QTwoJoinGuard 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hEn : GGSecFiveNSEnnolaInput)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hTCJ : GGTCJKnown) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
      K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
            n ∈ Subgroup.normalizer (Bs : Set G) ∧
              ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom := by
  intro y K' hnbr hA
  obtain ⟨hM⟩ := qTwoNbr_recognition hG hm hL hEn hFrameL hFm hLB hPJ hTCJ hnbr hA
  exact qTwoNbr_gen hM (qTwoNbr_comp_transport hM) (qTwoNbr_fourBlock hM)
    (qTwoNbr_normalTransport hG.1.1.1.2.1 hM)

end CFSG.StandardType.QTwo

end
