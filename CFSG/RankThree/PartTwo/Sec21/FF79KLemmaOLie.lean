module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

import CFSG.Adapters.LinearCatalogStated
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LOrder60

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.Open
open CFSG.RankThree.PartTwo.Sec4.Ronan148L
open CFSG.HardMathSupport.Solomon.Coordinator
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

theorem prime_pow_eq_prime_pow {p e a b : ℕ} (hp : p.Prime) (ha : a.Prime) (he : 0 < e)
    (h : p ^ e = a ^ b) : p = a ∧ e = b := by
  have hpa : p ∣ a ^ b := h ▸ dvd_pow_self p he.ne'
  have hpa' : p = a := (Nat.prime_dvd_prime_iff_eq hp ha).1 (hp.dvd_of_dvd_pow hpa)
  subst hpa'
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

theorem autFix_eq_eqLocus {X : Type} [Group X] (x : MulAut X) :
    Sec4.autFix x = x.toMonoidHom.eqLocus (MonoidHom.id X) := by
  ext y
  rfl

theorem isLnq_top_of_typeA {L : Type} [Group L] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : L ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    {a b : ℕ} (ha : q.p = a) (hb : q.exponent = b) : IsLnq (r + 1) a b (⊤ : Subgroup L) := by
  have h := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (Subgroup.topEquiv (G := L)).symm
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
  rw [ha, hb] at h
  exact h

end CFSG.RankThree.PartTwo.Sec21.FF79
