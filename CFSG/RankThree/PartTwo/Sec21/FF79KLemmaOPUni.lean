module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOUni
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOP
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPUniB

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Holt.Centralizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer)

theorem lemmaO_unitary_P {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)) (hq3 : q.p ≠ 3)
    {α : MulAut S} (hα : α ^ 3 = 1) (hout : ∀ c : S, α ≠ MulAut.conj c)
    {K : Subgroup S}
    (hK : CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α))
    (hA : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hB : ThreeRankLeOneInv S) : False := by
  obtain ⟨eA⟩ := hA
  obtain ⟨hZ, hL⟩ := center_bot_of_equiv_alt eA
  have hle := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.unitary_card_le_five r q hv
    hq3 he hα hK hL
  obtain ⟨e⟩ := he
  have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  obtain ⟨⟨hp, hf, hn3, hq⟩, -⟩ := id hM
  have hOut : 3 ∣ Nat.card (Outer S) := by
    by_contra hn
    obtain ⟨a, ha⟩ := autThreePowInner_of_not_three_dvd_outer hn (α : S ≃* S) 1 (fun x => by
        have h := congr_arg (fun β : MulAut S => β x) hα
        simpa [pow_succ, MulAut.mul_apply] using h)
    refine hout a ?_
    ext x
    simpa using ha x
  have hbound := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) hn3 hp hf hM).1
  have hdet : CFSG.RankThree.OuterOrder.determinantParameter .PSU (r + 1) (q.p ^ q.exponent) =
      Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := rfl
  rw [hdet] at hbound
  have h3dvd := hOut.trans hbound
  rw [TauCeti.PrimePower.card_def] at hle
  have hQ2 : 2 ≤ q.p ^ q.exponent :=
    le_trans hp.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hf2 : q.exponent ≤ 2 := by
    by_contra hc
    have : 2 ^ 3 ≤ q.p ^ q.exponent :=
      le_trans (Nat.pow_le_pow_left hp.two_le 3) (Nat.pow_le_pow_right hp.pos (by omega))
    omega
  have hg3 : 3 ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3dvd with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · omega
      · have := Nat.le_of_dvd q.exponent_pos h
        omega
    · exact h
  have hn_dvd : 3 ∣ r + 1 := hg3.trans (Nat.gcd_dvd_left _ _)
  have hq_dvd : 3 ∣ q.p ^ q.exponent + 1 := hg3.trans (Nat.gcd_dvd_right _ _)
  have hQ : q.p ^ q.exponent = 2 ∨ q.p ^ q.exponent = 5 := by omega
  by_cases hn6 : 6 ≤ r + 1
  · obtain ⟨t, u, v, ht, htu, htv, huv, hu, hv3, hnot⟩ :=
      exists_three_rank_two_psu hM (by omega) hQ
    exact hnot (hB t u v ht htu htv huv hu hv3)
  · have hn : r + 1 = 3 := by omega
    rcases hQ with hQ | hQ
    · exact hq (Prod.ext hn hQ)
    · have hq2 : q.p ≠ 2 := by
        intro hp2
        rw [hp2] at hQ
        have : 2 ∣ 5 := hQ ▸ dvd_pow_self 2 q.exponent_pos.ne'
        omega
      exact unitary_a5_false r q hv hq3 hq2 (by rw [hn]) ⟨e⟩ hα hK hZ hL

end CFSG.RankThree.PartTwo.Sec21.FF79
