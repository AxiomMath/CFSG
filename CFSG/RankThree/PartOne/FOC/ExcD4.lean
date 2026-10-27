module

public import CFSG.RankThree.PartOne.FOCD.ExcFinite
public import CFSG.RankThree.PartOne.FOC.SylowInner
public import CFSG.RankThree.PartOne.FOC.ExcD4Split
public import CFSG.RankThree.PartOne.FOC.ExcD4Sylow
public import CFSG.RankThree.PartOne.FOC.ExcD4Outer
public import CFSG.RankThree.PartOne.KF.ClsExcD4
public import CFSG.RankThree.PartOne.CTP.SeitzFineD4

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD
open TauCeti (PrimePower)


section D4


theorem innerCompN_trialityD4 {T : Type} [Group T] [Finite T] [IsSimpleGroup T] {f p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hch : ChevalleyExceptionalModel T .trialityD4 2 f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (e : T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : InnerCompN p T := by
  obtain ⟨hab, hA⟩ := sylowData_D4 hch K hK σ hσ e hp hp5
  refine innerCompN_of_sylow hp hab hA ?_
  by_cases hpq : p ∣ 2 ^ f - 1
  · right
    intro b hb1 hbp E hE
    have hb1' : e b ≠ 1 := fun h => hb1 (e.injective (h.trans (map_one e).symm))
    have hbp' : (e b) ^ p = 1 := by rw [← map_pow, hbp, map_one]
    exact compDvdAt_of_mulEquiv e (compDvdAt_D4_split Nat.prime_two hch.1.2.1 K hK σ hσ hp
      (by omega) hpq (e b) hb1' hbp') E hE
  · left
    exact kf123ExcD4NoRankTwo T f hch p hp hp5 hpq

end D4

section Index


theorem fieldInnerIdx_trialityD4 (q : PrimePower) (hq2 : q.p = 2) :
    FieldInnerIdx (.trialityD4 q) := by
  intro T _ _ p hp hp5 hs hnab hiso
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := CTP.exists_trialityD4_model hq2 hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hm' : TwistedChevalleyModel T .D4 (q.p ^ q.exponent) :=
    CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq2 (by decide) e0
  rw [hq2] at hm'
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hch : ChevalleyExceptionalModel T .trialityD4 2 q.exponent := ⟨⟨Nat.prime_two, hf, rfl⟩, hm'⟩
  exact fieldInnerT_of_compN (center_eq_bot_of_nonab hs hnab)
    (innerCompN_trialityD4 hp hp5 hch X hX σ hσ e)
    (OuterComp.of_mulEquiv e hp (outerComp_D4 hp hp5 hf X hX σ hσ))

end Index

end CFSG.RankThree.PartOne.FOC
