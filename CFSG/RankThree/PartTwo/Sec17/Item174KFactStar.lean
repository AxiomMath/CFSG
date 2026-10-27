module

public import CFSG.RankThree.PartTwo.Sec17.Item174KFact26
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOne
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Aux
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG

@[expose] def StarFor (H : Type) [Group H] [Finite H] : Prop :=
  IsSimpleGroup H → ∀ t : H, orderOf t = 3 →
    ∀ I : Subgroup H, Subgroup.normalizer (Subgroup.zpowers t : Set H) ≤ I →
      ⁅CFSG.Open.pCoreOf 2 I, Subgroup.zpowers t⁆ ≠ ⊥ →
        ∃ n : ℕ, Odd n ∧ Nonempty (H ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 n))

@[expose] def StarL2 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 3 → d.1 = .A 1 q → Nonempty (H ≃* (TauCeti.CFSGIndex.lie d).Group) → StarFor H

@[expose] def StarL3Odd : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 2 → q.card % 3 = 2 → d.1 = .A 2 q →
      Nonempty (H ≃* (TauCeti.CFSGIndex.lie d).Group) → StarFor H

@[expose] def StarU3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.card % 3 = 1 → d.1 = .twistedA 2 q →
      Nonempty (H ≃* (TauCeti.CFSGIndex.lie d).Group) → StarFor H

@[expose] def StarJ1 : Prop :=
  ∀ (H : Type) [Group H] [Finite H],
    Nonempty (H ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) → StarFor H

@[expose] def StarA5 : Prop :=
  ∀ (H : Type) [Group H] [Finite H],
    Nonempty (H ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group) → StarFor H

theorem starFor_of_L3Even (H : Type) [Group H] [Finite H] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (h2 : q.p = 2) (hq : q.card % 3 = 2) (hd : d.1 = .A 2 q)
    (he : Nonempty (H ≃* (TauCeti.CFSGIndex.lie d).Group)) : StarFor H := by
  intro _ _ _ _ _ _
  obtain ⟨e⟩ := he
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at h2
  subst h2
  haveI : Fact (TauCeti.PrimePower.p ⟨2, f, hp, hf⟩).Prime := ⟨hp⟩
  have e' := e.trans (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 2 ⟨2, f, hp, hf⟩ hv)
  refine ⟨f, ?_, ⟨e'⟩⟩
  rw [TauCeti.PrimePower.card_def] at hq
  change 2 ^ f % 3 = 2 at hq
  rcases Nat.even_or_odd f with ⟨k, hk⟩ | ho
  · exfalso
    rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at hq
    norm_num at hq
  · exact ho

theorem kfactStar_of_families
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple) (hL2 : StarL2)
    (hL3 : StarL3Odd) (hU3 : StarU3) (hJ1 : StarJ1) (hA5 : StarA5) : KFactStar := by
  intro H _ _ hK hsimp hr t ht3 I hNI hO2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hsimp
  have hnab : ∃ a b : H, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    apply hO2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  obtain ⟨i, he⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hK
  have hr1 : CFSG.Open.pRank 3 (⊤ : Subgroup H) = 1 :=
    le_antisymm hr
      (CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.one_le_pRank_of_orderOf_eq_prime t ht3)
  have key : StarFor H := by
    rcases hS H hsimp hnab i he hr1 with
      ⟨d, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), he'⟩ | he' | he'
    · exact hL2 H d q hq hd he'
    · by_cases h2 : q.p = 2
      · exact starFor_of_L3Even H d q h2 hq hd he'
      · exact hL3 H d q h2 hq hd he'
    · exact hU3 H d q hq hd he'
    · exact hJ1 H he'
    · exact hA5 H he'
  exact key hsimp t ht3 I hNI hO2

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
