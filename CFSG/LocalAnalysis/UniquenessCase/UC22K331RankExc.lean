module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Blueprint.Chevalley (Tag)
open CFSG.Blueprint (AdjointQuotient)
open CFSG.TauCetiBridge (fieldOf card_fieldOf)
open CFSG.TauCetiBridge.Even (UntwistedBridgeAll)
open CFSG.LieType.SeitzGeneration (Cat)

theorem k331Idx_untwisted {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeAll τ c)
    (hr : ∀ (K : Type) [Field K] [Finite K] (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* AdjointQuotient τ K) → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S))
    (q : PrimePower) (hv : (c q).Valid) : K331Idx (.lie ⟨c q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have hF := card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (fieldOf q 1) hF
  exact hr (fieldOf q 1) S ⟨e.trans φ.symm⟩

theorem k331Idx_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (hc : Nat.Coprime 3 (Nat.card (Cat ⟨.suzuki m, hv⟩))) : K331Idx (.lie ⟨.suzuki m, hv⟩) := by
  refine K331Idx.of_card (Or.inl fun h => ?_)
  have := hc.eq_one_of_dvd ((by norm_num : 3 ∣ 20160).trans h)
  omega

theorem k331Idx_tits (hv : LieTypeIndex.tits.Valid)
    (hc : Nat.card (Cat ⟨.tits, hv⟩) = 17971200) : K331Idx (.lie ⟨.tits, hv⟩) := by
  refine K331Idx.of_card (Or.inl ?_)
  change ¬ 20160 ∣ Nat.card (Cat ⟨.tits, hv⟩)
  rw [hc]
  decide

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
