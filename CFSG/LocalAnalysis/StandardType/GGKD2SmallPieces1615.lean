module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

@[expose] def SetupFalse (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a → False

@[expose] def SmallA1TwD2 : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)) →
      LargeEvenLabelAll lab (fun R _ I _ => SetupFalse R I)

@[expose] def SmallDerivedSuzuki : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .B2der ∨ lab.tag = .twF4der ∨ lab.tag = .twB2) →
      LargeEvenLabelAll lab (fun R _ I _ => SetupFalse R I)

@[expose] def SmallG2Der : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .G2der →
    LargeEvenLabelAll lab (fun R _ I _ => SetupFalse R I)

theorem corner1584_small_labels_of_pieces (h1 : SmallA1TwD2) (h2 : SmallDerivedSuzuki)
    (h3 : SmallG2Der) : corner1584_small_labels := by
  intro lab hlab
  by_cases hsm : SmallLab lab
  · have key : ∀ {P : LargeEvenRawCont}, (∀ (R : Type) [Group R] (I F : Set (MulAut R)),
        P R I F → ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
            GGRankOneSetup I ψ 3 e J 3 a → SmallLab lab → False) →
        LargeEvenLabelAll lab P → LargeEvenLabelAll lab (fun R _ I _ =>
          ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
            ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
            ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
              GGRankOneSetup I ψ 3 e J 3 a → SmallLab lab → False) :=
      fun hP h => LargeEvenLabelAll.mono (fun R _ I F hI => hP R I F hI) h
    rcases hsm with hA | hD | hB | hG | hF | hS
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h1 lab hlab (Or.inl hA))
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h1 lab hlab (Or.inr hD))
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h2 lab hlab (Or.inl hB))
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h3 lab hlab hG)
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h2 lab hlab (Or.inr (Or.inl hF)))
    · exact key (fun R _ I _ hI L' _ _ ψ hs hk hc e J a hset _ => hI L' ψ hs hk hc e J a hset)
        (h2 lab hlab (Or.inr (Or.inr hS)))
  · exact fun Q hQ => largeEvenRawDatum_mono (fun R _ I F hq =>
      ⟨hq, fun L' _ _ ψ hs hk hc e J a hset hsm' => absurd hsm' hsm⟩) hQ

end CFSG.StandardType.KD2Pieces1615

end
