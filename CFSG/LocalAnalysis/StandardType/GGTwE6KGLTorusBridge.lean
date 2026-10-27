module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem labelAll_torusLift_five {lab : LargeEvenLabel} {r : ℕ} (hr : 5 ≤ r)
    (h : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 r R) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, ggTorusLift_mono Nat.prime_three hq.2 hr⟩)
    (h Q hQ)

theorem largeEvenLabelAll_torusLift_twA_threeFive
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twA) (h3 : 3 ∣ 2 ^ lab.n + 1)
    (h7 : 7 ≤ lab.rank + 1) : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
  labelAll_torusLift_five (by unfold ggUnitaryTorusRank; split_ifs <;> omega)
    (largeEvenLabelAll_torusLift_twA hlab htag Nat.prime_three h3)

theorem largeEvenLabelAll_torusLift_typeA_threeFive {lab : LargeEvenLabel} (htag : lab.tag = .A)
    (h3 : 3 ∣ 2 ^ lab.n - 1) (h7 : 7 ≤ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
  labelAll_torusLift_five (by omega)
    (largeEvenLabelAll_torusLift_typeA Nat.prime_three htag (by omega) h3)

section Exceptional


theorem largeEvenLabelAll_torusLift_excPlus_threeFive
    {lab : LargeEvenLabel} (htag : lab.tag = .E7 ∨ lab.tag = .E8) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
  labelAll_torusLift_five (by rcases htag with h | h <;> rw [h] <;> decide)
    (largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by norm_num)
      ⟨htag.imp_right Or.inl, h3⟩)

theorem largeEvenLabelAll_torusLift_excMinus_threeFive {lab : LargeEvenLabel}
    (htag : lab.tag = .E7 ∨ lab.tag = .E8) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3
  rcases htag with rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_mono Nat.prime_three
      (TableBExc.ggTorusLift_E7 Nat.prime_three (by norm_num) hpq) (by norm_num)⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_mono Nat.prime_three
      (TableBExc.ggTorusLift_E8 Nat.prime_three (by norm_num) hpq) (by norm_num)⟩

end Exceptional

end CFSG.StandardType.SCFourCover

end
