module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePClauses
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGTAPBig (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 4 ≤ lab.rank) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank) ∨
    (lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 5 ≤ lab.rank) ∨
    lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4

private theorem ta2_labelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.1, hPP' R I F hq.2⟩) (h Q hQ)

private theorem ta2_seven_dvd {lab : LargeEvenLabel} (hn : lab.n = 3) : 7 ∣ 2 ^ lab.n - 1 := by
  rw [hn]
  norm_num

private theorem ta2_typeA_five {lab : LargeEvenLabel} (hn : lab.n = 3)
    (htag : lab.tag = .A) (hr : 5 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R :=
  ta2_labelAll_mono (fun R _ I F hlift => ggTorusLift_mono (by norm_num) hlift (by omega))
    (largeEvenLabelAll_torusLift_typeA (p := 7) (by norm_num) htag (by omega)
      (ta2_seven_dvd hn))

private theorem ta2_typeA_four {lab : LargeEvenLabel} (hn : lab.n = 3)
    (htag : lab.tag = .A) (hr : lab.rank = 4) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hr hn ⊢
  subst htag
  subst hr
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : 7 ∣ Nat.card K - 1 := by rw [hK, hn]; norm_num
  refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
  exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 5 K)
    (TypeA.ggTorusLift_coprime (p := 7) (by norm_num) hpK (by norm_num) (by norm_num)
      (TypeA.slHasSections_of_five_le (K := K) (by norm_num)))

private theorem ta2_typeBC {lab : LargeEvenLabel} (hn : lab.n = 3)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hr : 4 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hr hn ⊢
  have hpn : 7 ∣ 2 ^ n - 1 := by rw [hn]; norm_num
  rcases htag with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ', hlift⟩ :=
      TableBSymp.recipeSymplectic_torusLift (p := 7) (l := l) (n := n)
        (by norm_num) (by norm_num) hpn (by omega) hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono (by norm_num) hlift (by omega)⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ', hlift⟩ :=
      TableBSymp.recipeSymplectic_torusLift (p := 7) (l := l) (n := n)
        (by norm_num) (by norm_num) hpn (by omega) hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono (by norm_num) hlift (by omega)⟩

private theorem ta2_typeD {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hn : lab.n = 3) (htag : lab.tag = .D) (hr : 4 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R :=
  ta2_labelAll_mono (fun R _ I F hlift => ggTorusLift_mono (by norm_num) hlift hr)
    (largeEvenLabelAll_torusLift_D htag hlab hr (p := 7) (by norm_num) (ta2_seven_dvd hn))

private theorem ta2_type_twD {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hn : lab.n = 3) (htag : lab.tag = .twD) (hr : 5 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R :=
  ta2_labelAll_mono (fun R _ I F hlift => ggTorusLift_mono (by norm_num) hlift (by omega))
    (largeEvenLabelAll_torusLift_twD htag hlab (by omega) (p := 7) (by norm_num)
      (ta2_seven_dvd hn))

private theorem ta2_exc
    {lab : LargeEvenLabel} (hn : lab.n = 3)
    (htag : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn ⊢
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 7 ∣ Nat.card K - 1 := by rw [hK, hn]; norm_num
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono (by norm_num)
        (TableBExc.ggTorusLift_E6 (by norm_num) (by norm_num) (by norm_num) hpq) (by norm_num)⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 7 ∣ Nat.card K - 1 := by rw [hK, hn]; norm_num
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono (by norm_num)
        (TableBExc.ggTorusLift_E7 (by norm_num) (by norm_num) hpq) (by norm_num)⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 7 ∣ Nat.card K - 1 := by rw [hK, hn]; norm_num
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_mono (by norm_num)
        (TableBExc.ggTorusLift_E8 (by norm_num) (by norm_num) hpq) (by norm_num)⟩

private theorem ta2_F4
    {lab : LargeEvenLabel} (hn : lab.n = 3) (htag : lab.tag = .F4) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 7 ∣ Nat.card K - 1 := by rw [hK, hn]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusLift_mono (by norm_num)
      (TableBF4.ggTorusLift_F4 (by norm_num) (by norm_num) hpq) (by norm_num)⟩

theorem largeEvenLabelAll_torusLift_seven_four
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 3) (h : GGTAPBig lab) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 7 4 R := by
  rcases h with ⟨hA, hrA⟩ | ⟨hBC, hrBC⟩ | ⟨hD, hrD⟩ | ⟨htwD, hrtwD⟩ | hE6 | hE7 | hE8 | hF4
  · rcases lt_or_eq_of_le hrA with h5 | h4
    · exact ta2_typeA_five hn hA (by omega)
    · exact ta2_typeA_four hn hA (by omega)
  · exact ta2_typeBC hn hBC hrBC
  · exact ta2_typeD hlab hn hD hrD
  · exact ta2_type_twD hlab hn htwD hrtwD
  · exact ta2_exc hn (Or.inl hE6)
  · exact ta2_exc hn (Or.inr (Or.inl hE7))
  · exact ta2_exc hn (Or.inr (Or.inr hE8))
  · exact ta2_F4 hn hF4

end CFSG.StandardType

end
