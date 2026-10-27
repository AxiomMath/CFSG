module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitL
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddL
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggCRN_lift_A_split {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hd : 24 ≤ lab.rank + 1) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  (largeEvenLabelAll_torusLift_typeA Nat.prime_three htag (by omega) h3).mono
    fun R _ I F h => ggTorusLift_mono Nat.prime_three h (by omega)

theorem ggCRN_lift_twA_nonsplit
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) (hd : 24 ≤ lab.rank + 1) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R := by
  refine (largeEvenLabelAll_torusLift_twA (p := 3) hlab htag Nat.prime_three h3).mono
    fun R _ I F h => ggTorusLift_mono Nat.prime_three h ?_
  simp only [ggUnitaryTorusRank]
  split <;> omega

private theorem crna_recipeUnitarySplitEven_lattice
    {d r n : ℕ} (hdr : d = 2 * r) (hn : 1 ≤ n) (hd : 24 ≤ d) (hpq : 3 ∣ 2 ^ n - 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusLift 3 9 R := by
  subst hdr
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact ggTorusLift_mono Nat.prime_three
    (ggTorusLift_unitarySplit_even hK hn (by omega) Nat.prime_three (by norm_num) hpq)
    (by omega)

private theorem crna_recipeUnitarySplitOdd_lattice
    {d r n : ℕ} (hdr : d = 2 * r + 1) (hn : 1 ≤ n) (hd : 24 ≤ d) (hpq : 3 ∣ 2 ^ n - 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusLift 3 9 R := by
  subst hdr
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact ggTorusLift_mono Nat.prime_three
    (ggTorusLift_unitarySplit_odd hK hn (by omega) Nat.prime_three (by norm_num) hpq)
    (by omega)

theorem ggCRN_lift_twA_split
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) (hd : 24 ≤ lab.rank + 1) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hd h3
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  have hn : 1 ≤ n := hlab.1
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' (l + 1)
  · exact crna_recipeUnitarySplitEven_lattice hr hn (by omega) h3 hQ
  · exact crna_recipeUnitarySplitOdd_lattice hr hn (by omega) h3 hQ

end CFSG.StandardType

end
