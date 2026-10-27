module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusOrthMinus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusTypeAPlus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusSymplectic
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusOrthPlus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLSide35At_of_torusLift {lab : LargeEvenLabel}
    (h : LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R)
    (L : Type) [Group L] [Finite L]
    (hL : LargeEvenMarkingLegacy L (fun lab' _ _ _ _ _ => lab' = lab ∧ LargeEvenSplit 3 lab')) :
    ∃ E U : Subgroup L, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ IsPGroup 2 U ∧
      U ≠ ⊥ ∧ E ≤ Subgroup.normalizer (U : Set L) := by
  obtain ⟨hcomm, lab', hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, θ, rfl, hs⟩ := largeEvenRawDatum_exists
    ((largeEvenRawDatum_legacy _ _).2 hraw)
  obtain ⟨R', _, I', F', ⟨-, -, θ', -⟩, hlift⟩ := largeEvenRawDatum_exists
    (h hlab hs _ ((largeEvenRawDatum_legacy _ _).2 hraw))
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, -⟩ := hlift L
    (θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (θ'.surjective.comp (QuotientGroup.mk'_surjective _)) (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      exact (QuotientGroup.eq_one_iff x).1 ((MulEquiv.map_eq_one_iff θ').1 hx)) hcomm
  exact ⟨E, U, hE, hcard, hU2, hU, hEU⟩


private theorem ggNbrLSide_three_dvd_pow_sub {n : ℕ} (h : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := h
  have h4 : 2 ^ (m + m) = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
  rw [h4]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

private theorem ggNbrLSide_three_dvd_pow_add {n : ℕ} (h : Odd n) : 3 ∣ 2 ^ n + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow 2 1 h

private theorem ggNbrLSide_not_even_of_dvd_pow_add {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : ¬ Even n := by
  intro he
  have h1 := ggNbrLSide_three_dvd_pow_sub he
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem ggNbrLSide_torusLift_five_of_le {lab : LargeEvenLabel} {r : ℕ} (hr : 5 ≤ r)
    (h : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 r R) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, ggTorusLift_mono Nat.prime_three hq.2 hr⟩)
    (h Q hQ)

open SCFourCover

theorem ggNbrLSide35At_A (rank n : ℕ) : GGNbrLSide35At ⟨.A, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, h6⟩ | ⟨ho, h12⟩
  · exact largeEvenLabelAll_torusLift_typeA_threeFive rfl (ggNbrLSide_three_dvd_pow_sub he)
      (by show 7 ≤ rank + 1; omega)
  · exact largeEvenLabelAll_torusLift_typeAPlus_threeFive rfl (ggNbrLSide_three_dvd_pow_add ho)
      (by show 10 ≤ rank + 1; omega)

theorem ggNbrLSide35At_twA
    (rank n : ℕ) : GGNbrLSide35At ⟨.twA, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun hlab hs => ?_) L hL
  have h3 : 3 ∣ 2 ^ n + 1 := by
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | rfl
    · exact h
    · norm_num
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact absurd he (ggNbrLSide_not_even_of_dvd_pow_add h3)
  · exact largeEvenLabelAll_torusLift_twA_threeFive hlab rfl h3 (by show 7 ≤ rank + 1; omega)

theorem ggNbrLSide35At_B (rank n : ℕ) : GGNbrLSide35At ⟨.B, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  exact largeEvenLabelAll_torusLift_symplectic_threeFive (Or.inl rfl)
    (by rcases hrank with ⟨-, h⟩ | ⟨-, h⟩ <;> show 6 ≤ rank <;> omega)

theorem ggNbrLSide35At_C (rank n : ℕ) : GGNbrLSide35At ⟨.C, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  exact largeEvenLabelAll_torusLift_symplectic_threeFive (Or.inr rfl)
    (by rcases hrank with ⟨-, h⟩ | ⟨-, h⟩ <;> show 6 ≤ rank <;> omega)

theorem ggNbrLSide35At_D
    (rank n : ℕ) : GGNbrLSide35At ⟨.D, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun hlab _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, h6⟩ | ⟨ho, h12⟩
  · exact ggNbrLSide_torusLift_five_of_le (r := rank) (by omega)
      (largeEvenLabelAll_torusLift_D rfl hlab (by show 4 ≤ rank; omega) Nat.prime_three
        (ggNbrLSide_three_dvd_pow_sub he))
  · exact largeEvenLabelAll_torusLift_orthPlus_threeFive rfl (ggNbrLSide_three_dvd_pow_add ho)
      (by show 6 ≤ rank; omega)

theorem ggNbrLSide35At_twD
    (rank n : ℕ) : GGNbrLSide35At ⟨.twD, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun hlab _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, h6⟩ | ⟨ho, h12⟩
  · exact ggNbrLSide_torusLift_five_of_le (r := rank - 1) (by omega)
      (largeEvenLabelAll_torusLift_twD rfl hlab (by show 4 ≤ rank; omega) Nat.prime_three
        (ggNbrLSide_three_dvd_pow_sub he))
  · exact largeEvenLabelAll_torusLift_orthMinus_threeFive rfl (ggNbrLSide_three_dvd_pow_add ho)
      (by show 6 ≤ rank; omega)

theorem ggNbrLSide35At_E6
    (rank n : ℕ) : GGNbrLSide35At ⟨.E6, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact largeEvenLabelAll_torusLift_E6_three rfl (ggNbrLSide_three_dvd_pow_sub he)
  · omega

theorem ggNbrLSide35At_E7
    (rank n : ℕ) : GGNbrLSide35At ⟨.E7, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inl rfl)
      (ggNbrLSide_three_dvd_pow_sub he)
  · omega

theorem ggNbrLSide35At_E8
    (rank n : ℕ) : GGNbrLSide35At ⟨.E8, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ _ => ?_) L hL
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inr rfl)
      (ggNbrLSide_three_dvd_pow_sub he)
  · omega

theorem ggNbrLSide35At_twE6 (rank n : ℕ) : GGNbrLSide35At ⟨.twE6, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun _ hs => ?_) L hL
  have h3 : 3 ∣ 2 ^ n + 1 := by
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | rfl
    · exact h
    · norm_num
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact absurd he (ggNbrLSide_not_even_of_dvd_pow_add h3)
  · omega

theorem ggNbrLSide35At_of_rank_lt {lab : LargeEvenLabel} (h : ggNbrLSideRank lab < 6) :
    GGNbrLSide35At lab := by
  intro hrank
  unfold GGNbrLSideLargeRank at hrank
  rcases hrank with ⟨-, h6⟩ | ⟨-, h12⟩ <;> omega

theorem ggNbrLSide35_holds
    : GGNbrLSide35 := by
  intro lab
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case A => exact ggNbrLSide35At_A rank n
  case twA => exact ggNbrLSide35At_twA rank n
  case B => exact ggNbrLSide35At_B rank n
  case C => exact ggNbrLSide35At_C rank n
  case D => exact ggNbrLSide35At_D rank n
  case twD => exact ggNbrLSide35At_twD rank n
  case E6 => exact ggNbrLSide35At_E6 rank n
  case E7 => exact ggNbrLSide35At_E7 rank n
  case E8 => exact ggNbrLSide35At_E8 rank n
  case twE6 => exact ggNbrLSide35At_twE6 rank n
  all_goals exact ggNbrLSide35At_of_rank_lt (by simp [ggNbrLSideRank])

end CFSG.StandardType

end
