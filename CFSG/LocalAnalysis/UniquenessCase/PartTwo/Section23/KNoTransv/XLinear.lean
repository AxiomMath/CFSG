module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.Vol2.Ch12Sec6P31LieH
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

private theorem ordA_one_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ordA 1 (2 ^ k) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
  have hgcd : Nat.gcd 2 (2 ^ k - 1) = 1 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd (Nat.gcd 2 (2 ^ k - 1))
      (Nat.gcd_dvd_left 2 (2 ^ k - 1)) with h | h
    · exact h
    · exfalso
      have h1 : 2 ∣ 2 ^ k - 1 := by
        have hg := Nat.gcd_dvd_right 2 (2 ^ k - 1)
        rwa [h] at hg
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have hpos : 0 < 2 ^ k := by positivity
      omega
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq, hgcd, Nat.div_one]

private theorem not_prime_ordA_one_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ¬ (ordA 1 (2 ^ k)).Prime := by
  rw [ordA_one_two_pow hk]
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : 3 ≤ (2 ^ k) ^ 2 - 1 := by
    have h4 : 4 ≤ (2 ^ k) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  have hgt : 2 < 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    calc 2 < 6 := by norm_num
      _ = 2 * 3 := by norm_num
      _ ≤ 2 ^ k * ((2 ^ k) ^ 2 - 1) := Nat.mul_le_mul h2 h3
  intro hp
  have hpow : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hdvd : 2 ∣ 2 ^ k * ((2 ^ k) ^ 2 - 1) := dvd_mul_of_dvd_left hpow _
  rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega

private theorem quotient_center_of_isSLn {X : Type} [Group X] {n k : ℕ} (hn : 3 ≤ n)
    (hX : IsSLn X n k) (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA (n - 1) (2 ^ k) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  have hmap : (Subgroup.center X).map e.toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
    (Subgroup.map_center_eq e).trans (CFSG.Quasithin.H13.S126P31.center_statedSL_eq n K)
  have hE : X ⧸ center X ≃* StatedProj (StatedSL n K) :=
    QuotientGroup.congr (Subgroup.center X) ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
      e hmap
  have hadm : StatedLieAdmissible .PSL n 2 k :=
    ⟨Nat.prime_two, by omega, by omega, fun h => by simp at h; omega,
      fun h => by simp at h; omega⟩
  have hSC : StatedClassicalModel (StatedProj (StatedSL n K)) .PSL n 2 k :=
    ⟨hadm, K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSL n K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSC
  refine ⟨?_, ?_⟩
  · haveI := hsimple
    exact hE.isSimpleGroup
  · rw [Nat.card_congr hE.toEquiv,
      (CFSG.Timmesfeld.card_statedClassicalModel_two hSC).1 rfl]

theorem quotient_center_of_isL2 {X : Type} [Group X] {k : ℕ} (hX : IsL2 X k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA 1 (2 ^ k) := by
  have hLM : CFSG.Blueprint.LieModel X .PSL 2 2 k := hX
  have hSC : StatedClassicalModel X .PSL 2 2 k :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLM (by decide)
  have hcard : Nat.card X = ordA 1 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hSC).1 rfl
  have hS : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSC
  have hk : 1 ≤ k := hLM.admissible.2.1
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
      by_contra hne
      exact h ⟨a, b, hne⟩
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).mp hS
    rw [hcard] at hprime
    exact not_prime_ordA_one_two_pow hk hprime
  haveI := hS
  exact quotient_center_simple_and_card (center_eq_bot_of_isSimpleGroup hnonab) hcard

theorem quotient_center_of_isSLn_three {X : Type} [Group X] {k : ℕ} (hX : IsSLn X 3 k)
    (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA 2 (2 ^ k) :=
  quotient_center_of_isSLn (by norm_num) hX hk

theorem quotient_center_of_isSLn_four {X : Type} [Group X] {k : ℕ} (hX : IsSLn X 4 k)
    (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordA 3 (2 ^ k) :=
  quotient_center_of_isSLn (by norm_num) hX hk

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
