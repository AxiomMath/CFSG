module

public import CFSG.RankThree.CentralLift.ClassicalExactScalarCover
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin
open CFSG.Assembly.RankThreeEven (localRank)

variable {p ℓ f n : ℕ} {L : Type} [Group L] [Finite L]

theorem unitary_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hℓodd : Odd ℓ) (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f) :
    Subgroup.center L = ⊥ := by
  by_cases hcase : p = ℓ ∨ n = 3
  · exact unitary_small_local_rank_prime_center_trivial_of_defining_or_three hp hp3 hL hZ hloc
      hℓodd hcase hM
  rw [not_or] at hcase
  obtain ⟨hpℓ, -⟩ := hcase
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have hn3 : 3 ≤ n := hn
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := unitary_exact_scalar_cover hp hp3 hℓ hℓodd hf hK hn3
    (Or.inl hpℓ) (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have hpg : p ∣ Nat.gcd n (ℓ ^ f + 1) := (hdvd.trans hcard).trans hD
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
  have hn5 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have h5 : 5 ≤ p := CFSG.RankThree.Classical.five_le_of_prime hp hp3
  have := sub_two_le_localRank_of_unitary hp hp3 hℓ hℓodd hf hK hn3 hpn hpq e
  omega

theorem omegaOdd_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hℓodd : Odd ℓ) (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaOdd n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have hn3 : 3 ≤ n := hn
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have := four_mul_le_localRank_of_omegaOdd hp hp3 hf hK hn3 e
    omega
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := omegaOdd_exact_scalar_cover hp hp3 hℓ hℓodd hpℓ hf hK
    hn3 (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have h1 := Nat.le_of_dvd Nat.card_pos (hdvd.trans hcard)
  omega

theorem omegaMinus_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hℓodd : Odd ℓ) (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨hℓ, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hM
  have hn4 : 4 ≤ n := hn
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have := four_mul_le_localRank_of_omegaMinus hp hp3 hf hK hn4 hirr e
    omega
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := omegaMinus_exact_scalar_cover hp hp3 hℓ hℓodd hpℓ hf
    hK hn4 hirr (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have h1 := Nat.le_of_dvd Nat.card_pos (hdvd.trans hcard)
  omega

theorem remaining_odd_classical_small_local_rank_quasisimple_prime_center_trivial (hp : p.Prime)
    (hp3 : 3 < p) (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L))
    (hloc : localRank p L ≤ 2) (_hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (_hf : 1 ≤ f)
    {t : StatedLieTag}
    (ht : t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) t n ℓ f) :
    Subgroup.center L = ⊥ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact unitary_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hℓodd hM
  · exact symplectic_quasisimple_prime_center_trivial hp hp3 hL hZ hℓodd hM
  · exact omegaOdd_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hℓodd hM
  · exact omegaPlus_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hℓodd hM
  · exact omegaMinus_small_local_rank_prime_center_trivial hp hp3 hL hZ hloc hℓodd hM

end CFSG.RankThree.CentralLift
