module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bHolds
public import CFSG.Quasithin.Background.C126NatSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem hsurjSplit_holds :
    ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m → m ≠ 1 →
      ∃ f : ↥(Hinf (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.rankOneParabolic K 3 0)) →*
          Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  intro K hF hFin m hK hm
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    have : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  have hm2 : 2 ≤ m := by omega
  have h4 : ∃ s : Finset K, s.card = 4 := by
    refine CFSG.Quasithin.C126.Nat.exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.exists_sl2Surjection_rankOneParabolic
    (K := K) (r := 3) (i := (0 : Fin 3)) (by decide) h4

theorem kTab23b_holds : KTab23b :=
  kTab23b_of_naturalLines hsurjSplit_holds
