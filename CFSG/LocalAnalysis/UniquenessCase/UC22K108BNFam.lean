module

public import CFSG.Open.SplitBNPair
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108H207
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Milestones.ASVolI.I2
import CFSG.Blueprint.LieModelAPI
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Assembly.OrderReductions.OrderParity
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.ASVolI.ChIJK
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

private theorem k108BNFam_ne_top {S : Type} [Group S] {p : ℕ} {B N : Subgroup S} (hBN : IsSplitBNPair p B N)
    (hp : p ∣ Nat.card S) : B ≠ ⊤ := by
  rintro rfl
  obtain ⟨U, -, -, -, hUi, hUN, -, hsat⟩ := hBN.split
  have hconj : ∀ g : S, CFSG.conjugate (⊤ : Subgroup S) g = ⊤ := fun g =>
    Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective
  simp only [hconj, iInf_top, top_inf_eq] at hsat
  rw [← hsat, inf_top_eq] at hUN
  rw [hUN, Subgroup.index_bot] at hUi
  exact hUi hp

private theorem k108BNFam_of {S : Type} [Group S] (h : ∃ B N : Subgroup S, IsSplitBNPair 2 B N)
    (h2 : 2 ∣ Nat.card S) : ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  obtain ⟨B, N, hBN⟩ := h
  exact ⟨B, N, hBN, k108BNFam_ne_top hBN h2⟩

private theorem k108BNFam_two_dvd_classical {S : Type} [Group S] {t : StatedLieTag} {m n : ℕ}
    (h : LieModel S t m 2 n) (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus) : 2 ∣ Nat.card S := by
  have hc := LieModel.statedClassicalModel h (by rcases ht with rfl | rfl | rfl | rfl <;> decide)
  have hadm := LieModel.admissible h
  obtain ⟨h1, h2, h3, -, h5⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two hc
  rw [← even_iff_two_dvd]
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, -, hm, -⟩ := hadm
    rw [h1 rfl]
    exact CFSG.OrderReductions.OrderParity.orderA_even (m - 1) (2 ^ n) (by omega)
  · obtain ⟨-, -, hm, -⟩ := hadm
    have hconv : ∀ l Q : ℕ, 1 ≤ Q → CFSG.Open.ordTwistedA l Q = CFSG.Open.orderTwistedA l Q := by
      intro l Q hQ
      unfold CFSG.Open.ordTwistedA CFSG.Open.orderTwistedA
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
      have hc : ((Q ^ i : ℕ) : ℤ) = (Q : ℤ) ^ i := Nat.cast_pow Q i
      rcases Nat.even_or_odd i with hi | hi
      · rw [if_pos hi, hi.neg_one_pow]
        omega
      · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
        omega
    rw [h2 rfl, hconv _ _ Nat.one_le_two_pow]
    exact CFSG.OrderReductions.OrderParity.orderTwistedA_even (m - 1) (2 ^ n) (by omega)
  · obtain ⟨-, -, hm, -⟩ := hadm
    rw [h3 rfl]
    exact CFSG.OrderReductions.OrderParity.orderBC_even m (2 ^ n) hm
  · obtain ⟨-, -, hm⟩ := hadm
    rw [h5 rfl]
    exact CFSG.OrderReductions.OrderParity.orderTwistedD_even m (2 ^ n) hm

theorem k108FamL2_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamL2 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSL Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamU3_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamU3 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSU Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamL3_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamL3 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSL Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamSp4_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamSp4 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSp Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamU4_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamU4 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSU Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamU5_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamU5 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ h -
  exact k108BNFam_of (burnsideI2BN_PSU Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamL4_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamL4 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSL Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamSp6_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamSp6 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_PSp Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

theorem k108FamO8m_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamO8m S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  exact k108BNFam_of (burnsideI2BN_POmegaMinus Nat.prime_two (LieModel.admissible h)
    (LieModel.statedClassicalModel h (by decide))) (k108BNFam_two_dvd_classical h (by decide))

section Suzuki


set_option linter.unusedSectionVars false

theorem k108FamSz_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamSz S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ -
  have hsz := (LieModel.suzukiModel h).2
  refine k108BNFam_of (burnsideI2BN_suzuki_model hsz) ?_
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := hsz
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero) _) _

end Suzuki

section Exceptional


set_option linter.unusedSectionVars false

theorem k108FamG2_splitBN : ∀ (S : Type) [Group S] [Finite S], K108FamG2 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, hn, h⟩ -
  refine k108BNFam_of (lieModel_has_splitBNPair Nat.prime_two (by decide) h) ?_
  have hc : Nat.card S = CFSG.Open.ordG2 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two (LieModel.chevalleyExceptionalModel h (by decide))
  rw [hc, CFSG.Open.ordG2]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _

theorem k108Fam3D4_splitBN : ∀ (S : Type) [Group S] [Finite S], K108Fam3D4 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, hn, h⟩ -
  refine k108BNFam_of (lieModel_has_splitBNPair Nat.prime_two (by decide) h) ?_
  have hc : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two (LieModel.chevalleyExceptionalModel h (by decide))
  rw [hc, CFSG.Open.ordTrialityD4]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _) _

theorem k108Fam2F4_splitBN : ∀ (S : Type) [Group S] [Finite S], K108Fam2F4 S → IsSimpleGroup S →
    ∃ B N : Subgroup S, IsSplitBNPair 2 B N ∧ B ≠ ⊤ := by
  rintro S _ _ ⟨n, -, h⟩ hS
  refine k108BNFam_of (lieModel_has_splitBNPair Nat.prime_two (by decide) h) ?_
  have hr := (LieModel.reeTitsModel h (by decide)).2
  obtain ⟨-, -, -, -, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier S 2 n hr
  obtain ⟨-, a, rfl, K, _, _, hK, he⟩ := hr
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two (by omega) hK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨e⟩ := hiso a K rfl hK he
  by_contra h2
  have hbot := CFSG.LieType.Ree.ReeTag.eq_bot_of_normal_of_odd hK ⊤ inferInstance (by
    rw [Subgroup.card_top, ← Nat.card_congr e.toEquiv, Nat.odd_iff]
    omega)
  have h1 : ∀ z : S, e z = 1 := fun z => Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_top (e z))
  obtain ⟨x, y, hxy⟩ := exists_pair_ne S
  exact hxy (e.injective ((h1 x).trans (h1 y).symm))

end Exceptional

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
