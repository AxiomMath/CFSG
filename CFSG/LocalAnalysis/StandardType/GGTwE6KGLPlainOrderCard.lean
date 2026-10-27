module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPlainOrderPSU
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.RankThree.PartOne.F106.ConvOrdBound
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem omega_eight_le_plainOrd {q x : ℤ} (hq : 2 ≤ q) (hx0 : 0 ≤ x) (hx : x ≤ q ^ 5) :
    q ^ (4 * (4 - 1)) * x * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) ≤ q ^ 29 := by
  have h1 : (1 : ℤ) ≤ q := by linarith
  have hf : ∀ i ∈ Finset.Icc 1 (4 - 1), 0 ≤ q ^ (2 * i) - 1 := fun i _ =>
    sub_nonneg.2 (one_le_pow₀ h1)
  have hprod : ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) ≤ q ^ 12 := by
    calc ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1)
        ≤ ∏ i ∈ Finset.Icc 1 (4 - 1), q ^ (2 * i) :=
          Finset.prod_le_prod₀ hf fun i _ => by linarith
      _ = q ^ 12 := by
          rw [Finset.prod_pow_eq_pow_sum,
            show ∑ i ∈ Finset.Icc 1 (4 - 1), 2 * i = 12 by decide]
  calc q ^ (4 * (4 - 1)) * x * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1)
      ≤ q ^ 12 * q ^ 5 * q ^ 12 :=
        mul_le_mul (mul_le_mul le_rfl hx hx0 (by positivity)) hprod (Finset.prod_nonneg hf)
          (by positivity)
    _ = q ^ 29 := by ring

private theorem one_le_of_card_plainOrd {K : Type} [Field K] [Finite K] {g : ℕ}
    (hK : g = 0 → Nat.card K = 1) : 1 ≤ g := by
  rcases Nat.eq_zero_or_pos g with h0 | h
  · have := Finite.one_lt_card (α := K)
    rw [hK h0] at this
    exact absurd this (lt_irrefl 1)
  · exact h

private theorem finite_largeEvenProj_plainOrd {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (LargeEvenProj H) :=
  have : Finite H := Subtype.finite
  Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

private theorem crude_lt_plainOrd {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    (H : Subgroup (GL ι K)) {g e : ℕ} (hK : Nat.card K = (2 ^ g) ^ e)
    (hd : e * (Fintype.card ι * Fintype.card ι) ≤ 29) :
    Finite (LargeEvenProj H) ∧ Nat.card (LargeEvenProj H) < CFSG.Open.ordTwistedA 5 (2 ^ g) := by
  have hg : 1 ≤ g := one_le_of_card_plainOrd (K := K) fun h0 => by
    rw [hK, h0, pow_zero, one_pow]
  have : Finite H := Subtype.finite
  refine ⟨finite_largeEvenProj_plainOrd H,
    lt_of_le_of_lt ?_ (pow_twentyNine_lt_ordTwistedA_five hg)⟩
  calc Nat.card (LargeEvenProj H) ≤ Nat.card H :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    _ ≤ Nat.card (GL ι K) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card (Matrix ι ι K) :=
        Nat.card_le_card_of_injective (fun g : GL ι K => (g : Matrix ι ι K)) Units.val_injective
    _ = (2 ^ g) ^ (e * (Fintype.card ι * Fintype.card ι)) := by
        show Nat.card (ι → ι → K) = _
        rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), hK]
        ring
    _ ≤ (2 ^ g) ^ 29 := Nat.pow_le_pow_right (Nat.two_pow_pos g) hd

private theorem card_largeEvenProj_SU_plainOrd {N g : ℕ} (hN : 1 ≤ N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) :
    1 ≤ g ∧ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) =
      CFSG.Open.ordTwistedA N (2 ^ g) := by
  have hg : 1 ≤ g := one_le_of_card_plainOrd (K := K) fun h0 => by
    rw [hK, h0, pow_zero, one_pow]
  refine ⟨hg, ?_⟩
  change Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU (N + 1) (2 ^ g) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hg hK (by omega),
    CFSG.Open.ordTwistedA, Nat.add_sub_cancel, Nat.mul_comm (N + 1) N]

private theorem unitary_plainOrd {N g : ℕ} (hN : N = 3 ∨ N = 4) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ g) ^ 2) :
    Finite (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) ∧
      Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) <
        CFSG.Open.ordTwistedA 5 (2 ^ g) := by
  obtain ⟨hg, hR⟩ := card_largeEvenProj_SU_plainOrd (N := N) (by omega) hK
  refine ⟨finite_largeEvenProj_plainOrd _, ?_⟩
  rw [hR]
  exact lt_of_le_of_lt ((CFSG.RankThree.PartOne.F106.ordTwistedA_le N _
    (Nat.one_lt_two_pow (by omega))).trans
    (Nat.pow_le_pow_right (Nat.two_pow_pos g) (by rcases hN with rfl | rfl <;> decide)))
    (pow_twentyNine_lt_ordTwistedA_five hg)

private theorem omegaMinus_plainOrd {N g : ℕ} (hN : N ≤ 4) (h2 : N ≠ 2) (h3 : N ≠ 3) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ g) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (N - 1) b c))) ∧
      Nat.card (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (N - 1) b c))) <
        CFSG.Open.ordTwistedA 5 (2 ^ g) := by
  have hK1 : Nat.card K = (2 ^ g) ^ 1 := hK.trans (pow_one _).symm
  rcases (by omega : N - 1 = 0 ∨ N = 4) with h0 | rfl
  · refine crude_lt_plainOrd _ hK1 ?_
    simp only [Fintype.card_sum, Fintype.card_fin, h0]
    norm_num
  have hg : 1 ≤ g := one_le_of_card_plainOrd (K := K) fun h0 => by rw [hK, h0, pow_zero]
  haveI := CFSG.StandardType.charP_two_of_card hK
  refine ⟨finite_largeEvenProj_plainOrd _, lt_of_le_of_lt ?_
    (pow_twentyNine_lt_ordTwistedA_five hg)⟩
  show Nat.card (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 3 b c))) ≤ _
  have e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 3 b c)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (3 + 1) K b c)) :=
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj (LargeEvenOmega (LargeEvenQMinus 3 b c))).symm.trans
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.omegaModelEquivOfReindex
        (Equiv.sumAssoc (Fin 3) (Fin 3) (Fin 2)) (Q := LargeEvenQMinus 3 b c)
        (Q' := CFSG.Open.StatedQuadMinus (3 + 1) K b c) fun _ => rfl)
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K)
    (n := 4) le_rfl hirr
  have hq : (2 : ℤ) ≤ (Nat.card K : ℤ) := by
    rw [hK]
    exact_mod_cast Nat.one_lt_two_pow (by omega)
  have h4 : (Nat.card K : ℤ) ^ 4 * 2 ≤ (Nat.card K : ℤ) ^ 4 * Nat.card K :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h1 : (1 : ℤ) ≤ (Nat.card K : ℤ) ^ 4 := one_le_pow₀ (by linarith)
  have hb := h.le.trans (omega_eight_le_plainOrd (x := (Nat.card K : ℤ) ^ 4 + 1) hq
    (by positivity) (by rw [pow_succ]; linarith))
  rw [hK] at hb
  rw [Nat.card_congr e.toEquiv]
  exact_mod_cast hb

theorem largeEvenLabelAll_card_lt_ordTwistedA_five_classical {lab : LargeEvenLabel}
    (h : (lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank ≤ 4)) :
    LargeEvenLabelAll lab fun R _ _ _ =>
      Finite R ∧ Nat.card R < CFSG.Open.ordTwistedA 5 (2 ^ lab.n) := by
  obtain ⟨t, N, g⟩ := lab
  dsimp only at h ⊢
  intro Q hQ
  rcases h with ⟨rfl, hN⟩ | ⟨rfl, hN⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, unitary_plainOrd hN hK⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      exact ⟨K, i1, i2, hK, hq, crude_lt_plainOrd _ hK
        (by simp only [Fintype.card_fin]; norm_num)⟩
    · obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      exact ⟨K, i1, i2, hK, hq, unitary_plainOrd (N := 3) (Or.inl rfl) hK⟩
    · obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hQ
      exact ⟨K, i1, i2, hK, b, c, hbc, hq, omegaMinus_plainOrd hN h2 h3 hK hbc⟩

end CFSG.StandardType.SCFourCover
