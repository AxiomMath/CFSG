module

import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSp
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenClass
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IndicesTwistedA
import CFSG.LocalAnalysis.UniquenessCase.UC22P20w
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGenSeitz
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen

open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Solomon.Coordinator

theorem not_excIndex_B_three {q : TauCeti.PrimePower} {f : ℕ} (hqf : q.exponent = f)
    (hf1 : f ≠ 1) (hf3 : f ≠ 3) :
    ¬ ChevQ.ExcIndex 3 (TauCeti.LieTypeIndex.B 3 q) := by
  rintro (hbal | ⟨-, hrest⟩)
  · rcases hbal with ⟨-, h | h⟩
    · exact hf1 (hqf ▸ h.1.2)
    · exact hf3 (hqf ▸ h.1.2)
  · rcases hrest with hL2 | hG | hB | hE6 | hSix
    · exact hL2
    · exact hG
    · exact hB
    · exact hE6
    · rcases hSix with hF4 | hD4 | hFour
      · exact hF4
      · exact hD4
      · exact hFour

theorem not_excIndex_A_of {q : TauCeti.PrimePower} {r : ℕ}
    (hr : r = 3 ∨ r = 5 ∨ r = 6) : ¬ ChevQ.ExcIndex 3 (TauCeti.LieTypeIndex.A r q) := by
  rintro (hbal | ⟨-, hrest⟩)
  · exact hbal
  · rcases hrest with hL2 | hG | hB | hE6 | hSix
    · rcases hL2 with ⟨hr1, -⟩
      rcases hr with rfl | rfl | rfl <;> omega
    · rcases hG with ⟨-, n, hn, h⟩
      have h9 : 9 ≤ 3 ^ n := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
      rcases hr with rfl | rfl | rfl <;> omega
    · exact hB
    · exact hE6
    · rcases hSix with hF4 | hD4 | hFour
      · exact hF4
      · exact hD4
      · exact hFour

theorem not_excIndex_twistedD_four {q : TauCeti.PrimePower} :
    ¬ ChevQ.ExcIndex 3 (TauCeti.LieTypeIndex.twistedD 4 q) := by
  rintro (hbal | ⟨-, hrest⟩)
  · rcases hbal with ⟨-, -, hodd, h5⟩
    omega
  · rcases hrest with hL2 | hG | hB | hE6 | hSix
    · exact hL2
    · exact hG
    · exact hB
    · exact hE6
    · rcases hSix with hF4 | hD4 | hFour
      · exact hF4
      · exact hD4
      · exact hFour

theorem glbCore_eq_top_or_of_psp_two {L : Type} [Group L]
    [Finite L] (hL : IsSimpleGroup L) (hnc : ∃ a b : L, a * b ≠ b * a) {f : ℕ}
    (hm : LieModel L .PSp 3 2 f) (h243 : ¬ 243 ∣ Nat.card L)
    {A : Subgroup L} (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ f = 1 := by
  by_cases hf1 : f = 1
  · exact Or.inr hf1
  · left
    have hms : CFSG.Open.StatedClassicalModel L .PSp 3 2 f :=
      hm.statedClassicalModel_of_ne_zero (by norm_num)
    obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
      ChevQ.KSExactSp.exists_B_of_statedClassicalModel_PSp_even hms (by norm_num)
    refine glbCore_eq_top_of_classical hL hnc ⟨.B 3 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_B]
      omega
    · rintro ⟨m, q', hd, -⟩
      cases hd
    · by_cases hf3 : f = 3
      · exfalso
        apply h243
        rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hm, hf3]
        decide
      · exact not_excIndex_B_three hqf hf1 hf3

theorem glbCore_eq_top_of_pomegaMinus_two {L : Type} [Group L]
    [Finite L] (hL : IsSimpleGroup L) (hnc : ∃ a b : L, a * b ≠ b * a) {f : ℕ}
    (hm : LieModel L .POmegaMinus 4 2 f) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hms : CFSG.Open.StatedClassicalModel L .POmegaMinus 4 2 f :=
    hm.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨q, hv, hqp, -, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_index_pomegaMinus hms
  refine glbCore_eq_top_of_classical hL hnc ⟨.twistedD 4 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
  · rw [TauCeti.LieTypeIndex.characteristic_twistedD]
    omega
  · rintro ⟨m, q', hd, -⟩
    cases hd
  · exact not_excIndex_twistedD_four

theorem glbCore_eq_top_of_psl_two {L : Type} [Group L]
    [Finite L] (hL : IsSimpleGroup L) (hnc : ∃ a b : L, a * b ≠ b * a) {n f : ℕ}
    (hn : n = 4 ∨ n = 6 ∨ n = 7) (hm : LieModel L .PSL n 2 f) (hf : ¬ (n = 4 ∧ f = 1))
    {A : Subgroup L} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hcard : Nat.card A = 27) : CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hn0 : n ≠ 0 := by omega
  have hms : CFSG.Open.StatedClassicalModel L .PSL n 2 f :=
    hm.statedClassicalModel_of_ne_zero hn0
  have hdup : ¬ (TauCeti.LieTypeIndex.A (n - 1)
      ⟨2, f, hms.1.1, by have h := hms.1.2.1; omega⟩).IsDuplicateRepresentative := by
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [TauCeti.PrimePower.card_def]
    rintro (⟨h1n, -⟩ | ⟨h2n, -⟩ | ⟨h3n, hpow⟩)
    · omega
    · omega
    · have hf1 : f = 1 :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 2) (hpow.trans (pow_one 2).symm)
      have hn4 : n = 4 := by omega
      exact hf ⟨hn4, hf1⟩
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
    ChevQ.E6Three.KSConn.exists_A_of_statedClassicalModel_PSL L n 2 f hms hdup
  rcases hn with rfl | rfl | rfl
  · refine glbCore_eq_top_of_classical hL hnc ⟨.A 3 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_A]
      omega
    · rintro ⟨m, q', hd, -⟩
      cases hd
    · exact not_excIndex_A_of (Or.inl rfl)
  · refine glbCore_eq_top_of_classical hL hnc ⟨.A 5 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_A]
      omega
    · rintro ⟨m, q', hd, -⟩
      cases hd
    · exact not_excIndex_A_of (Or.inr (Or.inl rfl))
  · refine glbCore_eq_top_of_classical hL hnc ⟨.A 6 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_A]
      omega
    · rintro ⟨m, q', hd, -⟩
      cases hd
    · exact not_excIndex_A_of (Or.inr (Or.inr rfl))

private theorem not_utoralRestPrime_twistedA_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq2 : q.card ≠ 2) :
    ¬ CFSG.LieType.SeitzGeneration.UToralRestPrime ⟨.twistedA 3 q, hv⟩ 3 := by
  rintro ⟨m, q', hd, h3, hrest⟩
  obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj hd
  rcases hrest with h2 | hg
  · exact hq2 h2
  · have h4 : 3 ∣ 4 := hg.trans (Nat.gcd_dvd_left _ _)
    norm_num at h4

private theorem not_utoralRestPrime_twistedA_of_mod {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) (hq : q.card % 3 = 1) :
    ¬ CFSG.LieType.SeitzGeneration.UToralRestPrime ⟨.twistedA m q, hv⟩ 3 := by
  rintro ⟨m', q', hd, h3, -⟩
  obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj hd
  omega

theorem glbCore_eq_top_of_psu_two {L : Type} [Group L]
    [Finite L] (hL : IsSimpleGroup L) (hnc : ∃ a b : L, a * b ≠ b * a) {n f : ℕ}
    (hn : n = 4 ∨ n = 6 ∨ n = 7) (hm : LieModel L .PSU n 2 f) (hq2 : 2 ^ f ≠ 2)
    (hq : n ≠ 4 → 2 ^ f % 3 = 1) (h243 : ¬ 243 ∣ Nat.card L)
    {A : Subgroup L} (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hn0 : n ≠ 0 := by omega
  have hms : CFSG.Open.StatedClassicalModel L .PSU n 2 f :=
    hm.statedClassicalModel_of_ne_zero hn0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
    ChevQ.KSExact.exists_twistedA_of_statedClassicalModel_PSU hms
  have hqc : q.card = 2 ^ f := by
    rw [TauCeti.PrimePower.card_def, hqp, hqf]
  have h1 : ¬ ChevQ.IsTwoPow q 1 := by
    rintro ⟨-, he⟩
    exact hq2 (by rw [← hqf, he]; norm_num)
  rcases hn with h4 | h6 | h7
  · obtain rfl : m = 3 := by omega
    have h3 : ¬ ChevQ.IsTwoPow q 3 := by
      rintro ⟨-, he⟩
      have hf3 : f = 3 := hqf ▸ he
      apply h243
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hm, hf3]
      decide
    refine glbCore_eq_top_of_classical hL hnc ⟨.twistedA 3 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_twistedA]; omega
    · exact not_utoralRestPrime_twistedA_three hv (by rw [hqc]; exact hq2)
    · exact ChevQ.not_excIndex_twistedA h1 h3
  · obtain rfl : m = 5 := by omega
    have h3 : ¬ ChevQ.IsTwoPow q 3 := by
      rintro ⟨-, he⟩
      have hf3 : f = 3 := hqf ▸ he
      rw [hf3] at hq; norm_num at hq
    refine glbCore_eq_top_of_classical hL hnc ⟨.twistedA 5 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_twistedA]; omega
    · exact not_utoralRestPrime_twistedA_of_mod hv (by rw [hqc]; exact hq (by omega))
    · exact ChevQ.not_excIndex_twistedA h1 h3
  · obtain rfl : m = 6 := by omega
    have h3 : ¬ ChevQ.IsTwoPow q 3 := by
      rintro ⟨-, he⟩
      have hf3 : f = 3 := hqf ▸ he
      rw [hf3] at hq; norm_num at hq
    refine glbCore_eq_top_of_classical hL hnc ⟨.twistedA 6 q, hv⟩ ⟨e⟩ ?_ trivial ?_ ?_ hA hcard
    · rw [TauCeti.LieTypeIndex.characteristic_twistedA]; omega
    · exact not_utoralRestPrime_twistedA_of_mod hv (by rw [hqc]; exact hq (by omega))
    · exact ChevQ.not_excIndex_twistedA h1 h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen
