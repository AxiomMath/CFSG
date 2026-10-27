module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQHcoeffGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

theorem omq_omPlus_hcoeff {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {k : Type} [Field k] [CharP k 2] (ι : F →+* k) {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus n F)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ) {i : Fin n}
    (hi : μ i = (omPlusCurtisDatum n F hn).dScalar χ i) {c : ℕ} (hc : 1 ≤ c)
    (hχ : ∀ a : Fˣ, χ (torusD F hn i a) = ι (a : F) ^ c) :
    ∃ φ : Module.Dual k V, φ y = 1 ∧ ∀ s t : F,
      φ (σ (rootD F hn i (Multiplicative.ofAdd s) * negRootD F hn i (Multiplicative.ofAdd t)) y) =
        (1 + ι s * ι t) ^ c := by
  classical
  let D := omPlusCurtisDatum n F hn
  have hX : ∀ a, rankOneD F hn i (upperSL2 a) ∈ D.U := by
    intro a
    rw [rankOneD_upperSL2]
    apply D.X_le i
    change _ ∈ plusRootGroup n F hn (Pi.single i 1)
    rw [plusRootGroup_single]
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  have hY : ∀ a, rankOneD F hn i (lowerSL2 a) ∈ D.L := by
    intro a
    rw [rankOneD_lowerSL2]
    have hmem : negRootD F hn i (Multiplicative.ofAdd a) ∈ (negRootD F hn i).range := ⟨_, rfl⟩
    rw [← plusRootGroup_neg_single hn i] at hmem
    exact D.Y_le i hmem
  have hT : ∀ a : Fˣ, rankOneD F hn i (diagSL2 a) ∈ D.H := by
    intro a
    rw [← torusD_apply, omPlusCurtisDatum_H]
    exact Subgroup.mem_iSup_of_mem i ⟨a, rfl⟩
  have hN : σ (rankOneD F hn i (weylSL2 1)) y ∈ augSub σ D.L := by
    rw [← weylD_eq_rankOneD]
    have h := D.act_n_sub_mem_augL σ i ht.1
    rw [ht.2.2.2 i, D.heckeD_weight σ i ht.2.2.1, ← sub_smul, hi, sub_self, zero_smul,
      sub_zero] at h
    exact h
  obtain ⟨φ, hφ1, hφ⟩ := omq_curtis_hcoeff_of_sl2 D ι hσ ht (rankOneD F hn i) hX hY hT hc
    (fun a => by rw [← torusD_apply]; exact hχ a) hN
  refine ⟨φ, hφ1, fun s t => ?_⟩
  rw [← rankOneD_upperSL2, ← rankOneD_lowerSL2]
  exact hφ s t

end CFSG.LocalAnalysis.WeakClosure81
