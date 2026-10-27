module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.Quasithin.SmithCurtis

variable {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
  {k : Type*} [Field k] [CharP k 2]

private theorem c2slomqpl_mul_self_ne_one_of_ne_one {K : Type*} [Field K] [CharP K 2] {a : K}
    (ha : a ≠ 1) : a * a ≠ 1 := by
  rw [← pow_two, sq_ne_one_iff]
  exact ⟨ha, by simpa [CharTwo.neg_eq] using ha⟩

include hn in
theorem omq_omPlus_dScalar_eq_one (χ : spinGroup (quadPlus n F) → k) (i : Fin n)
    (hi : ∀ a : Fˣ, χ (torusD F hn i a) = 1) :
    (omPlusCurtisDatum n F hn).dScalar χ i = 1 := by
  have h := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_neg_one
    (SpinPlus.isCTGroupDatum hn) (plusDatum_steinbergExtras hn)
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn) 2
    (fun _ hγ => isPGroup_plusRootGroup n F hn hγ) χ i (fun h hh => by
      rw [MonoidHom.mem_range] at hh
      obtain ⟨a, rfl⟩ := hh
      exact hi a)
  rw [CharTwo.neg_eq] at h
  exact h

include hn in
theorem omq_omPlus_dScalar_eq_zero (χ : spinGroup (quadPlus n F) → k)
    (hχ : ∀ a ∈ (omPlusCurtisDatum n F hn).H, ∀ b ∈ (omPlusCurtisDatum n F hn).H,
      χ (a * b) = χ a * χ b)
    (hχ1 : χ 1 = 1) (i : Fin n) (hi : ∃ a : Fˣ, χ (torusD F hn i a) ≠ 1) :
    (omPlusCurtisDatum n F hn).dScalar χ i = 0 := by
  obtain ⟨a, ha⟩ := hi
  have hmem : torusD F hn i a ∈ (omPlusCurtisDatum n F hn).H := by
    rw [omPlusCurtisDatum_H]
    exact le_iSup (fun j => (torusD F hn j).range) i (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hnin : (weylD F hn i)⁻¹ = weylD F hn i := by
    have h2 : weylD F hn i * weylD F hn i = 1 := by
      rw [weylD_mul_self]
      have hneg : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
      rw [hneg, map_one]
    exact inv_eq_of_mul_eq_one_right h2
  have hconj : (weylD F hn i)⁻¹ * (torusD F hn i a)⁻¹ * weylD F hn i =
      torusD F hn i a := by
    have h1 : (weylD F hn i) * (torusD F hn i a)⁻¹ * (weylD F hn i)⁻¹ =
        torusD F hn i a := by
      have h0 := congrArg Inv.inv (weylD_mul_torusD_mul_inv (K := F) (hn := hn) i a)
      simpa only [mul_inv_rev, inv_inv, map_inv, mul_assoc] using h0
    rw [hnin] at h1
    rw [hnin]
    exact h1
  have hχt : χ (torusD F hn i a) *
      χ ((weylD F hn i)⁻¹ * (torusD F hn i a)⁻¹ * weylD F hn i) ≠ 1 := by
    rw [hconj]
    exact c2slomqpl_mul_self_ne_one_of_ne_one ha
  exact CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_zero_of_conj
    (SpinPlus.isCTGroupDatum hn) (plusDatum_steinbergExtras hn)
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn) 2
    (fun _ hγ => isPGroup_plusRootGroup n F hn hγ) χ hχ i hmem hχt

include hn in
theorem omq_omPlus_chi_eq_one_of_coroots (χ : spinGroup (quadPlus n F) → k)
    (hχ : ∀ a ∈ (omPlusCurtisDatum n F hn).H, ∀ b ∈ (omPlusCurtisDatum n F hn).H,
      χ (a * b) = χ a * χ b)
    (hχ1 : χ 1 = 1) (h : ∀ (i : Fin n) (a : Fˣ), χ (torusD F hn i a) = 1) :
    ∀ g ∈ (omPlusCurtisDatum n F hn).H, χ g = 1 := by
  intro g hg
  rw [omPlusCurtisDatum_H] at hg
  suffices hkey : g ∈ (omPlusCurtisDatum n F hn).H ∧ χ g = 1 from hkey.2
  refine Subgroup.iSup_induction (fun i => (torusD F hn i).range)
    (C := fun g => g ∈ (omPlusCurtisDatum n F hn).H ∧ χ g = 1) hg ?_ ?_ ?_
  · intro i x hx
    refine ⟨?_, ?_⟩
    · rw [omPlusCurtisDatum_H]
      exact le_iSup (fun j => (torusD F hn j).range) i hx
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      exact h i a
  · exact ⟨one_mem _, hχ1⟩
  · intro x y hx hy
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    rw [hχ x hx.1 y hy.1, hx.2, hy.2, one_mul]

include hn in
theorem omq_omPlus_exists_separating {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus n F)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ) {g : spinGroup (quadPlus n F)}
    (hg : σ g ≠ 1) : ∃ i : Fin n, μ i = (omPlusCurtisDatum n F hn).dScalar χ i := by
  by_contra h
  have hne : ∀ i, μ i ≠ (omPlusCurtisDatum n F hn).dScalar χ i := fun i hi => h ⟨i, hi⟩
  have hμ0 : ∀ i, μ i = 0 := by
    intro i
    rcases ht.mu_eq i with h0 | h1
    · exact h0
    · exact absurd h1 (hne i)
  have hne0 : ∀ i, (omPlusCurtisDatum n F hn).dScalar χ i ≠ 0 := by
    intro i h0
    exact hne i (by rw [hμ0 i, h0])
  have hχmul : ∀ a ∈ (omPlusCurtisDatum n F hn).H, ∀ b ∈ (omPlusCurtisDatum n F hn).H,
      χ (a * b) = χ a * χ b := fun a ha b hb => ht.chi_mul ha hb
  have hcor : ∀ (i : Fin n) (a : Fˣ), χ (torusD F hn i a) = 1 := by
    intro i a
    by_contra ha
    exact hne0 i (omq_omPlus_dScalar_eq_zero hn χ hχmul ht.chi_one i ⟨a, ha⟩)
  have hχH := omq_omPlus_chi_eq_one_of_coroots hn χ hχmul ht.chi_one hcor
  have hμzero : μ = 0 := funext hμ0
  have ht0 : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ 0 := by
    rw [hμzero] at ht
    exact ht
  exact hg (omq_rep_eq_one_of_isCurtisType_zero (omPlusCurtisDatum n F hn) hσ ht0 hχH g)

end CFSG.LocalAnalysis.WeakClosure81
