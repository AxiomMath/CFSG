module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabel
import CFSG.LieType.Universal.Spin.Twisted.Datum
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [CharP K 2] in
private theorem w135c2_omfMData_minusTorus_of_lt_eq_bot (hK : Nat.card K = 2) {n : ℕ}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i : Fin (n - 1)}
    (hi : i.val + 1 < n - 1) : minusTorus n hirrQ i = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  rw [minusTorus_of_lt n hirrQ hi, Subgroup.eq_bot_iff_forall]
  rintro x ⟨u, rfl⟩
  have hu : u = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact Units.ext (by simpa using h)
  rw [hu, map_one]

theorem omMinus_two_H_le_shortTorus (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).H ≤ shortTorus n hirrQ ⟨n - 2, by omega⟩ := by
  change (⨆ i, minusTorus n hirrQ i) ≤ shortTorus n hirrQ ⟨n - 2, by omega⟩
  refine iSup_le fun i => ?_
  by_cases hi : i.val + 1 < n - 1
  · rw [w135c2_omfMData_minusTorus_of_lt_eq_bot hK hirrQ hi]
    exact bot_le
  · have hi2 : i = ⟨n - 2, by omega⟩ := by
      apply Fin.ext
      show i.val = n - 2
      have := i.isLt
      omega
    rw [minusTorus_of_not_lt n hirrQ hi, hi2]

variable {k : Type} [Field k] [CharP k 2]

private theorem w135c2_omfMData_dScalar_long_eq_one {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    {χ : spinGroup (quadMinus n K b c) → k} (hχ1 : χ 1 = 1) {i : Fin (n - 1)}
    (hi : i.val + 1 < n - 1) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ i = 1 := by
  refine omq_omMinus_dScalar_eq_one hn hirrQ χ i fun h hh => ?_
  rw [w135c2_omfMData_minusTorus_of_lt_eq_bot hK hirrQ hi] at hh
  rw [Subgroup.mem_bot] at hh
  rw [hh, hχ1]

private theorem w135c2_omfMData_dScalar_eq_one_of_trivial {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {χ : spinGroup (quadMinus n K b c) → k} (i : Fin (n - 1))
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h = 1) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ i = 1 := by
  refine omq_omMinus_dScalar_eq_one hn hirrQ χ i fun h hh => hχ h ?_
  change h ∈ ⨆ j, minusTorus n hirrQ j
  exact Subgroup.mem_iSup_of_mem i hh

private theorem w135c2_omfMData_dScalar_short_eq_zero {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType ρ y χ μ)
    (hne : ∃ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h ≠ 1) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ ⟨n - 2, by omega⟩ = 0 := by
  obtain ⟨h, hh, hχh⟩ := hne
  have hh' : h ∈ minusTorus n hirrQ ⟨n - 2, by omega⟩ := by
    rw [minusTorus_of_not_lt n hirrQ (k := ⟨n - 2, by omega⟩)
      (by show ¬(n - 2 + 1 < n - 1); omega)]
    exact omMinus_two_H_le_shortTorus hK hn hirrQ hh
  exact omq_omMinus_dScalar_eq_zero hn hirrQ χ (fun a ha b hb => ht.chi_mul ha hb)
    ⟨n - 2, by omega⟩ ⟨h, hh', hχh⟩

private theorem w135c2_omfMData_dScalar_eq_zero_or_one {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType ρ y χ μ) (s : Fin (n - 1)) :
    (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ s = 0 ∨
      (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ s = 1 := by
  by_cases hs : s.val + 1 < n - 1
  · exact Or.inr (w135c2_omfMData_dScalar_long_eq_one hn hirrQ hK ht.chi_one hs)
  · by_cases htriv : ∃ h ∈ minusTorus n hirrQ s, χ h ≠ 1
    · exact Or.inl (omq_omMinus_dScalar_eq_zero hn hirrQ χ
        (fun a ha b hb => ht.chi_mul ha hb) s htriv)
    · push Not at htriv
      exact Or.inr (omq_omMinus_dScalar_eq_one hn hirrQ χ s htriv)

theorem omMinus_two_mu_cases_family (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType ρ y χ μ) :
    (∀ s, μ s = 0 ∨ μ s = 1) ∧
      ((∃ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h ≠ 1) →
        μ ⟨n - 2, by omega⟩ = 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd'S : ∀ i : Fin (n - 1),
      (SmallO8mCurtis.curtisDatum n hn hirrQ).d'Scalar χ i =
        (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ i := fun i =>
    CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
      (minusDatum_isCTGroupDatum n hirrQ hn) (minusDatum_steinbergExtras n hirrQ)
      (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirrQ hn) 2
      (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirrQ hγ) χ i
  have hd01 := w135c2_omfMData_dScalar_eq_zero_or_one hn hirrQ hK ht
  refine ⟨fun s => ?_, fun hne => ?_⟩
  · rcases ht.mu_eq s with h | h
    · exact Or.inl h
    · rcases hd01 s with h0 | h1
      · exact Or.inl (by rw [h, hd'S s, h0])
      · exact Or.inr (by rw [h, hd'S s, h1])
  · have hshort := w135c2_omfMData_dScalar_short_eq_zero hn hirrQ hK ht hne
    rcases ht.mu_eq ⟨n - 2, by omega⟩ with h | h
    · exact h
    · rw [h, hd'S]
      exact hshort

theorem omMinus_two_type_cases (hK : Nat.card K = 2) {n : ℕ} (hn : 4 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirrQ).IsCurtisType ρ y χ μ) :
    ((∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h = 1) ∧ μ = 0) ∨
      ((∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h = 1) ∧
        μ = fun s => if s.val = 0 then 1 else 0) ∨
      ∃ j : Fin (n - 1), j.val ≠ 0 ∧ μ j = (SmallO8mCurtis.curtisDatum n hn hirrQ).dScalar χ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcases := omMinus_two_mu_cases_family hK hn hirrQ ht
  by_cases hne : ∃ h ∈ (SmallO8mCurtis.curtisDatum n hn hirrQ).H, χ h ≠ 1
  · right; right
    refine ⟨⟨n - 2, by omega⟩, ?_, ?_⟩
    · show n - 2 ≠ 0
      omega
    · have hμ := hcases.2 hne
      have hd := w135c2_omfMData_dScalar_short_eq_zero hn hirrQ hK ht hne
      rw [hμ, hd]
  · push Not at hne
    by_cases hμ : ∃ j : Fin (n - 1), j.val ≠ 0 ∧ μ j = 1
    · right; right
      obtain ⟨j, hj0, hj1⟩ := hμ
      refine ⟨j, hj0, ?_⟩
      have hd := w135c2_omfMData_dScalar_eq_one_of_trivial hn hirrQ j hne
      rw [hj1, hd]
    · push Not at hμ
      have hμ01 := hcases.1
      have hμne : ∀ s : Fin (n - 1), s.val ≠ 0 → μ s = 0 :=
        fun s hs => (hμ01 s).resolve_right (fun h1 => hμ s hs h1)
      by_cases hzero : ∃ s : Fin (n - 1), s.val = 0 ∧ μ s ≠ 0
      · obtain ⟨s0, hs0, hs0ne⟩ := hzero
        refine Or.inr (Or.inl ⟨hne, ?_⟩)
        funext s
        by_cases hs : s.val = 0
        · have hss0 : s = s0 := Fin.ext (hs.trans hs0.symm)
          rw [hss0, if_pos hs0]
          exact (hμ01 s0).resolve_left hs0ne
        · rw [if_neg hs]
          exact hμne s hs
      · push Not at hzero
        left
        refine ⟨hne, ?_⟩
        funext s
        by_cases hs : s.val = 0
        · exact hzero s hs
        · exact hμne s hs

end CFSG.LocalAnalysis.WeakClosure81
