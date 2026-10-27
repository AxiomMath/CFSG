module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNonBinary
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusIsoNat
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabels
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabel
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
  CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqma8_d'Scalar_eq_dScalar {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*}
    [Field k] (χ : spinGroup (quadMinus n K b c) → k) (i : Fin (n - 1)) :
    (SmallO8mCurtis.curtisDatum n hn hirr).d'Scalar χ i =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ i

theorem omq_omMinus_node_zero_dichotomy (h1l : OmqMinusWeightVectorLong) (h2 : OmqRankFromWeights)
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hF4 : 4 ≤ Nat.card K) {k V : Type} [Field k]
    [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V] (ι : K →+* k)
    (ι' : ShortField b c →+* k) (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x)
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hJ : ∀ i : Fin (n - 1),
      μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ↔ i.val = 0)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ n - 1) π s) :
    (∃ (a : ℕ) (β : V ≃ₗ[k] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k)),
      ∀ (g : spinGroup (quadMinus n K b c)) (v : V),
        β (σ g v) = SmallO8mCurtis.naturalRep n b c (ι.comp (iterateFrobenius K 2 a)) g (β v)) ∨
    4 ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  obtain ⟨cc, hc1, hcq, hχ, hμ1, hμ0⟩ := omq_omMinus_label_of_single hn hirr ι ht hJ
  by_cases hpow : ∃ a : ℕ, cc = 2 ^ a
  · obtain ⟨a, rfl⟩ := hpow
    left
    have hodd : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units]
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨e, -, hcard⟩ := FiniteField.card K 2
      have hcard' : Nat.card K = 2 ^ (e : ℕ) := by
        rw [Nat.card_eq_fintype_card, hcard]
      rw [hcard']
      exact Nat.Even.sub_odd (Nat.succ_le_of_lt (Nat.two_pow_pos (e : ℕ)))
        (Even.pow_of_ne_zero (even_two : Even (2 : ℕ)) e.2.ne') odd_one
    have hclt : 2 ^ a < Nat.card Kˣ := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rw [pow_zero]
        have h3 : 3 ≤ Nat.card Kˣ := by
          rw [Nat.card_units]
          omega
        omega
      · have heven : Even (2 ^ a) := even_two.pow_of_ne_zero (Nat.ne_of_gt ha)
        have hne : 2 ^ a ≠ Nat.card Kˣ := by
          intro h
          exact (Nat.not_even_iff_odd.mpr hodd) (h ▸ heven)
        exact lt_of_le_of_ne hcq hne
    have hμzero : μ = 0 := by
      funext i
      by_cases hi : i.val = 0
      · have hie : i = (⟨0, by omega⟩ : Fin (n - 1)) := Fin.ext hi
        rw [hie]
        exact hμ0 hclt
      · have hne : μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i :=
          fun h => hi ((hJ i).mp h)
        rcases ht.mu_eq i with h0 | hd
        · exact h0
        · exact absurd (hd.trans (c2slomqma8_d'Scalar_eq_dScalar hn hirr χ i)) hne
    obtain ⟨β, hβ⟩ := omq_omMinus_iso_natural hn hirr hF4 ι hσ ht hμzero (a := a) hχ
    exact ⟨a, β, hβ⟩
  · right
    exact omq_omMinus_nonbinary_rank h1l h2 hn hirr ι ι' hι' hσ ht ((hJ _).mpr rfl) hc1 hcq hχ
      (fun a h => hpow ⟨a, h⟩) hxr hs hsh

end CFSG.LocalAnalysis.WeakClosure81
