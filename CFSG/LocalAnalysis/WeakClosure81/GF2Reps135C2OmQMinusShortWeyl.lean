module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusShortWord
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqi6_conj_shortWeyl_long {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    (minusFrame n b c).longWeyl hij true false * shortWeyl n hirr j *
        ((minusFrame n b c).longWeyl hij true false)⁻¹ = shortWeyl n hirr i := by
  have hsign : (longWeylSign i j : K) = 1 := by
    simp [longWeylSign, hij.symm]
  have hx : ∀ t : Bool,
      (minusFrame n b c).longWeyl hij true false *
        twShortRoot n hirr j t (.ofAdd planeOne) *
          ((minusFrame n b c).longWeyl hij true false)⁻¹ =
      twShortRoot n hirr i t (.ofAdd planeOne) := by
    intro t
    rw [longWeyl_conj_twShortRoot, longWeylBool_true_false, Equiv.swap_apply_right, hsign,
      one_smul]
  rw [shortWeyl_eq, shortWeyl_eq]
  calc
    (minusFrame n b c).longWeyl hij true false *
        (shortPosHom n hirr j (.ofAdd planeOne) * shortNegHom n hirr j (.ofAdd planeOne) *
          shortPosHom n hirr j (.ofAdd planeOne)) *
          ((minusFrame n b c).longWeyl hij true false)⁻¹ =
      ((minusFrame n b c).longWeyl hij true false * shortPosHom n hirr j (.ofAdd planeOne) *
        ((minusFrame n b c).longWeyl hij true false)⁻¹) *
      ((minusFrame n b c).longWeyl hij true false * shortNegHom n hirr j (.ofAdd planeOne) *
        ((minusFrame n b c).longWeyl hij true false)⁻¹) *
      ((minusFrame n b c).longWeyl hij true false * shortPosHom n hirr j (.ofAdd planeOne) *
        ((minusFrame n b c).longWeyl hij true false)⁻¹) := by group
    _ = _ := by
      have hx1 := hx true
      have hx0 := hx false
      simp only [twShortRoot_true, twShortRoot_false] at hx1 hx0
      rw [hx1, hx0]

private theorem c2slomqi6_minusWeyl_sq {n : ℕ} {K : Type} [Field K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    minusWeyl n hirr i * minusWeyl n hirr i = 1 := by
  have hneg : (-1 : Kˣ) = 1 := by
    apply Units.ext
    change (-1 : K) = 1
    exact CharTwo.neg_eq 1
  by_cases hi : i.val + 1 < n - 1
  · rw [minusWeyl_of_lt n hirr hi, (minusFrame n b c).toHypFrame.longWeyl_mul_self, hneg,
      map_one]
  · rw [minusWeyl_of_not_lt n hirr hi, shortWeyl_eq_minusFrame,
      (minusFrame n b c).shortWeyl_mul_self, hneg, map_one]

theorem omq_omMinus_shortWeyl_eq_prod {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    shortWeyl n hirr ⟨0, by omega⟩ =
      ((omqMinusShortWord (n - 1) (by omega)).map (minusWeyl n hirr)).prod := by
  have hl : 0 < n - 1 := by omega
  have key : ∀ d : ℕ, (hd : d < n - 1) →
      shortWeyl n hirr ⟨n - 2 - d, by omega⟩ =
        ((omqMinusPalWord (n - 1) hl d).map (minusWeyl n hirr)).prod := by
    intro d
    induction d with
    | zero =>
      intro hd
      have h1 : ¬ ((⟨n - 2 - 0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1) := by
        show ¬ (n - 2 - 0 + 1 < n - 1)
        omega
      have h2 : (⟨n - 2 - 0, by omega⟩ : Fin (n - 1)) = ⟨n - 1 - 1, by omega⟩ := by
        apply Fin.ext
        show n - 2 - 0 = n - 1 - 1
        omega
      rw [omqMinusPalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        h2, ← minusWeyl_of_not_lt n hirr (k := ⟨n - 1 - 1, by omega⟩)
          (by show ¬ (n - 1 - 1 + 1 < n - 1); omega)]
    | succ d ih =>
      intro hd
      have hlt : (⟨n - 1 - 2 - d, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by
        show n - 1 - 2 - d + 1 < n - 1
        omega
      have hidx : (⟨n - 2 - (d + 1), by omega⟩ : Fin (n - 1)) =
          ⟨n - 1 - 2 - d, by omega⟩ := by
        apply Fin.ext
        show n - 2 - (d + 1) = n - 1 - 2 - d
        omega
      have hnext : (⟨n - 2 - d, by omega⟩ : Fin (n - 1)) =
          ⟨(⟨n - 1 - 2 - d, by omega⟩ : Fin (n - 1)).val + 1, hlt⟩ := by
        apply Fin.ext
        show n - 2 - d = n - 1 - 2 - d + 1
        omega
      have ih' := ih (by omega)
      rw [hnext] at ih'
      have hconj := c2slomqi6_conj_shortWeyl_long hirr
        (succ_ne_of_lt n (k := ⟨n - 1 - 2 - d, by omega⟩) hlt)
      have hinv : (minusWeyl n hirr ⟨n - 1 - 2 - d, by omega⟩)⁻¹ =
          minusWeyl n hirr ⟨n - 1 - 2 - d, by omega⟩ :=
        inv_eq_of_mul_eq_one_right (c2slomqi6_minusWeyl_sq hirr _)
      rw [← minusWeyl_of_lt n hirr hlt, hinv, ih'] at hconj
      rw [hidx, ← hconj]
      simp only [omqMinusPalWord, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
        List.prod_append, List.prod_nil, mul_one]
      group
  have hd0 : n - 1 - 1 < n - 1 := by omega
  have h0 := key (n - 1 - 1) hd0
  have hidx : (⟨n - 2 - (n - 1 - 1), by omega⟩ : Fin (n - 1)) = ⟨0, by omega⟩ := by
    apply Fin.ext
    show n - 2 - (n - 1 - 1) = 0
    omega
  rw [hidx] at h0
  exact h0

theorem omq_omMinus_shortWeyl_mem_augSub {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k]
    {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hex : ∃ j : Fin (n - 1), μ j = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ j) :
    σ (shortWeyl n hirr ⟨0, by omega⟩) y ∈ augSub σ (SmallO8mCurtis.curtisDatum n hn hirr).L := by
  classical
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  have hl : 3 ≤ n - 1 := by omega
  obtain ⟨j, hj⟩ := hex
  have hred := omq_omMinus_reduced_shortWord (n - 1) hl
  have hprod : D.nW ((coxeterMatrix (isFiniteType_cartanB (n - 1))).toCoxeterSystem.wordProd
      (omqMinusShortWord (n - 1) (by omega))) =
      ((omqMinusShortWord (n - 1) (by omega)).map (minusWeyl n hirr)).prod :=
    CFSG.LieType.Steinberg.nrep_wordProd (minusDatum_isCTGroupDatum n hirr hn) hred
  have hcoinv := D.coinv_formula σ hred ht.1
  rw [D.coinvOp_eigen σ ht.2.2.1 ht.2.2.2] at hcoinv
  have hzero : D.coinvScalar χ μ (omqMinusShortWord (n - 1) (by omega)) = 0 := by
    unfold CurtisDatum.coinvScalar
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨j, omq_omMinus_shortWord_mem (n - 1) (by omega) j, by
      rw [hj, sub_self]⟩
  rw [hzero, zero_smul, sub_zero, hprod, ← omq_omMinus_shortWeyl_eq_prod hn hirr] at hcoinv
  exact hcoinv

end CFSG.LocalAnalysis.WeakClosure81
