module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFNW

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw5_inv_pow_val {k : Type*} [Field k] {M : ℕ} [NeZero M] {u : k}
    (hu : u ^ M = 1) (hne : u ≠ 0) (x : ZMod M) : (u⁻¹) ^ x.val = u ^ (-x).val := by
  have h1 : u ^ ((-x).val + x.val) = 1 := by
    have h2 : (((-x).val + x.val : ℕ) : ZMod M) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, neg_add_cancel]
    obtain ⟨j, hj⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h2
    rw [hj, pow_mul, hu, one_pow]
  rw [pow_add] at h1
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_left h1).symm

private theorem c2slomqmw5_toral_pow_eq_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] (ι : K →+* k)
    (ι' : ShortField b c →+* k) {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ}
    {z : ShortField b c} (hg : OmqMinusToral n g t z) :
    (∀ i, ι (t i : K) ^ Nat.card Kˣ = 1) ∧ ι' z ^ (Nat.card K + 1) = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  · rw [← map_pow, omq_shortField_pow_card_succ hirr, hg.2.2.1, map_one, map_one]

private theorem c2slomqmw5_toral_conj {n : ℕ} {K : Type*} [Field K] {b c : K}
    {π : Equiv.Perm (Fin (n - 1))} {s : Fin (n - 1) → ℤ} (hs : SpIsSign s)
    {T g : spinGroup (quadMinus n K b c)}
    (hT : omqnfActs n b c π s (spinAction (quadMinus n K b c) T))
    {t : Fin (n - 1) → Kˣ} {z : ShortField b c} (hg : OmqMinusToral n g t z) :
    OmqMinusToral n (T⁻¹ * g * T) (fun a => (t (π a)) ^ (s a))
      (if ∏ a, s a = 1 then z else star z) := by
  have hE : ∀ a, spinAction (quadMinus n K b c) (T⁻¹ * g * T) (eVec n a) =
      (((t (π a)) ^ (s a) : Kˣ) : K) • eVec n a := by
    intro a
    have h1 := hT.1 (Sum.inl a)
    rw [spMonoPerm_inl] at h1
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rcases hs a with ha | ha
    · rw [if_pos ha] at h1
      change spinAction (quadMinus n K b c) T (eVec n a) = eVec n (π a) at h1
      rw [h1, hg.1, map_smul, ha, zpow_one]
      rw [spinAction_inv_apply_of_apply _ T h1]
    · have hne : ¬ s a = 1 := by rw [ha]; norm_num
      rw [if_neg hne] at h1
      change spinAction (quadMinus n K b c) T (eVec n a) = fVec n (π a) at h1
      rw [h1, hg.2.1, map_smul, ha, zpow_neg_one]
      rw [spinAction_inv_apply_of_apply _ T h1]
  have hF : ∀ a, spinAction (quadMinus n K b c) (T⁻¹ * g * T) (fVec n a) =
      ((((t (π a)) ^ (s a))⁻¹ : Kˣ) : K) • fVec n a := by
    intro a
    have h1 := hT.1 (Sum.inr a)
    rw [spMonoPerm_inr] at h1
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rcases hs a with ha | ha
    · rw [if_pos ha] at h1
      change spinAction (quadMinus n K b c) T (fVec n a) = fVec n (π a) at h1
      rw [h1, hg.2.1, map_smul, ha, zpow_one]
      rw [spinAction_inv_apply_of_apply _ T h1]
    · have hne : ¬ s a = 1 := by rw [ha]; norm_num
      rw [if_neg hne] at h1
      change spinAction (quadMinus n K b c) T (fVec n a) = eVec n (π a) at h1
      rw [h1, hg.1, map_smul, ha, zpow_neg_one, inv_inv]
      rw [spinAction_inv_apply_of_apply _ T h1]
  have hrefl : ∀ w : ShortField b c, planeRefl b c planeOne (fieldCoord w) =
      fieldCoord (-(star w)) := by
    intro w
    ext k
    fin_cases k <;>
      simp [planeRefl, planeOne, fieldCoord, polarPlane, planeNorm] <;> ring
  have hP : ∀ u : ShortField b c, spinAction (quadMinus n K b c) (T⁻¹ * g * T)
      (planeVec n (fieldCoord u)) =
      planeVec n (fieldCoord ((if ∏ a, s a = 1 then z else star z) * u)) := by
    intro u
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    by_cases hp : ∏ a, s a = 1
    · rw [if_pos hp]
      have h2 : spinAction (quadMinus n K b c) T (planeVec n (fieldCoord u)) =
          planeVec n (fieldCoord u) := by
        rw [hT.2, if_pos hp]
      have h3 : spinAction (quadMinus n K b c) T (planeVec n (fieldCoord (z * u))) =
          planeVec n (fieldCoord (z * u)) := by
        rw [hT.2, if_pos hp]
      rw [h2, hg.2.2.2 u, spinAction_inv_apply_of_apply _ T h3]
    · rw [if_neg hp]
      have h2 : ∀ w : ShortField b c, spinAction (quadMinus n K b c) T
          (planeVec n (fieldCoord w)) = planeVec n (fieldCoord (-(star w))) := by
        intro w
        rw [hT.2, if_neg hp, hrefl]
      have h3 : spinAction (quadMinus n K b c) T
          (planeVec n (fieldCoord (-(star (z * -(star u)))))) =
          planeVec n (fieldCoord (z * -(star u))) := by
        rw [h2, star_neg, star_star, neg_neg]
      rw [h2, hg.2.2.2, spinAction_inv_apply_of_apply _ T h3]
      congr 2
      rw [star_mul', star_neg, star_star]
      ring
  refine ⟨hE, hF, ?_, hP⟩
  split_ifs
  · exact hg.2.2.1
  · rw [QuadraticAlgebra.norm_star]
    exact hg.2.2.1

theorem omq_omMinus_wt_conj {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k) (ι' : ShortField b c →+* k)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s)
    (ν : OmqMinusLat (n - 1) m h) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    ((SmallO8mCurtis.curtisDatum n hn hirr).nW x)⁻¹ * g *
        (SmallO8mCurtis.curtisDatum n hn hirr).nW x ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H ∧
      omqMinusWt n ι ι' ν (((SmallO8mCurtis.curtisDatum n hn hirr).nW x)⁻¹ * g *
          (SmallO8mCurtis.curtisDatum n hn hirr).nW x) =
        omqMinusWt n ι ι' (omqMinusAct π s ν) g := by
  haveI := fact_shortField hirr
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  haveI : NeZero h := ⟨by omega⟩
  obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr hg
  have hact := omqnf_spinAction_nW hn hirr hxr hs
  have hconj := c2slomqmw5_toral_conj hs hact ht
  refine ⟨CFSG.Quasithin.SmithCurtis.CurtisDatum.nW_normH
    (D := SmallO8mCurtis.curtisDatum n hn hirr) x hg, ?_⟩
  obtain ⟨hpt, hpz⟩ := c2slomqmw5_toral_pow_eq_one hirr ι ι' ht
  rw [omq_omMinus_wt_eq_of_toral ι ι' ν hconj,
    omq_omMinus_wt_eq_of_toral ι ι' (omqMinusAct π s ν) ht]
  congr 1
  · rw [← Equiv.prod_comp π (fun b => ι (t b : K) ^ ((omqMinusAct π s ν).1 b).val)]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hu : ι (t (π a) : K) ^ m = 1 := by rw [hm]; exact hpt (π a)
    have hne : ι (t (π a) : K) ≠ 0 := fun h0 =>
      (t (π a)).ne_zero (ι.injective (h0.trans (map_zero ι).symm))
    have e : (omqMinusAct π s ν).1 (π a) = ((s a : ℤ) : ZMod m) * ν.1 a := by
      simp [omqMinusAct, omqSignedAct]
    rw [e]
    rcases hs a with ha | ha
    · rw [ha]
      simp
    · rw [ha]
      simp only [zpow_neg, zpow_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      rw [Units.val_inv_eq_inv_val, map_inv₀, c2slomqmw5_inv_pow_val hu hne]
  · have e : (omqMinusAct π s ν).2 = ((∏ a, s a : ℤ) : ZMod h) * ν.2 := rfl
    rw [e]
    by_cases hp : ∏ a, s a = 1
    · rw [if_pos hp, hp]
      simp
    · have hp' : ∏ a, s a = -1 := by
        have hprod : ∏ a, s a = 1 ∨ ∏ a, s a = -1 := by
          refine Finset.prod_induction s (fun x => x = 1 ∨ x = -1) ?_ (Or.inl rfl)
            (fun a _ => hs a)
          rintro x y (hx | hx) (hy | hy) <;> simp [hx, hy]
        rcases hprod with h1 | h1
        · exact absurd h1 hp
        · exact h1
      rw [if_neg hp, hp']
      have hzz : z * star z = 1 := by
        have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star z
        rw [ht.2.2.1, map_one] at h
        exact h.symm
      have hne : ι' z ≠ 0 := fun h0 => by
        rw [h0, zero_pow (Nat.succ_ne_zero _)] at hpz
        exact zero_ne_one hpz
      have hs' : star z = z⁻¹ := eq_inv_of_mul_eq_one_right hzz
      rw [hs', map_inv₀]
      have e2 : ((-1 : ℤ) : ZMod h) * ν.2 = -ν.2 := by simp
      rw [e2]
      exact c2slomqmw5_inv_pow_val (by rw [hh]; exact hpz) hne ν.2

end CFSG.LocalAnalysis.WeakClosure81
