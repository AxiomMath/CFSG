module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusPlane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_H_toral {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    ∃ (t : Fin (n - 1) → Kˣ) (z : ShortField b c), OmqMinusToral n g t z := by
  haveI := fact_shortField hirr
  change g ∈ ⨆ j, minusTorus n hirr j at hg
  refine Subgroup.iSup_induction (minusTorus n hirr)
    (C := fun g => ∃ (t : Fin (n - 1) → Kˣ) (z : ShortField b c), OmqMinusToral n g t z) hg
    ?_ ?_ ?_
  · intro j x hx
    by_cases hj : j.val + 1 < n - 1
    · rw [minusTorus_of_lt n hirr hj] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨_, _, omq_omMinus_toral_longTorus hj a⟩
    · rw [minusTorus_of_not_lt n hirr hj] at hx
      obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr j).mp hx
      obtain ⟨u, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
      have hu : u ≠ 0 := fun h0 => ha (by rw [h0]; ext k; fin_cases k <;> rfl)
      exact ⟨_, _, by
        simpa [shortTorusHom_apply] using omq_omMinus_toral_shortTorusHom hirr j (Units.mk0 u hu)⟩
  · exact ⟨_, _, OmqMinusToral.one n⟩
  · rintro x y ⟨t, z, hx⟩ ⟨t', z', hy⟩
    exact ⟨_, _, hx.mul hy⟩

private theorem c2slomqmw2_shortTorusHom_mul_inv {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)}
    (hij : i ≠ j) (t : (ShortField b c)ˣ) :
    shortTorusHom n hirrQ i t * (shortTorusHom n hirrQ j t)⁻¹ =
      (minusFrame n b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t) := by
  have := fact_shortField hirrQ
  have hfaith : Function.Injective (spinAction (quadMinus n K b c)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← ker_spinMatrix, ker_spinMatrix_quadMinus_eq_bot hirrQ CharTwo.two_eq_zero]
  have ha := fieldCoord_ne_zero t.ne_zero
  have hn : QuadraticAlgebra.norm (t : ShortField b c) ≠ 0 :=
    (QuadraticAlgebra.norm_eq_zero_iff_eq_zero).not.mpr t.ne_zero
  rw [mul_inv_eq_iff_eq_mul]
  apply hfaith
  rw [shortTorusHom_apply, shortTorusHom_apply, map_mul]
  have hf : ∀ m r,
      spinAction (quadMinus n K b c) (shortTorusElt n hirrQ i (fieldCoord (t : ShortField b c)))
          (minusVec n m r) =
        (spinAction (quadMinus n K b c)
          ((minusFrame n b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t)) *
          spinAction (quadMinus n K b c)
            (shortTorusElt n hirrQ j (fieldCoord (t : ShortField b c)))) (minusVec n m r) := by
    intro m r
    rw [LinearEquiv.mul_apply, spinAction_shortTorusElt_minusVec n hirrQ i ha,
      spinAction_shortTorusElt_minusVec n hirrQ j ha, map_smul,
      ← minusFrame_vec, HypFrame.spinAction_longTorus_vec, minusFrame_vec, smul_smul]
    cases r <;> by_cases hmi : m = i <;> by_cases hmj : m = j
    all_goals simp [shortTorusScalar, longCoroot, hmi, hmj, hij, hij.symm,
      planeNorm_fieldCoord, Units.val_inv_eq_inv_val, hn] at *
  have hp : ∀ p,
      spinAction (quadMinus n K b c) (shortTorusElt n hirrQ i (fieldCoord (t : ShortField b c)))
          (planeVec n p) =
        (spinAction (quadMinus n K b c)
          ((minusFrame n b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t)) *
          spinAction (quadMinus n K b c)
            (shortTorusElt n hirrQ j (fieldCoord (t : ShortField b c)))) (planeVec n p) := by
    intro p
    rw [LinearEquiv.mul_apply, spinAction_shortTorusElt_planeVec n hirrQ i ha,
      spinAction_shortTorusElt_planeVec n hirrQ j ha, spinAction_longTorus_planeVec]
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun x a => ?_
  rw [show (Pi.single x a : Vm n K) = a • Pi.single x 1 by
    funext y
    by_cases h : y = x <;> simp [h]]
  simp only [LinearEquiv.coe_coe, map_smul]
  congr 1
  rcases x with m | m | s
  · exact hf m true
  · exact hf m false
  · have hs : (Pi.single (.inr (.inr s)) 1 : Vm n K) = planeVec n (Pi.single s 1) := by
      funext x
      rcases x with k | k | s' <;> simp [planeVec, Pi.single_apply]
    rw [hs, hp]

theorem omq_omMinus_torus_mem_H {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (∀ (i : Fin (n - 1)) (hi : i.val + 1 < n - 1) (a : Kˣ),
      (minusFrame n b c).longTorus (succ_ne_of_lt n hi) true false a ∈
        (SmallO8mCurtis.curtisDatum n hn hirr).H) ∧
    ∀ (i : Fin (n - 1)) (u : (ShortField b c)ˣ),
      shortTorusHom n hirr i u ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
  haveI := fact_shortField hirr
  have hlong : ∀ (i : Fin (n - 1)) (hi : i.val + 1 < n - 1) (a : Kˣ),
      (minusFrame n b c).longTorus (succ_ne_of_lt n hi) true false a ∈
        (SmallO8mCurtis.curtisDatum n hn hirr).H := by
    intro i hi a
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [minusTorus_of_lt n hirr hi]
    exact ⟨a, rfl⟩
  have hlast : ∀ i : Fin (n - 1), ¬ (i.val + 1 < n - 1) → ∀ u : (ShortField b c)ˣ,
      shortTorusHom n hirr i u ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
    intro i hi u
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [minusTorus_of_not_lt n hirr hi, ← range_shortTorusHom]
    exact ⟨u, rfl⟩
  refine ⟨hlong, fun i u => ?_⟩
  suffices h : ∀ d : ℕ, ∀ i : Fin (n - 1), n - 2 - i.val = d → ∀ u : (ShortField b c)ˣ,
      shortTorusHom n hirr i u ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H from h _ i rfl u
  intro d
  induction d with
  | zero =>
    intro i hi u
    exact hlast i (by omega) u
  | succ d ih =>
    intro i hi u
    have hlt : i.val + 1 < n - 1 := by omega
    have hnext := ih ⟨i.val + 1, hlt⟩ (by simp only; omega) u
    have heq := (mul_inv_eq_iff_eq_mul).mp
      (c2slomqmw2_shortTorusHom_mul_inv hirr (succ_ne_of_lt n hlt) u)
    rw [heq]
    exact mul_mem (hlong i hlt _) hnext

private theorem c2slomqmw2_exists_toral_t {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (t : Fin (n - 1) → Kˣ) :
    ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, OmqMinusToral n g t (1 : ShortField b c) := by
  haveI := fact_shortField hirr
  classical
  have hone : ∀ (i : Fin (n - 1)) (a : Kˣ), ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      OmqMinusToral n g (fun l => if l = i then a else 1) (1 : ShortField b c) := by
    intro i a
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (a : K)
    have hr0 : r ≠ 0 := by
      intro h0
      simp [h0] at hr
    let lam : Kˣ := Units.mk0 r hr0
    let u : (ShortField b c)ˣ := Units.map (algebraMap K (ShortField b c)).toMonoidHom lam
    refine ⟨shortTorusHom n hirr i u, (omq_omMinus_torus_mem_H hn hirr).2 i u, ?_⟩
    have h := omq_omMinus_toral_shortTorusHom hirr i u
    have e1 : (u : ShortField b c) / star (u : ShortField b c) = 1 := by
      have : star (u : ShortField b c) = (u : ShortField b c) := by
        change star (algebraMap K (ShortField b c) r) = algebraMap K (ShortField b c) r
        ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      rw [this, div_self u.ne_zero]
    have e2 : Units.map QuadraticAlgebra.norm u = a := by
      apply Units.ext
      change QuadraticAlgebra.norm (algebraMap K (ShortField b c) r) = a
      rw [QuadraticAlgebra.norm_algebraMap]
      simpa [pow_two] using hr.symm
    rw [e1, e2] at h
    exact h
  have hS : ∀ S : Finset (Fin (n - 1)), ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      OmqMinusToral n g (fun l => if l ∈ S then t l else 1) (1 : ShortField b c) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simpa using OmqMinusToral.one n⟩
    | insert i S hi ih =>
      obtain ⟨g, hgH, hg⟩ := ih
      obtain ⟨g', hg'H, hg'⟩ := hone i (t i)
      refine ⟨g' * g, mul_mem hg'H hgH, ?_⟩
      have h := hg'.mul hg
      rw [one_mul] at h
      convert h using 1
      funext l
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  obtain ⟨g, hgH, hg⟩ := hS Finset.univ
  exact ⟨g, hgH, by simpa using hg⟩

private theorem c2slomqmw2_exists_toral_z {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z : ShortField b c} (hz : QuadraticAlgebra.norm z = 1) :
    ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      OmqMinusToral n g (fun _ => 1) z := by
  haveI := fact_shortField hirr
  classical
  have hzz : z * star z = 1 := by
    have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star z
    rw [hz, map_one] at h
    exact h.symm
  obtain ⟨u, hu⟩ : ∃ u : (ShortField b c)ˣ,
      (u : ShortField b c) / star (u : ShortField b c) = z := by
    by_cases hz1 : z = 1
    · exact ⟨1, by simp [hz1]⟩
    · have hCh : CharP (ShortField b c) 2 :=
        charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
      have h1z : (1 + z) ≠ 0 := by
        intro h0
        apply hz1
        have e : z = -1 := by linear_combination h0
        rw [e, CharTwo.neg_eq]
      refine ⟨Units.mk0 (1 + z) h1z, ?_⟩
      show (1 + z) / star (1 + z) = z
      have hs : star (1 + z) ≠ 0 := star_ne_zero.mpr h1z
      rw [div_eq_iff hs, star_add, star_one]
      linear_combination (-1 : ShortField b c) * hzz
  let i₀ : Fin (n - 1) := ⟨0, by omega⟩
  have h0 := omq_omMinus_toral_shortTorusHom hirr i₀ u
  rw [hu] at h0
  obtain ⟨g₁, hg₁H, hg₁⟩ := c2slomqmw2_exists_toral_t hn hirr
    (fun l => if l = i₀ then (Units.map QuadraticAlgebra.norm u)⁻¹ else (1 : Kˣ))
  refine ⟨shortTorusHom n hirr i₀ u * g₁,
    mul_mem ((omq_omMinus_torus_mem_H hn hirr).2 i₀ u) hg₁H, ?_⟩
  have h := h0.mul hg₁
  rw [mul_one] at h
  convert h using 1
  funext l
  by_cases hl : l = i₀
  · simp [hl]
  · simp [hl]

theorem omq_omMinus_exists_toral {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (t : Fin (n - 1) → Kˣ)
    {z : ShortField b c} (hz : QuadraticAlgebra.norm z = 1) :
    ∃ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, OmqMinusToral n g t z := by
  obtain ⟨g, hgH, hg⟩ := c2slomqmw2_exists_toral_t hn hirr t
  obtain ⟨g', hg'H, hg'⟩ := c2slomqmw2_exists_toral_z hn hirr hz
  refine ⟨g * g', mul_mem hgH hg'H, ?_⟩
  have h := hg.mul hg'
  have e : (t * fun _ => (1 : Kˣ)) = t := by
    funext l
    simp
  rw [e, one_mul] at h
  exact h

theorem omq_omMinus_mem_H_of_toral {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ} {z : ShortField b c}
    (hg : OmqMinusToral n g t z) : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
  obtain ⟨g₀, hg₀H, hg₀⟩ := omq_omMinus_exists_toral hn hirr t hg.2.2.1
  suffices e : g = g₀ by rw [e]; exact hg₀H
  have hfaith : Function.Injective (spinAction (quadMinus n K b c)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← ker_spinMatrix, ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero]
  apply hfaith
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun x a => ?_
  rw [show (Pi.single x a : Vm n K) = a • Pi.single x 1 by
    funext y
    by_cases h : y = x <;> simp [h]]
  simp only [LinearEquiv.coe_coe, map_smul]
  congr 1
  rcases x with i | i | s
  · exact (hg.1 i).trans (hg₀.1 i).symm
  · exact (hg.2.1 i).trans (hg₀.2.1 i).symm
  · have hs : (Pi.single (.inr (.inr s)) 1 : Vm n K) = planeVec n (Pi.single s 1) := by
      funext x
      rcases x with k | k | s' <;> simp [planeVec, Pi.single_apply]
    obtain ⟨u, hu⟩ := exists_fieldCoord_eq (b := b) (c := c) (Pi.single s (1 : K))
    rw [hs, ← hu, hg.2.2.2 u, hg₀.2.2.2 u]

end CFSG.LocalAnalysis.WeakClosure81
