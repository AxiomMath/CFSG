module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw6_eq_of_pow_eq {k : Type*} [Field k] {M : ℕ} (x : kˣ)
    (hx : orderOf x = M) {a b : ℕ} (ha : a < M) (hb : b < M) (h : (x : k) ^ a = (x : k) ^ b) :
    a = b := by
  have h' : x ^ a = x ^ b := Units.ext (by simpa using h)
  have h1 := pow_eq_pow_iff_modEq.mp h'
  rw [hx] at h1
  exact Nat.ModEq.eq_of_lt_of_lt h1 ha hb

theorem omq_omMinus_wt_injective {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k]
    {m h : ℕ} (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k)
    (ι' : ShortField b c →+* k) {ν ν' : OmqMinusLat (n - 1) m h}
    (hν : ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      omqMinusWt n ι ι' ν g = omqMinusWt n ι ι' ν' g) : ν = ν' := by
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  haveI : NeZero h := ⟨by omega⟩
  refine Prod.ext (funext fun i => ?_) ?_
  ·
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hγord : orderOf γ = m := by
      rw [hm]; exact orderOf_eq_card_of_forall_mem_zpowers hγ
    let f : Kˣ →* kˣ := Units.map ι.toMonoidHom
    have hf : Function.Injective f := fun x y hxy => Units.ext (ι.injective (congrArg
      (fun u : kˣ => (u : k)) hxy))
    have hord : orderOf (f γ) = m := by
      have h1 := orderOf_injective f hf γ
      rw [hγord] at h1
      exact h1
    obtain ⟨g, hgH, hg⟩ := omq_omMinus_exists_toral hn hirr
      (Function.update (fun _ => (1 : Kˣ)) i γ) (z := 1) (by simp)
    have h1 := hν g hgH
    rw [omq_omMinus_wt_eq_of_toral ι ι' ν hg, omq_omMinus_wt_eq_of_toral ι ι' ν' hg] at h1
    have hprod : ∀ μ : OmqMinusLat (n - 1) m h, ∏ l : Fin (n - 1),
        ι ((Function.update (fun _ => (1 : Kˣ)) i γ l : Kˣ) : K) ^ (μ.1 l).val =
          ι (γ : K) ^ (μ.1 i).val := by
      intro μ
      rw [Finset.prod_eq_single i]
      · simp
      · intro l _ hl
        simp [Function.update_of_ne hl]
      · simp
    rw [hprod ν, hprod ν', map_one, one_pow, one_pow, mul_one, mul_one] at h1
    have := c2slomqmw6_eq_of_pow_eq (f γ) hord (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact ZMod.val_injective _ this
  ·
    obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := (ShortField b c)ˣ)
    have hcard := omq_omMinus_card_shortField_units hirr
    rw [← hm, ← hh] at hcard
    have hword : orderOf w = m * h := by
      rw [← hcard]; exact orderOf_eq_card_of_forall_mem_zpowers hw
    have hz0 : orderOf (w ^ m) = h := by
      rw [orderOf_pow' w (NeZero.ne m), hword, Nat.gcd_eq_right (Dvd.intro _ rfl),
        Nat.mul_div_cancel_left h (Nat.pos_of_ne_zero (NeZero.ne m))]
    have hnorm : QuadraticAlgebra.norm (((w ^ m : (ShortField b c)ˣ)) : ShortField b c) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow]
      have hn0 : QuadraticAlgebra.norm (w : ShortField b c) ≠ 0 :=
        (QuadraticAlgebra.norm_eq_zero_iff_eq_zero).not.mpr w.ne_zero
      have h1 : (Units.mk0 (QuadraticAlgebra.norm (w : ShortField b c)) hn0) ^ m = 1 := by
        rw [hm]; exact pow_card_eq_one'
      simpa using congrArg (fun u : Kˣ => (u : K)) h1
    obtain ⟨g, hgH, hg⟩ := omq_omMinus_exists_toral hn hirr (fun _ => (1 : Kˣ))
      (z := ((w ^ m : (ShortField b c)ˣ) : ShortField b c)) hnorm
    have h1 := hν g hgH
    rw [omq_omMinus_wt_eq_of_toral ι ι' ν hg, omq_omMinus_wt_eq_of_toral ι ι' ν' hg] at h1
    simp only [Units.val_one, map_one, one_pow, Finset.prod_const_one, one_mul] at h1
    let f' : (ShortField b c)ˣ →* kˣ := Units.map ι'.toMonoidHom
    have hf' : Function.Injective f' := fun x y hxy => Units.ext (ι'.injective (congrArg
      (fun u : kˣ => (u : k)) hxy))
    have hord' : orderOf (f' (w ^ m)) = h := by
      have h2 := orderOf_injective f' hf' (w ^ m)
      rw [hz0] at h2
      exact h2
    have := c2slomqmw6_eq_of_pow_eq (f' (w ^ m)) hord' (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact ZMod.val_injective _ this

end CFSG.LocalAnalysis.WeakClosure81
