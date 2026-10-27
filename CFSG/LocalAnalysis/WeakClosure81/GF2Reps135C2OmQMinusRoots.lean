module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusChars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw8_inv_pow_val {k : Type*} [Field k] {M : ℕ} [NeZero M] {u : k}
    (hu : u ^ M = 1) (hne : u ≠ 0) (x : ZMod M) : (u⁻¹) ^ x.val = u ^ (-x).val := by
  have h1 : u ^ ((-x).val + x.val) = 1 := by
    have h2 : (((-x).val + x.val : ℕ) : ZMod M) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, neg_add_cancel]
    obtain ⟨j, hj⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h2
    rw [hj, pow_mul, hu, one_pow]
  rw [pow_add] at h1
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_left h1).symm

private theorem c2slomqmw8_starCoord_eq {K : Type*} [Field K] {b c : K} (x : ShortField b c) :
    starCoord x = fieldCoord (-(star x)) := by
  ext i
  fin_cases i <;> simp [starCoord, fieldCoord, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem omq_omMinus_exists_alpha_long {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ α : (SmallO8mCurtis.curtisDatum n hn hirr).H →* Kˣ,
      (∀ (g : (SmallO8mCurtis.curtisDatum n hn hirr).H) (s : K),
        (g : spinGroup (quadMinus n K b c)) *
            (minusFrame n b c).longRoot (succ_ne_of_lt n (k := ⟨0, by omega⟩)
              (by show 0 + 1 < n - 1; omega)).symm true false (.ofAdd s) *
            (g : spinGroup (quadMinus n K b c))⁻¹ =
          (minusFrame n b c).longRoot (succ_ne_of_lt n (k := ⟨0, by omega⟩)
            (by show 0 + 1 < n - 1; omega)).symm true false (.ofAdd (((α g)⁻¹ : Kˣ) * s))) ∧
      ∀ {k : Type} [Field k] (ι : K →+* k) (ι' : ShortField b c →+* k)
        (g : (SmallO8mCurtis.curtisDatum n hn hirr).H),
        ι (α g : K) = omqMinusWt n ι ι'
          ((Pi.single ⟨0, by omega⟩ (1 : ZMod (Nat.card Kˣ)) -
            Pi.single ⟨1, by omega⟩ (1 : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
            (0 : ZMod (Nat.card K + 1))) g := by
  classical
  let i0 : Fin (n - 1) := ⟨0, by omega⟩
  let i1 : Fin (n - 1) := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  refine ⟨omqMinusEntryHom hn hirr i0 * (omqMinusEntryHom hn hirr i1)⁻¹, ?_, ?_⟩
  · intro g s
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    have he : spinAction (quadMinus n K b c) g.1 ((minusFrame n b c).vec i1 true) =
        (t i1 : K) • (minusFrame n b c).vec i1 true := by
      rw [minusFrame_vec, minusVec_true]
      exact ht.1 i1
    have hf : spinAction (quadMinus n K b c) g.1 ((minusFrame n b c).vec i0 false) =
        (((t i0)⁻¹ : Kˣ) : K) • (minusFrame n b c).vec i0 false := by
      rw [minusFrame_vec, minusVec_false]
      exact ht.2.1 i0
    have key := (minusFrame n b c).conj_longRoot g.1 hi01.symm true false hi01.symm true false
      he hf s
    rw [key]
    congr 2
    have e0 : ((omqMinusEntryHom hn hirr i0 g : Kˣ) : K) = (t i0 : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    have e1 : ((omqMinusEntryHom hn hirr i1 g : Kˣ) : K) = (t i1 : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
    rw [e0, e1]
  · intro k _ ι ι' g
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
    have hpt : ∀ i, ι (t i : K) ^ Nat.card Kˣ = 1 := fun i => by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
    rw [omq_omMinus_wt_eq_of_toral ι ι' _ ht]
    have e0 : ((omqMinusEntryHom hn hirr i0 g : Kˣ) : K) = (t i0 : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    have e1 : ((omqMinusEntryHom hn hirr i1 g : Kˣ) : K) = (t i1 : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      map_mul, map_inv₀, e0, e1, ZMod.val_zero, pow_zero, mul_one]
    rw [← Finset.prod_subset (Finset.subset_univ {i0, i1}), Finset.prod_pair hi01]
    · have hne1 : ι (t i1 : K) ≠ 0 := fun h0 =>
        (t i1).ne_zero (ι.injective (h0.trans (map_zero ι).symm))
      have hu0 : ι (t i0 : K) ^ (Nat.card Kˣ) = 1 := hpt i0
      have hu1 : ι (t i1 : K) ^ (Nat.card Kˣ) = 1 := hpt i1
      have v0 : ((Pi.single i0 (1 : ZMod (Nat.card Kˣ)) - Pi.single i1 (1 : ZMod (Nat.card Kˣ)) :
          Fin (n - 1) → ZMod (Nat.card Kˣ)) i0) = 1 := by
        simp [Pi.single_apply, hi01]
      have v1 : ((Pi.single i0 (1 : ZMod (Nat.card Kˣ)) - Pi.single i1 (1 : ZMod (Nat.card Kˣ)) :
          Fin (n - 1) → ZMod (Nat.card Kˣ)) i1) = -1 := by
        simp [Pi.single_apply, hi01.symm]
      show ι (t i0 : K) * (ι (t i1 : K))⁻¹ = ι (t i0 : K) ^ ((Pi.single i0 (1 : ZMod _) -
        Pi.single i1 (1 : ZMod _) : Fin (n - 1) → ZMod (Nat.card Kˣ)) i0).val *
          ι (t i1 : K) ^ ((Pi.single i0 (1 : ZMod _) -
        Pi.single i1 (1 : ZMod _) : Fin (n - 1) → ZMod (Nat.card Kˣ)) i1).val
      rw [v0, v1]
      have h1 : ι (t i0 : K) ^ (1 : ZMod (Nat.card Kˣ)).val = ι (t i0 : K) := by
        rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hu0, pow_one]
      have h2 : ι (t i1 : K) ^ (-1 : ZMod (Nat.card Kˣ)).val = (ι (t i1 : K))⁻¹ := by
        have h3 := c2slomqmw8_inv_pow_val hu1 hne1 (1 : ZMod (Nat.card Kˣ))
        rw [← h3, ZMod.val_one_eq_one_mod,
          ← pow_eq_pow_mod 1 (by rw [inv_pow, hu1, inv_one]), pow_one]
      rw [h1, h2]
    · intro l _ hl
      have h1 : l ≠ (⟨0, by omega⟩ : Fin (n - 1)) := fun h => hl (by simp [i0, h])
      have h2 : l ≠ (⟨1, by omega⟩ : Fin (n - 1)) := fun h => hl (by simp [i1, h])
      simp [Pi.single_apply, h1, h2]

theorem omq_omMinus_exists_alpha_short {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    ∃ α : (SmallO8mCurtis.curtisDatum n hn hirr).H →* (ShortField b c)ˣ,
      (∀ (g : (SmallO8mCurtis.curtisDatum n hn hirr).H) (s : ShortField b c),
        (g : spinGroup (quadMinus n K b c)) * shortY n hirr i s *
            (g : spinGroup (quadMinus n K b c))⁻¹ =
          shortY n hirr i (((α g)⁻¹ : (ShortField b c)ˣ) * s)) ∧
      ∀ {k : Type} [Field k] (ι : K →+* k) (ι' : ShortField b c →+* k),
        (∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x) →
        ∀ g : (SmallO8mCurtis.curtisDatum n hn hirr).H,
          ι' (α g : ShortField b c) = omqMinusWt n ι ι'
            ((Pi.single i (1 : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
              (1 : ZMod (Nat.card K + 1))) g := by
  classical
  haveI := fact_shortField hirr
  refine ⟨(Units.map (algebraMap K (ShortField b c)).toMonoidHom).comp
    (omqMinusEntryHom hn hirr i) *
    omqMinusZHom hn hirr, ?_, ?_⟩
  · intro g s
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    have hzz : z * star z = 1 := by
      have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star z
      rw [ht.2.2.1, map_one] at h
      exact h.symm
    have hz' : z⁻¹ = star z := inv_eq_of_mul_eq_one_right hzz
    have hp : spinAction (quadMinus n K b c) g.1 (planeVec n (starCoord s)) =
        planeVec n (fieldCoord (z * -(star s))) := by
      rw [c2slomqmw8_starCoord_eq, ht.2.2.2]
    have key := conj_shortNegHom_of_fVec n hirr g.1 i (r := (((t i)⁻¹ : Kˣ) : K))
      (p := starCoord s) (q := fieldCoord (z * -(star s))) (ht.2.1 i) hp
    change g.1 * shortNegHom n hirr i (.ofAdd (starCoord s)) * g.1⁻¹ =
      shortNegHom n hirr i (.ofAdd (starCoord _))
    rw [key]
    congr 2
    have e0 : ((omqMinusEntryHom hn hirr i g : Kˣ) : K) = (t i : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    have hastar : ∀ x : K, star (algebraMap K (ShortField b c) x) =
        algebraMap K (ShortField b c) x := fun x => by
      ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    rw [← fieldCoord_algebraMap_mul, c2slomqmw8_starCoord_eq]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv_rev, omqMinusZHom_val, ht.omqMinusZ_eq]
    have hmap : ((Units.map (algebraMap K (ShortField b c)).toMonoidHom
        (omqMinusEntryHom hn hirr i g) : (ShortField b c)ˣ) : ShortField b c) =
          algebraMap K (ShortField b c) (t i : K) := by
      rw [Units.coe_map]
      show algebraMap K (ShortField b c) ((omqMinusEntryHom hn hirr i g : Kˣ) : K) = _
      rw [e0]
    rw [hmap, star_mul', star_mul', star_inv₀, star_inv₀, hastar, ← hz', inv_inv, map_inv₀]
    ring
  · intro k _ ι ι' hι' g
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
    haveI : NeZero (Nat.card K + 1) := ⟨Nat.succ_ne_zero _⟩
    have hpt : ι (t i : K) ^ Nat.card Kˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
    have hpz : ι' z ^ (Nat.card K + 1) = 1 := by
      rw [← map_pow, omq_shortField_pow_card_succ hirr, ht.2.2.1, map_one, map_one]
    rw [omq_omMinus_wt_eq_of_toral ι ι' _ ht]
    have e0 : ((omqMinusEntryHom hn hirr i g : Kˣ) : K) = (t i : K) := by
      rw [omqMinusEntryHom_val, ht.mat_inl_inl]
    have hmap : ((Units.map (algebraMap K (ShortField b c)).toMonoidHom
        (omqMinusEntryHom hn hirr i g) : (ShortField b c)ˣ) : ShortField b c) =
          algebraMap K (ShortField b c) (t i : K) := by
      rw [Units.coe_map]
      show algebraMap K (ShortField b c) ((omqMinusEntryHom hn hirr i g : Kˣ) : K) = _
      rw [e0]
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, omqMinusZHom_val,
      ht.omqMinusZ_eq, hmap, map_mul, hι']
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ZMod.val_one_eq_one_mod,
        ← pow_eq_pow_mod 1 hpt, ← pow_eq_pow_mod 1 hpz, pow_one, pow_one]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, ZMod.val_zero, pow_zero]

end CFSG.LocalAnalysis.WeakClosure81
