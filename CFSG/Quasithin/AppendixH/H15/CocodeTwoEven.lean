module

public import CFSG.Quasithin.AppendixH.H16.OmegaPlus6

public section

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH

@[expose] def evBlkSet : Fin 6 → Finset (Fin 8) :=
  ![({0, 1, 2, 3} : Finset (Fin 8)), {0, 1, 2, 4}, {0, 1, 5, 6}, {0, 1, 5, 7}, {0, 2, 6, 7},
    {0, 3, 4, 5}]

@[expose] def evBlk (i : Fin 6) (p : Fin 8) : ZMod 2 := if p ∈ evBlkSet i then 1 else 0

@[expose] def evVec (x : Fin 6 → ZMod 2) (p : Fin 8) : ZMod 2 := ∑ i, x i * evBlk i p

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem evBlk_sum_all : ∀ i : Fin 6, ∑ p, evBlk i p = 0 := by
  decide +kernel

private theorem evVec_inj_all :
    ∀ x y : Fin 6 → ZMod 2,
      ((∀ p, evVec x p + evVec y p = 0) ∨
        (∀ p, evVec x p + evVec y p = 1)) → x = y := by
  decide +kernel

private theorem exists_evVec_all :
    ∀ Z : Fin 8 → ZMod 2, (∑ p, Z p = 0) →
      ∃ x : Fin 6 → ZMod 2, evVec x = Z ∨ evVec x = Z + 1 := by
  decide +kernel

private theorem ind_pair_sum_all :
    ∀ i j : Fin 8, i ≠ j →
      ∑ p, (if p = i ∨ p = j then (1 : ZMod 2) else 0) = 0 := by
  decide +kernel

private theorem pair_indicator_eq_sets_all :
    ∀ (i j k l : Fin 8), i ≠ j → k ≠ l →
      ((∀ p, (if p = i ∨ p = j then (1 : ZMod 2) else 0) +
          (if p = k ∨ p = l then (1 : ZMod 2) else 0) = 0) ∨
        (∀ p, (if p = i ∨ p = j then (1 : ZMod 2) else 0) +
          (if p = k ∨ p = l then (1 : ZMod 2) else 0) = 1)) →
      ({i, j} : Finset (Fin 8)) = {k, l} := by
  decide +kernel

private theorem ind_pair_eq_of_sets_all :
    ∀ (i j k l : Fin 8), ({i, j} : Finset (Fin 8)) = {k, l} →
      (fun p => if p = i ∨ p = j then (1 : ZMod 2) else 0) =
        (fun p => if p = k ∨ p = l then (1 : ZMod 2) else 0) := by
  decide +kernel

theorem evVec_add (x y : Fin 6 → ZMod 2) : evVec (x + y) = evVec x + evVec y := by
  funext p
  unfold evVec
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem evVec_even (x : Fin 6 → ZMod 2) : ∑ p, evVec x p = 0 := by
  unfold evVec
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  simp [evBlk_sum_all]

theorem evVec_inj {x y : Fin 6 → ZMod 2}
    (h : (∀ p, evVec x p + evVec y p = 0) ∨ (∀ p, evVec x p + evVec y p = 1)) : x = y :=
  evVec_inj_all x y h

theorem exists_evVec {Z : Fin 8 → ZMod 2} (hZ : ∑ p, Z p = 0) :
    ∃ x : Fin 6 → ZMod 2, evVec x = Z ∨ evVec x = Z + 1 :=
  exists_evVec_all Z hZ

@[expose, irreducible] noncomputable def evDec (Z : Fin 8 → ZMod 2) : Fin 6 → ZMod 2 := by
  classical
  exact if h : ∃ x : Fin 6 → ZMod 2, evVec x = Z ∨ evVec x = Z + 1 then h.choose else 0

theorem evVec_evDec {Z : Fin 8 → ZMod 2} (hZ : ∑ p, Z p = 0) :
    evVec (evDec Z) = Z ∨ evVec (evDec Z) = Z + 1 := by
  unfold evDec
  rw [dif_pos (exists_evVec hZ)]
  exact (exists_evVec hZ).choose_spec

theorem evDec_eq {Z : Fin 8 → ZMod 2} {x : Fin 6 → ZMod 2} (hZ : ∑ p, Z p = 0)
    (h : evVec x = Z ∨ evVec x = Z + 1) : evDec Z = x := by
  let y : Fin 6 → ZMod 2 := evDec Z
  have hy : evVec y = Z ∨ evVec y = Z + 1 := evVec_evDec hZ
  have hsum : (∀ p, evVec y p + evVec x p = 0) ∨
      (∀ p, evVec y p + evVec x p = 1) := by
    rcases hy with hy | hy <;> rcases h with hx | hx
    · left
      intro p
      rw [hy, hx]
      exact CharTwo.add_self_eq_zero (Z p)
    · right
      intro p
      rw [hy, hx]
      simp only [Pi.add_apply, Pi.one_apply]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · right
      intro p
      rw [hy, hx]
      simp only [Pi.add_apply, Pi.one_apply]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    · left
      intro p
      rw [hy, hx]
      simp only [Pi.add_apply, Pi.one_apply]
      exact CharTwo.add_self_eq_zero (Z p + 1)
  have hyx : y = x := evVec_inj (x := y) (y := x) hsum
  exact hyx

theorem evDec_add {Z Z' : Fin 8 → ZMod 2} (hZ : ∑ p, Z p = 0) (hZ' : ∑ p, Z' p = 0) :
    evDec (Z + Z') = evDec Z + evDec Z' := by
  have hZsum : ∑ p, (Z + Z') p = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hZ, hZ', add_zero]
  have hx : evVec (evDec Z) = Z ∨ evVec (evDec Z) = Z + 1 := evVec_evDec hZ
  have hx' : evVec (evDec Z') = Z' ∨ evVec (evDec Z') = Z' + 1 := evVec_evDec hZ'
  have h : evVec (evDec Z + evDec Z') = Z + Z' ∨
      evVec (evDec Z + evDec Z') = (Z + Z') + 1 := by
    rw [evVec_add]
    rcases hx with hx | hx <;> rcases hx' with hx' | hx'
    · left
      rw [hx, hx']
    · right
      rw [hx, hx']
      abel
    · right
      rw [hx, hx']
      abel
    · left
      rw [hx, hx']
      funext p
      simp only [Pi.add_apply, Pi.one_apply]
      calc (Z p + 1) + (Z' p + 1) = (Z p + Z' p) + (1 + 1) := by abel
        _ = Z p + Z' p := by
            rw [CharTwo.add_self_eq_zero (1 : ZMod 2), add_zero]
  exact evDec_eq hZsum h

@[expose] def evWt (Z : Fin 8 → ZMod 2) : ℕ := (Finset.univ.filter fun p => Z p = 1).card

private theorem qPlus6_eq_evWt_all :
    ∀ x : Fin 6 → ZMod 2, qPlus6 x = ((evWt (evVec x) / 2 : ℕ) : ZMod 2) := by
  decide +kernel

private theorem evWt_ind_pair_all :
    ∀ i j : Fin 8, i ≠ j →
      evWt (fun p => if p = i ∨ p = j then (1 : ZMod 2) else 0) = 2 := by
  decide +kernel

private theorem evWt_cast_sum_all (Z : Fin 8 → ZMod 2) :
    ((evWt Z : ℕ) : ZMod 2) = ∑ p, Z p := by
  revert Z
  decide +kernel

private theorem evWt_comp (Z : Fin 8 → ZMod 2) (σ : Equiv.Perm (Fin 8)) :
    evWt (fun p => Z (σ.symm p)) = evWt Z := by
  unfold evWt
  refine Finset.card_bij (fun p _ => σ.symm p) ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p₁ _ p₂ _ h
    exact σ.symm.injective h
  · intro q hq
    refine ⟨σ q, ?_, ?_⟩
    · simpa using hq
    · simp

private theorem evWt_add_one (Z : Fin 8 → ZMod 2) : evWt (Z + 1) = 8 - evWt Z := by
  have hiff : ∀ p, (Z + 1) p = 1 ↔ Z p = 0 := by
    intro p
    change Z p + 1 = 1 ↔ Z p = 0
    rcases zmod2_eq_zero_or_one (Z p) with h | h <;> rw [h] <;> decide
  have hset : (Finset.univ.filter fun p => (Z + 1) p = 1) =
      (Finset.univ.filter fun p => Z p = 0) := by
    apply Finset.filter_congr
    intro p _
    exact hiff p
  have hnot : (Finset.univ.filter fun p => ¬ Z p = 1) =
      (Finset.univ.filter fun p => Z p = 0) := by
    apply Finset.filter_congr
    intro p _
    rcases zmod2_eq_zero_or_one (Z p) with h | h <;> simp [h]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 8))) (p := fun p => Z p = 1)
  rw [hnot, Finset.card_univ, Fintype.card_fin] at hsplit
  unfold evWt
  rw [hset]
  omega

private theorem zmod2_half_eq_half_complement {w : ℕ} (hw8 : w ≤ 8) (heven : Even w) :
    ((w / 2 : ℕ) : ZMod 2) = (((8 - w) / 2 : ℕ) : ZMod 2) := by
  obtain ⟨k, rfl⟩ := heven
  have hk : k ≤ 4 := by omega
  have h2 : 8 - (k + k) = 2 * (4 - k) := by omega
  have h1 : (k + k) / 2 = k := by
    rw [← two_mul]
    exact Nat.mul_div_cancel_left k (by norm_num)
  rw [h1, h2, Nat.mul_div_cancel_left (4 - k) (by norm_num)]
  interval_cases k <;> decide

theorem qPlus6_eq_evWt (x : Fin 6 → ZMod 2) :
    qPlus6 x = ((evWt (evVec x) / 2 : ℕ) : ZMod 2) :=
  qPlus6_eq_evWt_all x

@[expose] noncomputable def evAct (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    Fin 6 → ZMod 2 :=
  evDec fun p => evVec x (σ.symm p)

theorem evVec_evAct (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    evVec (evAct σ x) = (fun p => evVec x (σ.symm p)) ∨
      evVec (evAct σ x) = (fun p => evVec x (σ.symm p)) + 1 := by
  unfold evAct
  refine evVec_evDec ?_
  simpa using (Equiv.sum_comp σ.symm (fun q => evVec x q)).trans (evVec_even x)

theorem evAct_add (σ : Equiv.Perm (Fin 8)) (x y : Fin 6 → ZMod 2) :
    evAct σ (x + y) = evAct σ x + evAct σ y := by
  unfold evAct
  rw [evVec_add]
  have hx : ∑ p, evVec x (σ.symm p) = 0 := by
    simpa using (Equiv.sum_comp σ.symm (fun q => evVec x q)).trans (evVec_even x)
  have hy : ∑ p, evVec y (σ.symm p) = 0 := by
    simpa using (Equiv.sum_comp σ.symm (fun q => evVec y q)).trans (evVec_even y)
  rw [show (fun p => (evVec x + evVec y) (σ.symm p)) =
      (fun p => evVec x (σ.symm p)) + (fun p => evVec y (σ.symm p)) by
    funext p
    simp only [Pi.add_apply, Pi.one_apply]]
  exact evDec_add hx hy

theorem evAct_one (x : Fin 6 → ZMod 2) : evAct 1 x = x := by
  unfold evAct
  have harg : (fun p => evVec x ((1 : Equiv.Perm (Fin 8)).symm p)) = evVec x := by
    funext p
    rfl
  rw [harg]
  exact evDec_eq (evVec_even x) (Or.inl rfl)

private theorem perm_symm_mul (σ τ : Equiv.Perm (Fin 8)) :
    (σ * τ).symm = τ.symm * σ.symm := by
  ext p
  rfl

theorem evAct_mul (σ τ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    evAct (σ * τ) x = evAct σ (evAct τ x) := by
  let W : Fin 8 → ZMod 2 := fun p => evVec x ((σ * τ).symm p)
  have hW : ∑ p, W p = 0 := by
    simpa [W] using
      (Equiv.sum_comp (σ * τ).symm (fun q => evVec x q)).trans (evVec_even x)
  have key : evVec (evAct σ (evAct τ x)) = W ∨
      evVec (evAct σ (evAct τ x)) = W + 1 := by
    rcases evVec_evAct σ (evAct τ x) with hσ | hσ
    · rcases evVec_evAct τ x with hτ | hτ
      · left
        rw [hσ, hτ]
        funext p
        simp [W, Pi.add_apply, Equiv.Perm.mul_apply, perm_symm_mul]
      · right
        rw [hσ, hτ]
        funext p
        simp [W, Pi.add_apply, Equiv.Perm.mul_apply, perm_symm_mul]
    · rcases evVec_evAct τ x with hτ | hτ
      · right
        rw [hσ, hτ]
        funext p
        simp [W, Pi.add_apply, Equiv.Perm.mul_apply, perm_symm_mul]
      · left
        rw [hσ, hτ]
        funext p
        simp [W, Pi.add_apply, Equiv.Perm.mul_apply, perm_symm_mul, add_assoc,
          CharTwo.add_self_eq_zero]
  change evDec W = evAct σ (evAct τ x)
  exact evDec_eq hW key

theorem evAct_inv_mul (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    evAct σ⁻¹ (evAct σ x) = x := by
  rw [← evAct_mul, inv_mul_cancel, evAct_one]

theorem evAct_mul_inv (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    evAct σ (evAct σ⁻¹ x) = x := by
  rw [← evAct_mul, mul_inv_cancel, evAct_one]

@[expose] noncomputable def evActEquiv (σ : Equiv.Perm (Fin 8)) :
    (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun := evAct σ
  invFun := evAct σ⁻¹
  left_inv := evAct_inv_mul σ
  right_inv := evAct_mul_inv σ
  map_add' := evAct_add σ

@[expose] noncomputable def evActHom :
    Equiv.Perm (Fin 8) →* MulAut (Multiplicative (Fin 6 → ZMod 2)) where
  toFun σ := AddEquiv.toMultiplicative (evActEquiv σ)
  map_one' := MulEquiv.ext fun v => by
    apply Multiplicative.toAdd.injective
    exact evAct_one (Multiplicative.toAdd v)
  map_mul' σ τ := MulEquiv.ext fun v => by
    apply Multiplicative.toAdd.injective
    exact evAct_mul σ τ (Multiplicative.toAdd v)

theorem evActHom_apply (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    Multiplicative.toAdd (evActHom σ (Multiplicative.ofAdd x)) = evAct σ x := by
  rfl

theorem qPlus6_evAct (σ : Equiv.Perm (Fin 8)) (x : Fin 6 → ZMod 2) :
    qPlus6 (evAct σ x) = qPlus6 x := by
  let Z : Fin 8 → ZMod 2 := evVec x
  have hwcast : ((evWt Z : ℕ) : ZMod 2) = 0 := by
    rw [evWt_cast_sum_all, evVec_even x]
  have hwle : evWt Z ≤ 8 := by
    unfold evWt
    simpa using Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin 8))) (p := fun p => Z p = 1)
  have heven : Even (evWt Z) := by
    rw [even_iff_two_dvd]
    exact (ZMod.natCast_eq_zero_iff (evWt Z) 2).1 hwcast
  rw [qPlus6_eq_evWt, qPlus6_eq_evWt]
  rcases evVec_evAct σ x with h | h
  · have hw : evWt (evVec (evAct σ x)) = evWt Z := by
      rw [h]
      exact evWt_comp Z σ
    rw [hw]
  · have hw : evWt (evVec (evAct σ x)) = 8 - evWt Z := by
      rw [h, evWt_add_one, evWt_comp Z σ]
    rw [hw]
    exact (zmod2_half_eq_half_complement hwle heven).symm

@[expose] noncomputable def evPair (i j : Fin 8) : Fin 6 → ZMod 2 :=
  evDec fun p => if p = i ∨ p = j then 1 else 0

theorem evVec_evPair {i j : Fin 8} (hij : i ≠ j) :
    evVec (evPair i j) = (fun p => if p = i ∨ p = j then 1 else 0) ∨
      evVec (evPair i j) = (fun p => if p = i ∨ p = j then 1 else 0) + 1 := by
  unfold evPair
  exact evVec_evDec (ind_pair_sum_all i j hij)

theorem qPlus6_evPair {i j : Fin 8} (hij : i ≠ j) : qPlus6 (evPair i j) = 1 := by
  rw [qPlus6_eq_evWt]
  rcases evVec_evPair hij with h | h
  · rw [h, evWt_ind_pair_all i j hij]
    decide
  · rw [h, evWt_add_one, evWt_ind_pair_all i j hij]
    decide

theorem evAct_evPair (σ : Equiv.Perm (Fin 8)) {i j : Fin 8} (hij : i ≠ j) :
    evAct σ (evPair i j) = evPair (σ i) (σ j) := by
  let A : Fin 8 → ZMod 2 := fun p => if p = i ∨ p = j then 1 else 0
  let B : Fin 8 → ZMod 2 := fun p => if p = σ i ∨ p = σ j then 1 else 0
  let Z : Fin 8 → ZMod 2 := fun p => evVec (evPair i j) (σ.symm p)
  have hZ : ∑ p, Z p = 0 := by
    simpa [Z] using
      (Equiv.sum_comp σ.symm (fun q => evVec (evPair i j) q)).trans
        (evVec_even (evPair i j))
  have hσij : σ i ≠ σ j := fun h => hij (σ.injective h)
  have hperm : (fun p => A (σ.symm p)) = B := by
    funext p
    simp only [A, B, Equiv.symm_apply_eq]
  have key : evVec (evPair (σ i) (σ j)) = Z ∨
      evVec (evPair (σ i) (σ j)) = Z + 1 := by
    rcases evVec_evPair hij with hA | hA
    · have hZeq : Z = B := by
        funext p
        simp only [Z, hA]
        simpa [A] using congrFun hperm p
      rcases evVec_evPair hσij with hB | hB
      · left
        rw [hB]
        simpa [B] using hZeq.symm
      · right
        rw [hB, hZeq]
    · have hZeq : Z = B + 1 := by
        funext p
        simp only [Z, hA, Pi.add_apply, Pi.one_apply]
        simpa [A] using congrFun hperm p
      rcases evVec_evPair hσij with hB | hB
      · right
        rw [hB, hZeq]
        funext p
        simp [B, Pi.add_apply, Pi.one_apply, add_assoc, CharTwo.add_self_eq_zero]
      · left
        rw [hB, hZeq]
  have hdec : evDec Z = evPair (σ i) (σ j) := evDec_eq hZ key
  unfold evAct
  simpa [Z] using hdec

theorem evPair_eq_iff {i j k l : Fin 8} (hij : i ≠ j) (hkl : k ≠ l) :
    evPair i j = evPair k l ↔ ({i, j} : Finset (Fin 8)) = {k, l} := by
  constructor
  · intro h
    let A : Fin 8 → ZMod 2 := fun p => if p = i ∨ p = j then 1 else 0
    let B : Fin 8 → ZMod 2 := fun p => if p = k ∨ p = l then 1 else 0
    have hvec : evVec (evPair i j) = evVec (evPair k l) := congrArg evVec h
    have hA := evVec_evPair hij
    have hB := evVec_evPair hkl
    let C : Fin 8 → ZMod 2 := evVec (evPair k l)
    have hA' : A = C ∨ A = C + 1 := by
      change (fun p => if p = i ∨ p = j then 1 else 0) = C ∨
        (fun p => if p = i ∨ p = j then 1 else 0) = C + 1
      rcases hA with hA | hA
      · left
        rw [← hA, hvec]
      · right
        change (fun p => if p = i ∨ p = j then 1 else 0) = evVec (evPair k l) + 1
        rw [← hvec, hA]
        funext p
        simp only [Pi.add_apply, Pi.one_apply]
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hB' : B = C ∨ B = C + 1 := by
      change (fun p => if p = k ∨ p = l then 1 else 0) = C ∨
        (fun p => if p = k ∨ p = l then 1 else 0) = C + 1
      rcases hB with hB | hB
      · left
        rw [← hB]
      · right
        change (fun p => if p = k ∨ p = l then 1 else 0) = evVec (evPair k l) + 1
        rw [hB]
        funext p
        simp only [Pi.add_apply, Pi.one_apply]
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hAB : (∀ p, A p + B p = 0) ∨ (∀ p, A p + B p = 1) := by
      rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
      · left
        intro p
        rw [hA', hB']
        exact CharTwo.add_self_eq_zero (C p)
      · right
        intro p
        rw [hA', hB']
        simp only [Pi.add_apply, Pi.one_apply]
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      · right
        intro p
        rw [hA', hB']
        simp only [Pi.add_apply, Pi.one_apply]
        rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
      · left
        intro p
        rw [hA', hB']
        exact CharTwo.add_self_eq_zero (C p + 1)
    exact pair_indicator_eq_sets_all i j k l hij hkl hAB
  · intro h
    have hfun := ind_pair_eq_of_sets_all i j k l h
    unfold evPair
    rw [hfun]

theorem evActHom_injective : Function.Injective evActHom := by
  intro σ τ h
  let ρ : Equiv.Perm (Fin 8) := σ⁻¹ * τ
  have hρ1 : evActHom ρ = 1 := by
    rw [show ρ = σ⁻¹ * τ from rfl, map_mul, map_inv, h, inv_mul_cancel]
  have hfix : ∀ x : Fin 6 → ZMod 2, evAct ρ x = x := by
    intro x
    have hx := congrArg
      (fun f : MulAut (Multiplicative (Fin 6 → ZMod 2)) =>
        Multiplicative.toAdd (f (Multiplicative.ofAdd x))) hρ1
    simpa [evActHom_apply] using hx
  have hstab : ∀ i j : Fin 8, i ≠ j → ({ρ i, ρ j} : Finset (Fin 8)) = {i, j} := by
    intro i j hij
    have hρij : ρ i ≠ ρ j := fun hh => hij (ρ.injective hh)
    have heq : evPair (ρ i) (ρ j) = evPair i j := by
      rw [← evAct_evPair ρ hij]
      exact hfix (evPair i j)
    exact (evPair_eq_iff hρij hij).1 heq
  have hfixpoint : ∀ i : Fin 8, ρ i = i := by
    intro i
    have hcard : 1 < (Finset.univ.erase i).card := by simp
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    have hsetij := hstab i j (Ne.symm hji)
    have hsetik := hstab i k (Ne.symm hki)
    have hmem1 : ρ i ∈ ({i, j} : Finset (Fin 8)) := by
      rw [← hsetij]
      simp
    have hmem2 : ρ i ∈ ({i, k} : Finset (Fin 8)) := by
      rw [← hsetik]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    rcases hmem1 with h | h
    · exact h
    · rcases hmem2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hjk
  have hρeq : ρ = 1 := Equiv.ext hfixpoint
  have hτσ : τ = σ := by
    calc τ = σ * ρ := by simp [ρ, mul_assoc]
      _ = σ := by rw [hρeq, mul_one]
  exact hτσ.symm

theorem map_alternatingGroup_evActHom :
    (alternatingGroup (Fin 8)).map evActHom = omegaN 6 qPlus6 := by
  apply CFSG.ASVolI.H16.eq_omegaN_qPlus6_of_card
  · intro g hg x
    rcases Subgroup.mem_map.mp hg with ⟨σ, -, rfl⟩
    rw [evActHom_apply]
    exact qPlus6_evAct σ x
  · rw [Subgroup.card_map_of_injective evActHom_injective]
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]

end CFSG.ASVolI.AppH
