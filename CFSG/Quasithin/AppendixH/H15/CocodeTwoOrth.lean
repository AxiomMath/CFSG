module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoEven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin

private def ind2 (i j : Fin 8) : Fin 8 → ZMod 2 :=
  fun p => if p = i ∨ p = j then 1 else 0

private def allOnes8 : Fin 8 → ZMod 2 := fun _ => 1

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem ind2_sum_all : ∀ i j : Fin 8, i ≠ j → ∑ p, ind2 i j p = 0 := by
  decide +kernel

private theorem exists_ind2_of_qPlus6_all :
    ∀ x : Fin 6 → ZMod 2, qPlus6 x = 1 →
      ∃ i j : Fin 8, i ≠ j ∧ (evVec x = ind2 i j ∨ evVec x = ind2 i j + 1) := by
  decide +kernel

private theorem evDec_zero : evDec (0 : Fin 8 → ZMod 2) = 0 := by
  apply evDec_eq (Z := 0) (x := 0)
  · simp
  · left
    funext p
    simp [evVec]

private theorem sum_ind2_erase_zero (p : Fin 8) :
    ∑ q ∈ (Finset.univ.erase (0 : Fin 8)), ind2 0 q p = 1 := by
  fin_cases p <;> decide +kernel

private theorem sum_ind2_erase_zero_fun :
    (∑ q ∈ (Finset.univ.erase (0 : Fin 8)), ind2 0 q) = allOnes8 := by
  funext p
  rw [Finset.sum_apply, sum_ind2_erase_zero p]
  rfl

private theorem evDec_allOnes : evDec allOnes8 = 0 := by
  apply evDec_eq (Z := allOnes8) (x := 0)
  · decide +kernel
  · right
    funext p
    fin_cases p <;> decide +kernel

private theorem evDec_sum {ι : Type*} (s : Finset ι) :
    ∀ Z : ι → Fin 8 → ZMod 2, (∀ i ∈ s, ∑ p, Z i p = 0) →
      evDec (∑ i ∈ s, Z i) = ∑ i ∈ s, evDec (Z i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro Z _
      rw [Finset.sum_empty, Finset.sum_empty]
      exact evDec_zero
  | insert a s ha ih =>
      intro Z hZ
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hZa : ∑ p, Z a p = 0 := hZ a (Finset.mem_insert_self a s)
      have hZs : ∑ p, (∑ i ∈ s, Z i) p = 0 := by
        simp only [Finset.sum_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_eq_zero fun i hi => hZ i (Finset.mem_insert_of_mem hi)
      rw [evDec_add hZa hZs, ih Z fun i hi => hZ i (Finset.mem_insert_of_mem hi)]

private theorem sum_evPair_erase_zero :
    (∑ q ∈ (Finset.univ.erase (0 : Fin 8)), evPair 0 q) = 0 := by
  have h := evDec_sum (s := Finset.univ.erase (0 : Fin 8))
    (Z := fun q p => if p = 0 ∨ p = q then (1 : ZMod 2) else 0)
    (by
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      simpa [ind2] using ind2_sum_all 0 q (Ne.symm hq0))
  change (∑ q ∈ (Finset.univ.erase (0 : Fin 8)),
    evDec (fun p => if p = 0 ∨ p = q then (1 : ZMod 2) else 0)) = 0
  rw [← h]
  change evDec (∑ q ∈ (Finset.univ.erase (0 : Fin 8)), ind2 0 q) = 0
  rw [sum_ind2_erase_zero_fun, evDec_allOnes]

private theorem ofAdd_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 6 → ZMod 2) :
    Multiplicative.ofAdd (∑ i ∈ s, f i) =
      ∏ i ∈ s, Multiplicative.ofAdd (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [show Multiplicative.ofAdd (f a + ∑ i ∈ s, f i) =
          Multiplicative.ofAdd (f a) * Multiplicative.ofAdd (∑ i ∈ s, f i) from rfl]
      rw [ih]

private theorem mult_sq_one (v : Multiplicative (Fin 6 → ZMod 2)) : v ^ 2 = 1 := by
  revert v
  decide +kernel

private def qB : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4)
    (by intro x x' y; simp only [Pi.add_apply]; ring)
    (by intro c x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y y'; simp only [Pi.add_apply]; ring)
    (by intro c x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem qB_symm (x y : Fin 6 → ZMod 2) : qB x y = qB y x := by
  simp only [qB, LinearMap.mk₂_apply]
  ring

private theorem qB_nondeg_left_all :
    ∀ x : Fin 6 → ZMod 2, (∀ y, qB x y = 0) → x = 0 := by
  decide +kernel

private theorem qB_nondegenerate : qB.Nondegenerate :=
  ⟨qB_nondeg_left_all, fun y hy => qB_nondeg_left_all y fun x => by
    rw [qB_symm]; exact hy x⟩

private theorem qB_eq_polar (x y : Fin 6 → ZMod 2) :
    qB x y = qPlus6 (x + y) + qPlus6 x + qPlus6 y := by
  simp only [qB, LinearMap.mk₂_apply, qPlus6, Pi.add_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_mul, add_zero, zero_add]

theorem exists_evPair_of_qPlus6 {x : Fin 6 → ZMod 2} (hx : qPlus6 x = 1) :
    ∃ p q : Fin 8, p ≠ q ∧ evPair p q = x := by
  obtain ⟨i, j, hij, h | h⟩ := exists_ind2_of_qPlus6_all x hx
  · exact ⟨i, j, hij, evDec_eq (Z := ind2 i j) (ind2_sum_all i j hij) (Or.inl h)⟩
  · exact ⟨i, j, hij, evDec_eq (Z := ind2 i j) (ind2_sum_all i j hij) (Or.inr h)⟩

theorem card_le_eight_of_singular {I : Subgroup (Multiplicative (Fin 6 → ZMod 2))}
    (h : ∀ x ∈ I, qPlus6 (Multiplicative.toAdd x) = 0) : Nat.card I ≤ 8 := by
  let W : Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
    { carrier := {y | Multiplicative.ofAdd y ∈ I}
      zero_mem' := by simpa using I.one_mem
      add_mem' := by
        intro x y hx hy
        show Multiplicative.ofAdd x * Multiplicative.ofAdd y ∈ I
        exact I.mul_mem hx hy
      smul_mem' := by
        intro c x hx
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simpa using I.one_mem
        · simpa using hx }
  have hcardWI : Nat.card W = Nat.card I := by
    refine Nat.card_congr ?_
    exact { toFun := fun y => ⟨Multiplicative.ofAdd (y : Fin 6 → ZMod 2), y.2⟩
            invFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 2)), x.2⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext rfl }
  have hle : W ≤ qB.orthogonal W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hxI : Multiplicative.ofAdd x ∈ I := hx
    have hyI : Multiplicative.ofAdd y ∈ I := hy
    have hxyI : Multiplicative.ofAdd (x + y) ∈ I := by
      simpa using I.mul_mem hxI hyI
    have hxq : qPlus6 x = 0 := h _ hxI
    have hyq : qPlus6 y = 0 := h _ hyI
    have hxyq : qPlus6 (x + y) = 0 := h _ hxyI
    rw [qB_eq_polar y x, add_comm y x, hxyq, hyq, hxq]
    simp
  have hfr : Module.finrank (ZMod 2) W ≤ 3 := by
    have hmono := Submodule.finrank_mono hle
    have horth := LinearMap.BilinForm.finrank_orthogonal (B := qB) qB_nondegenerate W
    have hdim : Module.finrank (ZMod 2) (Fin 6 → ZMod 2) = 6 := by
      simp [Module.finrank_fin_fun]
    rw [horth, hdim] at hmono
    omega
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hWcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), hZ2]
  calc Nat.card I = Nat.card W := hcardWI.symm
    _ = 2 ^ Module.finrank (ZMod 2) W := hWcard
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hfr
    _ = 8 := by norm_num

theorem rk_le_three_of_avoid {I : Subgroup (Multiplicative (Fin 6 → ZMod 2))}
    (h : ∀ x ∈ I, ∀ p q : Fin 8, p ≠ q → x ≠ Multiplicative.ofAdd (evPair p q)) :
    rk ↥I ≤ 3 := by
  have hsing : ∀ x ∈ I, qPlus6 (Multiplicative.toAdd x) = 0 := by
    intro x hx
    rcases zmod2_eq_zero_or_one (qPlus6 (Multiplicative.toAdd x)) with hq | hq
    · exact hq
    · exfalso
      obtain ⟨p, q, hpq, hpqx⟩ := exists_evPair_of_qPlus6 hq
      refine h x hx p q hpq ?_
      rw [hpqx]
      rfl
  have hcard : Nat.card I = 2 ^ rk ↥I :=
    card_eq_two_pow (V := Multiplicative (Fin 6 → ZMod 2)) mult_sq_one I
  have hle8 : Nat.card I ≤ 8 := card_le_eight_of_singular hsing
  have hpow : 2 ^ rk ↥I ≤ 2 ^ 3 := by
    rw [← hcard]
    simpa using hle8
  exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow

theorem rk_le_four_of_avoid_zero {I : Subgroup (Multiplicative (Fin 6 → ZMod 2))}
    (h : ∀ x ∈ I, ∀ q : Fin 8, q ≠ 0 → x ≠ Multiplicative.ofAdd (evPair 0 q)) :
    rk ↥I ≤ 4 := by
  by_contra hcon
  have hlt : 4 < rk ↥I := by omega
  have hcardI : Nat.card I = 2 ^ rk ↥I :=
    card_eq_two_pow (V := Multiplicative (Fin 6 → ZMod 2)) mult_sq_one I
  have hVcard : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 64 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    simp [Fintype.card_fun, ZMod.card]
  have hge : 32 ≤ Nat.card I := by
    rw [hcardI]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ rk ↥I := Nat.pow_le_pow_right (by norm_num) (by omega)
  have himul : I.index * Nat.card I = Nat.card (Multiplicative (Fin 6 → ZMod 2)) :=
    Subgroup.index_mul_card I
  have hindex_le : I.index ≤ 2 := by
    have h32 : I.index * 32 ≤ 64 := by
      calc I.index * 32 ≤ I.index * Nat.card I := Nat.mul_le_mul_left _ hge
        _ = Nat.card (Multiplicative (Fin 6 → ZMod 2)) := himul
        _ = 64 := hVcard
    omega
  have hindex_ne : I.index ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hVcard] at himul
    norm_num at himul
  rcases (by omega : I.index = 1 ∨ I.index = 2) with hidx | hidx
  · have htop : I = ⊤ := Subgroup.index_eq_one.mp hidx
    exact h (Multiplicative.ofAdd (evPair 0 1))
      (by rw [htop]; exact Subgroup.mem_top _) 1 (by decide) rfl
  · obtain ⟨k, hk_not, hk_prop⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hidx
    have hk7 : k ^ 7 = k := by
      have h6 : k ^ 6 = 1 := by
        change k ^ (2 * 3) = 1
        rw [pow_mul, mult_sq_one k, one_pow]
      calc k ^ 7 = k ^ 6 * k := by
              change k ^ (6 + 1) = k ^ 6 * k
              rw [pow_succ]
        _ = 1 * k := by rw [h6]
        _ = k := by simp
    have hprod_eq : (∏ q ∈ (Finset.univ.erase (0 : Fin 8)),
        (Multiplicative.ofAdd (evPair 0 q) * k)) = k := by
      rw [Finset.prod_mul_distrib,
        ← ofAdd_sum (Finset.univ.erase (0 : Fin 8)) (fun q => evPair 0 q),
        sum_evPair_erase_zero,
        show Multiplicative.ofAdd (0 : Fin 6 → ZMod 2) = 1 from rfl, one_mul,
        Finset.prod_const, show (Finset.univ.erase (0 : Fin 8)).card = 7 by decide, hk7]
    have hprodI : (∏ q ∈ (Finset.univ.erase (0 : Fin 8)),
        (Multiplicative.ofAdd (evPair 0 q) * k)) ∈ I := by
      refine I.prod_mem fun q hq => ?_
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      have hnot : Multiplicative.ofAdd (evPair 0 q) ∉ I := fun hmem =>
        h (Multiplicative.ofAdd (evPair 0 q)) hmem q hq0 rfl
      rcases hk_prop (Multiplicative.ofAdd (evPair 0 q)) with hkq | hqI
      · exact hkq
      · exact absurd hqI hnot
    rw [hprod_eq] at hprodI
    exact hk_not hprodI

end CFSG.ASVolI.AppH
