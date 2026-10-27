module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46a
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSec45
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreThetaModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

@[expose] def extendSixFun (σ : Perm (Fin 6)) (x : Fin 8) : Fin 8 :=
  if h : x.val < 6 then
    ⟨(σ ⟨x.val, h⟩).val,
      Nat.lt_trans (σ ⟨x.val, h⟩).isLt
        (Nat.lt_trans (Nat.lt_succ_self 6) (Nat.lt_succ_self 7))⟩
  else x

@[expose] def extendSixInv (σ : Perm (Fin 6)) (x : Fin 8) : Fin 8 :=
  if h : x.val < 6 then
    ⟨(σ.symm ⟨x.val, h⟩).val,
      Nat.lt_trans (σ.symm ⟨x.val, h⟩).isLt
        (Nat.lt_trans (Nat.lt_succ_self 6) (Nat.lt_succ_self 7))⟩
  else x

@[expose] def extendSix (σ : Perm (Fin 6)) : Perm (Fin 8) where
  toFun := extendSixFun σ
  invFun := extendSixInv σ
  left_inv x := by
    show extendSixInv σ (extendSixFun σ x) = x
    unfold extendSixFun extendSixInv
    by_cases h : x.val < 6
    · rw [dif_pos h]
      have h' : (σ ⟨x.val, h⟩).val < 6 := (σ ⟨x.val, h⟩).isLt
      rw [dif_pos h']
      simp
    · rw [dif_neg h, dif_neg h]
  right_inv x := by
    show extendSixFun σ (extendSixInv σ x) = x
    unfold extendSixFun extendSixInv
    by_cases h : x.val < 6
    · rw [dif_pos h]
      have h' : (σ.symm ⟨x.val, h⟩).val < 6 := (σ.symm ⟨x.val, h⟩).isLt
      rw [dif_pos h']
      simp
    · rw [dif_neg h, dif_neg h]

@[expose] def ofSix (σ : Perm (Fin 6)) (e : Bool) : Perm (Fin 8) :=
  extendSix σ * bif e then swap 6 7 else 1

private def sixEquiv : Fin 6 ≃ {x : Fin 8 // x.val < 6} where
  toFun x := ⟨⟨x.val, by omega⟩, by simp⟩
  invFun x := ⟨x.val.val, x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

private theorem ofSubtype_permCongr_sixEquiv (σ : Perm (Fin 6)) :
    ofSubtype (sixEquiv.permCongr σ) = extendSix σ := by
  refine Equiv.ext fun x => ?_
  by_cases h : x.val < 6
  · rw [ofSubtype_apply_of_mem (sixEquiv.permCongr σ) h, Equiv.permCongr_apply]
    simp [sixEquiv, extendSix, extendSixFun, h]
  · rw [ofSubtype_apply_of_not_mem (sixEquiv.permCongr σ) h]
    simp [extendSix, extendSixFun, h]

private theorem eq_extendSix_of_fix {t : Perm (Fin 8)} (h6 : t 6 = 6) (h7 : t 7 = 7) :
    ∃ σ : Perm (Fin 6), t = extendSix σ := by
  have hx67 : ∀ x : Fin 8, 6 ≤ x.val → x = 6 ∨ x = 7 := by
    intro x hx
    have hlt : x.val < 8 := x.isLt
    have h : x.val = 6 ∨ x.val = 7 := by omega
    rcases h with h | h
    · left; exact Fin.ext (by simpa using h)
    · right; exact Fin.ext (by simpa using h)
  have hsub : ∀ x : Fin 8, (t x).val < 6 ↔ x.val < 6 := by
    intro x
    constructor
    · intro hx
      by_contra h
      rcases hx67 x (by omega) with rfl | rfl
      · rw [h6] at hx; exact absurd hx (by decide)
      · rw [h7] at hx; exact absurd hx (by decide)
    · intro hx
      by_contra h
      rcases hx67 (t x) (by omega) with ht | ht
      · have hx6 : x = 6 := t.injective (ht.trans h6.symm)
        rw [hx6] at hx; exact absurd hx (by decide)
      · have hx7 : x = 7 := t.injective (ht.trans h7.symm)
        rw [hx7] at hx; exact absurd hx (by decide)
  have h2 : ∀ x, t x ≠ x → x.val < 6 := by
    intro x hx
    by_contra h
    rcases hx67 x (by omega) with h' | h'
    · exact hx (by rw [h', h6])
    · exact hx (by rw [h', h7])
  let τ : Perm {x : Fin 8 // x.val < 6} := t.subtypePerm hsub
  have hτ : t = ofSubtype τ := (ofSubtype_subtypePerm hsub h2).symm
  refine ⟨sixEquiv.symm.permCongr τ, ?_⟩
  rw [hτ, ← ofSubtype_permCongr_sixEquiv]
  congr 1

theorem exists_eq_ofSix {t : Perm (Fin 8)}
    (h : t 6 = 6 ∧ t 7 = 7 ∨ t 6 = 7 ∧ t 7 = 6) :
    ∃ (σ : Perm (Fin 6)) (e : Bool), t = ofSix σ e := by
  rcases h with ⟨h6, h7⟩ | ⟨h6, h7⟩
  · obtain ⟨σ, rfl⟩ := eq_extendSix_of_fix h6 h7
    exact ⟨σ, false, by simp [ofSix]⟩
  · have h6' : (t * swap 6 7 : Perm (Fin 8)) 6 = 6 := by
      show t (swap 6 7 6) = 6
      rw [Equiv.swap_apply_left, h7]
    have h7' : (t * swap 6 7 : Perm (Fin 8)) 7 = 7 := by
      show t (swap 6 7 7) = 7
      rw [Equiv.swap_apply_right, h6]
    obtain ⟨σ, hσ⟩ := eq_extendSix_of_fix h6' h7'
    refine ⟨σ, true, ?_⟩
    simp [ofSix]
    calc t = t * (swap 6 7 * swap 6 7) := by rw [swap_mul_self, mul_one]
      _ = (t * swap 6 7) * swap 6 7 := by group
      _ = extendSix σ * swap 6 7 := by rw [hσ]

private theorem maps_pair_of_commute_swap {t : Perm (Fin 8)}
    (h : t * swap 6 7 = swap 6 7 * t) :
    t 6 = 6 ∧ t 7 = 7 ∨ t 6 = 7 ∧ t 7 = 6 := by
  have h7 : t 7 = swap 6 7 (t 6) := by
    have := congrArg (fun f : Perm (Fin 8) => f 6) h
    simpa using this
  by_cases h6 : t 6 = 6
  · exact Or.inl ⟨h6, by rw [h7, h6, Equiv.swap_apply_left]⟩
  by_cases h6' : t 6 = 7
  · exact Or.inr ⟨h6', by rw [h7, h6', Equiv.swap_apply_right]⟩
  · exfalso
    have hfix : swap 6 7 (t 6) = t 6 := by
      rw [Equiv.swap_apply_def, if_neg h6, if_neg h6']
    have hne : t 7 ≠ t 6 := fun he => absurd (t.injective he) (by decide)
    exact hne (by rw [h7, hfix])

theorem a8c_mul_a8d_apply_eq_self_iff (x : Fin 8) :
    (a8c * a8d) x = x ↔ x = 6 ∨ x = 7 := by
  fin_cases x <;> (unfold a8c a8d; decide)

theorem maps_pair_of_commute_of_fixed {p t : Perm (Fin 8)}
    (hp : ∀ x, p x = x ↔ x = 6 ∨ x = 7) (h : t * p = p * t) :
    t 6 = 6 ∧ t 7 = 7 ∨ t 6 = 7 ∧ t 7 = 6 := by
  have ht : t ∈ Subgroup.centralizer ({p} : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h
  have h6 : p (t 6) = t 6 :=
    (Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer ht).2
      ((hp 6).2 (Or.inl rfl))
  have h7 : p (t 7) = t 7 :=
    (Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer ht).2
      ((hp 7).2 (Or.inr rfl))
  rcases (hp (t 6)).1 h6 with h6 | h6 <;> rcases (hp (t 7)).1 h7 with h7 | h7
  · exact absurd (t.injective (h6.trans h7.symm)) (by decide)
  · exact Or.inl ⟨h6, h7⟩
  · exact Or.inr ⟨h6, h7⟩
  · exact absurd (t.injective (h6.trans h7.symm)) (by decide)

private theorem maps_pair_of_commute_a8 {g : Perm (Fin 8)}
    (hc : g * a8c = a8c * g) (hd : g * a8d = a8d * g) :
    g 6 = 6 ∧ g 7 = 7 ∨ g 6 = 7 ∧ g 7 = 6 :=
  maps_pair_of_commute_of_fixed a8c_mul_a8d_apply_eq_self_iff
    (Commute.mul_right (show Commute g a8c from hc) (show Commute g a8d from hd))

private theorem ofSix_cen_two :
    ∀ (σ : Perm (Fin 6)) (e : Bool),
      (ofSix σ e * a8c = a8c * ofSix σ e → ofSix σ e * a8d = a8d * ofSix σ e →
        (∃ i ∈ Finset.range 3, ∃ j ∈ Finset.range 3, ∃ k ∈ Finset.range 2,
          ofSix σ e = a8c ^ i * a8d ^ j * swap 6 7 ^ k) ∧
        (ofSix σ e * ofSix σ e = 1 → ofSix σ e = 1 ∨ ofSix σ e = swap 6 7)) := by
  unfold a8c a8d
  decide +kernel

private def tab (x : Perm (Fin 8)) : List (Fin 8) := List.ofFn fun i => x i

private def comp (a b : List (Fin 8)) : List (Fin 8) := b.map fun j => a.getD j.val 0

private def sqT (a : List (Fin 8)) : List (Fin 8) := comp a a

private def pow8T (a : List (Fin 8)) : List (Fin 8) := sqT (sqT (sqT a))

private def tabOne : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

private theorem tab_getD (x : Perm (Fin 8)) (j : Fin 8) : (tab x).getD j.val 0 = x j := by
  have hj : (j : ℕ) < (tab x).length := by simp [tab]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [tab, List.getElem_ofFn]

private theorem tab_mul (x y : Perm (Fin 8)) : tab (x * y) = comp (tab x) (tab y) := by
  unfold tab comp
  rw [List.map_ofFn]
  congr 1
  funext i
  exact (tab_getD x (y i)).symm

private theorem tab_inj {x y : Perm (Fin 8)} (h : tab x = tab y) : x = y := by
  ext j
  rw [← tab_getD x j, ← tab_getD y j, h]

private theorem tab_one : tab (1 : Perm (Fin 8)) = tabOne := by
  decide

private theorem tab_pow8 (x : Perm (Fin 8)) : tab (x ^ 8) = pow8T (tab x) := by
  have h : x ^ 8 = (x * x) * (x * x) * ((x * x) * (x * x)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h, tab_mul, tab_mul, tab_mul]
  rfl

private theorem tab_conj (A b : Perm (Fin 8)) :
    tab (A * (b * A * b⁻¹)) = comp (tab A) (comp (comp (tab b) (tab A)) (tab b⁻¹)) := by
  rw [tab_mul, tab_mul, tab_mul]

private abbrev Vcheck (T : List (Fin 8)) : Prop :=
  (pow8T T = tabOne ∧
    pow8T (comp T (comp (comp (tab (swap 3 4 * swap 4 5)) T)
      (tab ((swap 3 4 * swap 4 5)⁻¹)))) = tabOne ∧
    pow8T (comp T (comp (comp (tab (swap 1 2 * swap 6 7)) T)
      (tab ((swap 1 2 * swap 6 7)⁻¹)))) = tabOne ∧
    pow8T (comp T (comp (comp (tab (swap 0 3 * swap 2 4)) T)
      (tab ((swap 0 3 * swap 2 4)⁻¹)))) = tabOne ∧
    pow8T (comp T (comp (comp (tab (swap 1 4 * swap 2 3)) T)
      (tab ((swap 1 4 * swap 2 3)⁻¹)))) = tabOne) →
  T = tabOne

private theorem extendSix_cen_V : ∀ σ : Perm (Fin 6), Vcheck (tab (extendSix σ)) := by
  decide +kernel

private theorem mul_swap_comm_of_fix {t : Perm (Fin 8)} (h6 : t 6 = 6) (h7 : t 7 = 7) :
    t * swap 6 7 = swap 6 7 * t := by
  ext x
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x = 6
  · subst hx; simp [h6, h7]
  · by_cases hx' : x = 7
    · subst hx'; simp [h6, h7]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
      have h1 : t x ≠ 6 := fun h => hx (t.injective (h.trans h6.symm))
      have h2 : t x ≠ 7 := fun h => hx' (t.injective (h.trans h7.symm))
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem pow8_swap : (swap 6 7 : Perm (Fin 8)) ^ 8 = 1 := by
  decide

private theorem pow8_mul_swap {A : Perm (Fin 8)} (hA : A * swap 6 7 = swap 6 7 * A) :
    (A * swap 6 7) ^ 8 = A ^ 8 := by
  rw [Commute.mul_pow hA]
  simp [pow8_swap]

private theorem mul_swap_conj {A b : Perm (Fin 8)}
    (hA : A * swap 6 7 = swap 6 7 * A) (hb : b * swap 6 7 = swap 6 7 * b) :
    (A * swap 6 7) * (b * (A * swap 6 7) * b⁻¹) = A * (b * A * b⁻¹) := by
  calc (A * swap 6 7) * (b * (A * swap 6 7) * b⁻¹)
      = A * (swap 6 7 * b) * A * swap 6 7 * b⁻¹ := by group
    _ = A * (b * swap 6 7) * A * swap 6 7 * b⁻¹ := by rw [hb.symm]
    _ = A * b * (swap 6 7 * A) * swap 6 7 * b⁻¹ := by group
    _ = A * b * (A * swap 6 7) * swap 6 7 * b⁻¹ := by rw [hA.symm]
    _ = A * b * A * (swap 6 7 * swap 6 7) * b⁻¹ := by group
    _ = A * b * A * b⁻¹ := by rw [swap_mul_self]; group

theorem cen_two : ∀ g : Perm (Fin 8), g * a8c = a8c * g → g * a8d = a8d * g →
    (∃ i ∈ Finset.range 3, ∃ j ∈ Finset.range 3, ∃ e ∈ Finset.range 2,
      g = a8c ^ i * a8d ^ j * swap 6 7 ^ e) ∧ (g * g = 1 → g = 1 ∨ g = swap 6 7) := by
  intro g hc hd
  obtain ⟨σ, e, rfl⟩ := exists_eq_ofSix (maps_pair_of_commute_a8 hc hd)
  exact ofSix_cen_two σ e hc hd

theorem cen_V : ∀ t : Perm (Fin 8), t * swap 6 7 = swap 6 7 * t → t ^ 8 = 1 →
    (t * ((swap 3 4 * swap 4 5) * t * (swap 3 4 * swap 4 5)⁻¹)) ^ 8 = 1 →
    (t * ((swap 1 2 * swap 6 7) * t * (swap 1 2 * swap 6 7)⁻¹)) ^ 8 = 1 →
    (t * ((swap 0 3 * swap 2 4) * t * (swap 0 3 * swap 2 4)⁻¹)) ^ 8 = 1 →
    (t * ((swap 1 4 * swap 2 3) * t * (swap 1 4 * swap 2 3)⁻¹)) ^ 8 = 1 →
    t = 1 ∨ t = swap 6 7 := by
  intro t hcomm h8 h1 h2 h3 h4
  obtain ⟨σ, e, rfl⟩ := exists_eq_ofSix (maps_pair_of_commute_swap hcomm)
  have hA : extendSix σ * swap 6 7 = swap 6 7 * extendSix σ :=
    mul_swap_comm_of_fix (t := extendSix σ) (by simp [extendSix, extendSixFun])
      (by simp [extendSix, extendSixFun])
  have hb1 : (swap 3 4 * swap 4 5 : Perm (Fin 8)) * swap 6 7
      = swap 6 7 * (swap 3 4 * swap 4 5) :=
    mul_swap_comm_of_fix (t := swap 3 4 * swap 4 5) (by decide) (by decide)
  have hb2 : (swap 1 2 * swap 6 7 : Perm (Fin 8)) * swap 6 7
      = swap 6 7 * (swap 1 2 * swap 6 7) := by decide
  have hb3 : (swap 0 3 * swap 2 4 : Perm (Fin 8)) * swap 6 7
      = swap 6 7 * (swap 0 3 * swap 2 4) :=
    mul_swap_comm_of_fix (t := swap 0 3 * swap 2 4) (by decide) (by decide)
  have hb4 : (swap 1 4 * swap 2 3 : Perm (Fin 8)) * swap 6 7
      = swap 6 7 * (swap 1 4 * swap 2 3) :=
    mul_swap_comm_of_fix (t := swap 1 4 * swap 2 3) (by decide) (by decide)
  have key : extendSix σ = 1 := by
    have h8' : extendSix σ ^ 8 = 1 := by
      cases e
      · simpa [ofSix] using h8
      · rw [← pow8_mul_swap hA]; simpa [ofSix] using h8
    have h1' : (extendSix σ * ((swap 3 4 * swap 4 5) * extendSix σ
        * (swap 3 4 * swap 4 5)⁻¹)) ^ 8 = 1 := by
      cases e
      · simpa [ofSix] using h1
      · rw [← mul_swap_conj hA hb1]; simpa [ofSix] using h1
    have h2' : (extendSix σ * ((swap 1 2 * swap 6 7) * extendSix σ
        * (swap 1 2 * swap 6 7)⁻¹)) ^ 8 = 1 := by
      cases e
      · simpa [ofSix] using h2
      · rw [← mul_swap_conj hA hb2]; simpa [ofSix] using h2
    have h3' : (extendSix σ * ((swap 0 3 * swap 2 4) * extendSix σ
        * (swap 0 3 * swap 2 4)⁻¹)) ^ 8 = 1 := by
      cases e
      · simpa [ofSix] using h3
      · rw [← mul_swap_conj hA hb3]; simpa [ofSix] using h3
    have h4' : (extendSix σ * ((swap 1 4 * swap 2 3) * extendSix σ
        * (swap 1 4 * swap 2 3)⁻¹)) ^ 8 = 1 := by
      cases e
      · simpa [ofSix] using h4
      · rw [← mul_swap_conj hA hb4]; simpa [ofSix] using h4
    have hT : pow8T (tab (extendSix σ)) = tabOne := by
      rw [← tab_pow8, h8', tab_one]
    have hT1 : pow8T (comp (tab (extendSix σ))
        (comp (comp (tab (swap 3 4 * swap 4 5)) (tab (extendSix σ)))
          (tab ((swap 3 4 * swap 4 5)⁻¹)))) = tabOne := by
      rw [← tab_conj, ← tab_pow8, h1', tab_one]
    have hT2 : pow8T (comp (tab (extendSix σ))
        (comp (comp (tab (swap 1 2 * swap 6 7)) (tab (extendSix σ)))
          (tab ((swap 1 2 * swap 6 7)⁻¹)))) = tabOne := by
      rw [← tab_conj, ← tab_pow8, h2', tab_one]
    have hT3 : pow8T (comp (tab (extendSix σ))
        (comp (comp (tab (swap 0 3 * swap 2 4)) (tab (extendSix σ)))
          (tab ((swap 0 3 * swap 2 4)⁻¹)))) = tabOne := by
      rw [← tab_conj, ← tab_pow8, h3', tab_one]
    have hT4 : pow8T (comp (tab (extendSix σ))
        (comp (comp (tab (swap 1 4 * swap 2 3)) (tab (extendSix σ)))
          (tab ((swap 1 4 * swap 2 3)⁻¹)))) = tabOne := by
      rw [← tab_conj, ← tab_pow8, h4', tab_one]
    exact tab_inj ((extendSix_cen_V σ ⟨hT, hT1, hT2, hT3, hT4⟩).trans tab_one.symm)
  cases e
  · exact Or.inl (by simpa [ofSix] using key)
  · exact Or.inr (by simp [ofSix, key])

theorem two_pow_perm8 {t : Perm (Fin 8)} {k : ℕ} (h : t ^ (2 ^ k) = 1) : t ^ 8 = 1 := by
  have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.2 fun n hn => ?_
  have hn1 : n ∣ 2 ^ k := (Equiv.Perm.dvd_of_mem_cycleType hn).trans h1
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn1
  have hle : 2 ^ j ≤ 8 := by
    have := (Multiset.le_sum_of_mem hn).trans (Equiv.Perm.sum_cycleType_le t)
    simpa using this
  have hj : j ≤ 3 := by
    by_contra hc
    have h16 : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (le_trans h16 hle) (by norm_num)
  have := pow_dvd_pow 2 hj
  simpa using this

theorem sign_c345 : sign (swap (3 : Fin 8) 4 * swap 4 5) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem sign_p12_67 : sign (swap (1 : Fin 8) 2 * swap 6 7) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem sign_p03_24 : sign (swap (0 : Fin 8) 3 * swap 2 4) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem sign_p14_23 : sign (swap (1 : Fin 8) 4 * swap 2 3) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

noncomputable def thG (L : Subgroup G) (θ : ↥(Nor L) →* Perm (Fin 8)) (g : G) : Perm (Fin 8) := by
  classical exact if hg : g ∈ Nor L then θ ⟨g, hg⟩ else 1

theorem thG_of_mem {θ : ↥(Nor L) →* Perm (Fin 8)} {g : G} (hg : g ∈ Nor L) :
    thG L θ g = θ ⟨g, hg⟩ := by
  unfold thG
  rw [dif_pos hg]

theorem thG_mul {θ : ↥(Nor L) →* Perm (Fin 8)} {g g' : G} (hg : g ∈ Nor L) (hg' : g' ∈ Nor L) :
    thG L θ (g * g') = thG L θ g * thG L θ g' := by
  rw [thG_of_mem hg, thG_of_mem hg', thG_of_mem (mul_mem hg hg')]
  exact map_mul θ ⟨g, hg⟩ ⟨g', hg'⟩

theorem thG_one {θ : ↥(Nor L) →* Perm (Fin 8)} : thG L θ 1 = 1 := by
  rw [thG_of_mem (one_mem _)]
  exact map_one θ

theorem thG_inv {θ : ↥(Nor L) →* Perm (Fin 8)} {g : G} (hg : g ∈ Nor L) :
    thG L θ g⁻¹ = (thG L θ g)⁻¹ := by
  rw [thG_of_mem hg, thG_of_mem (inv_mem hg)]
  exact map_inv θ ⟨g, hg⟩

theorem thG_pow {θ : ↥(Nor L) →* Perm (Fin 8)} {g : G} (hg : g ∈ Nor L) (n : ℕ) :
    thG L θ (g ^ n) = (thG L θ g) ^ n := by
  induction n with
  | zero => simpa using thG_one
  | succ n ih => rw [pow_succ, thG_mul (pow_mem hg n) hg, ih, pow_succ]

theorem thG_conj {θ : ↥(Nor L) →* Perm (Fin 8)} {x g : G} (hx : x ∈ Nor L) (hg : g ∈ Nor L) :
    thG L θ (x * g * x⁻¹) = thG L θ x * thG L θ g * (thG L θ x)⁻¹ := by
  rw [thG_mul (mul_mem hx hg) (inv_mem hx), thG_mul hx hg, thG_inv hx]

structure ThM (L : Subgroup G) (b₁ b₂ : G) (θ : ↥(Nor L) →* Perm (Fin 8)) : Prop where
  ker : ∀ g ∈ Nor L, thG L θ g = 1 ↔ g ∈ CenS L
  surj : ∀ a ∈ alternatingGroup (Fin 8), ∃ x ∈ L, thG L θ x = a
  c : thG L θ b₁ = a8c
  d : thG L θ b₂ = a8d

theorem exists_thM (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) :
    ∃ θ : ↥(Nor L) →* Perm (Fin 8), ThM L b₁ b₂ θ := by
  obtain ⟨θ, hker, -, hsurj, hb₁θ, hb₂θ⟩ := theta_model hA h
  refine ⟨θ, ⟨fun g hg => ?_, fun a ha => ?_, ?_, ?_⟩⟩
  · rw [thG_of_mem hg]; exact hker ⟨g, hg⟩
  · obtain ⟨x, hx⟩ := hsurj a ha
    exact ⟨x, x.2, by rw [thG_of_mem (Subgroup.le_normalizer x.2)]; exact hx⟩
  · rw [thG_of_mem (Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2)]; exact hb₁θ
  · rw [thG_of_mem (Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2)]; exact hb₂θ

variable {θ : ↥(Nor L) →* Perm (Fin 8)}

theorem two_elt_zpowers (h : FF84Sec4 b L B K b₁ b₂) {w : G} (hw : w ∈ Subgroup.zpowers b)
    {k : ℕ} (hk : w ^ 2 ^ k = 1) : w = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h3 : (b ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow3_of_mem h (mem_b h),
      one_zpow]
  exact eq_one_of_two_three hk h3

theorem Qθ (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥)
    (hθ : ThM L b₁ b₂ θ) {g : G} (hgN : g ∈ Nor L) (hgb : g ∈ Cen b) (hg1 : thG L θ g = 1) :
    g ∈ Subgroup.zpowers b :=
  Q_eq h hZ hX g (Subgroup.mem_inf.2 ⟨hgb, (hθ.ker g hgN).1 hg1⟩)

theorem cen_thG (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hθ : ThM L b₁ b₂ θ) {x σ : G} (hxL : x ∈ L) (hσN : σ ∈ Nor L)
    (hc : thG L θ x * thG L θ σ = thG L θ σ * thG L θ x) : x * σ = σ * x := by
  have hxN : x ∈ Nor L := Subgroup.le_normalizer hxL
  have hcL : x * σ * x⁻¹ * σ⁻¹ ∈ L := by
    have h1 : σ * x⁻¹ * σ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hσN _).1 (inv_mem hxL)
    have := mul_mem hxL h1
    rwa [show x * (σ * x⁻¹ * σ⁻¹) = x * σ * x⁻¹ * σ⁻¹ by group] at this
  have hcN : x * σ * x⁻¹ * σ⁻¹ ∈ Nor L := Subgroup.le_normalizer hcL
  have h1 : thG L θ (x * σ * x⁻¹ * σ⁻¹) = 1 := by
    rw [thG_mul (mul_mem (mul_mem hxN hσN) (inv_mem hxN)) (inv_mem hσN), thG_conj hxN hσN,
      thG_inv hσN, hc]
    group
  have h2 := (hθ.ker _ hcN).1 h1
  have h3 := L_inf_cenS hZ _ hcL h2
  calc x * σ = (x * σ * x⁻¹ * σ⁻¹) * (σ * x) := by group
    _ = σ * x := by rw [h3, one_mul]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
