module

public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem wt2_toP_mul : ∀ i j k i' j' k' : Fin 3,
    toP i j k * toP i' j' k' = toP (i + i') (j + j') (k + k') := by
  decide +kernel

theorem wt2_toE_mul (a b c a' b' c' : Fin 3) :
    toE a b c * toE a' b' c' = toE (a + a') (b + b') (c + c') :=
  Subtype.ext (wt2_toP_mul a b c a' b' c')

theorem wt2_toE_zero : toE 0 0 0 = 1 := Subtype.ext (by decide)

theorem wt2_toE_inv (a b c : Fin 3) : (toE a b c)⁻¹ = toE (-a) (-b) (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [wt2_toE_mul, add_neg_cancel, add_neg_cancel, add_neg_cancel, wt2_toE_zero]

theorem wt2_fin3 : ∀ a : Fin 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide

theorem wt2_ea_eq : ea = toE 1 0 0 := Subtype.ext (by decide)

theorem wt2_eb_eq : eb = toE 0 1 0 := Subtype.ext (by decide)

theorem wt2_ec_eq : ec = toE 0 0 1 := Subtype.ext (by decide)

theorem wt2_axisA {B : Subgroup (alternatingGroup (Fin 10))} (ha : ea ∉ B) {a : Fin 3}
    (ha0 : a ≠ 0) (h : toE a 0 0 ∈ B) : False := by
  apply ha
  rw [wt2_ea_eq]
  rcases wt2_fin3 a ha0 with rfl | rfl
  · exact h
  · have e2 : toE 2 0 0 * toE 2 0 0 = toE 1 0 0 := (wt2_toE_mul 2 0 0 2 0 0).trans rfl
    rw [← e2]
    exact B.mul_mem h h

theorem wt2_axisB {B : Subgroup (alternatingGroup (Fin 10))} (hb : eb ∉ B) {b : Fin 3}
    (hb0 : b ≠ 0) (h : toE 0 b 0 ∈ B) : False := by
  apply hb
  rw [wt2_eb_eq]
  rcases wt2_fin3 b hb0 with rfl | rfl
  · exact h
  · have e2 : toE 0 2 0 * toE 0 2 0 = toE 0 1 0 := (wt2_toE_mul 0 2 0 0 2 0).trans rfl
    rw [← e2]
    exact B.mul_mem h h

theorem wt2_axisC {B : Subgroup (alternatingGroup (Fin 10))} (hc : ec ∉ B) {c : Fin 3}
    (hc0 : c ≠ 0) (h : toE 0 0 c ∈ B) : False := by
  apply hc
  rw [wt2_ec_eq]
  rcases wt2_fin3 c hc0 with rfl | rfl
  · exact h
  · have e2 : toE 0 0 2 * toE 0 0 2 = toE 0 0 1 := (wt2_toE_mul 0 0 2 0 0 2).trans rfl
    rw [← e2]
    exact B.mul_mem h h

def wt2_coordA (x : alternatingGroup (Fin 10)) : Fin 3 :=
  if (x : Perm (Fin 10)) 0 = 0 then 0 else if (x : Perm (Fin 10)) 0 = 2 then 1 else 2

def wt2_coordB (x : alternatingGroup (Fin 10)) : Fin 3 :=
  if (x : Perm (Fin 10)) 3 = 3 then 0 else if (x : Perm (Fin 10)) 3 = 5 then 1 else 2

def wt2_coordC (x : alternatingGroup (Fin 10)) : Fin 3 :=
  if (x : Perm (Fin 10)) 6 = 6 then 0 else if (x : Perm (Fin 10)) 6 = 8 then 1 else 2

theorem wt2_coordA_toE : ∀ a b c : Fin 3, wt2_coordA (toE a b c) = a := by decide

theorem wt2_coordB_toE : ∀ a b c : Fin 3, wt2_coordB (toE a b c) = b := by decide

theorem wt2_coordC_toE : ∀ a b c : Fin 3, wt2_coordC (toE a b c) = c := by decide

theorem wt2_card_le_three {B : Subgroup (alternatingGroup (Fin 10))}
    (g : alternatingGroup (Fin 10) → Fin 3) (hg : ∀ x ∈ B, ∀ y ∈ B, g x = g y → x = y) :
    Nat.card B ≤ 3 := by
  have hinj : Function.Injective (fun x : B => g x.1) :=
    fun x y h => Subtype.ext (hg x.1 x.2 y.1 y.2 h)
  have h := Nat.card_le_card_of_injective (fun x : B => g x.1) hinj
  simpa using h

theorem exists_weight_two_of_card_nine {B : Subgroup (alternatingGroup (Fin 10))}
    (hBE : B ≤ Ebar) (hB9 : Nat.card B = 9) (ha : ea ∉ B) (hb : eb ∉ B) (hc : ec ∉ B) :
    (∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ toE i j 0 ∈ B) ∧
    (∃ j k : Fin 3, j ≠ 0 ∧ k ≠ 0 ∧ toE 0 j k ∈ B) ∧
    (∃ i k : Fin 3, i ≠ 0 ∧ k ≠ 0 ∧ toE i 0 k ∈ B) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon
    have H0 : ∀ a b : Fin 3, toE a b 0 ∈ B → a = 0 ∧ b = 0 := by
      intro a b hab
      by_cases ha0 : a = 0
      · by_cases hb0 : b = 0
        · exact ⟨ha0, hb0⟩
        · subst ha0
          exact (wt2_axisB hb hb0 hab).elim
      · by_cases hb0 : b = 0
        · subst hb0
          exact (wt2_axisA ha ha0 hab).elim
        · exact (hcon ⟨a, b, ha0, hb0, hab⟩).elim
    have hcard := wt2_card_le_three (B := B) wt2_coordC fun x hx y hy hxy => by
      obtain ⟨a, b, c, rfl⟩ := mem_Ebar_iff_toE.mp (hBE hx)
      obtain ⟨a', b', c', rfl⟩ := mem_Ebar_iff_toE.mp (hBE hy)
      rw [wt2_coordC_toE, wt2_coordC_toE] at hxy
      have hmem : (toE a b c)⁻¹ * toE a' b' c' ∈ B := B.mul_mem (B.inv_mem hx) hy
      rw [wt2_toE_inv, wt2_toE_mul, ← hxy, neg_add_cancel] at hmem
      obtain ⟨h1, h2⟩ := H0 _ _ hmem
      rw [neg_add_eq_zero] at h1 h2
      rw [← h1, ← h2, ← hxy]
    omega
  · by_contra hcon
    have H0 : ∀ b c : Fin 3, toE 0 b c ∈ B → b = 0 ∧ c = 0 := by
      intro b c hbc
      by_cases hb0 : b = 0
      · by_cases hc0 : c = 0
        · exact ⟨hb0, hc0⟩
        · subst hb0
          exact (wt2_axisC hc hc0 hbc).elim
      · by_cases hc0 : c = 0
        · subst hc0
          exact (wt2_axisB hb hb0 hbc).elim
        · exact (hcon ⟨b, c, hb0, hc0, hbc⟩).elim
    have hcard := wt2_card_le_three (B := B) wt2_coordA fun x hx y hy hxy => by
      obtain ⟨a, b, c, rfl⟩ := mem_Ebar_iff_toE.mp (hBE hx)
      obtain ⟨a', b', c', rfl⟩ := mem_Ebar_iff_toE.mp (hBE hy)
      rw [wt2_coordA_toE, wt2_coordA_toE] at hxy
      have hmem : (toE a b c)⁻¹ * toE a' b' c' ∈ B := B.mul_mem (B.inv_mem hx) hy
      rw [wt2_toE_inv, wt2_toE_mul, ← hxy, neg_add_cancel] at hmem
      obtain ⟨h1, h2⟩ := H0 _ _ hmem
      rw [neg_add_eq_zero] at h1 h2
      rw [← h1, ← h2, ← hxy]
    omega
  · by_contra hcon
    have H0 : ∀ a c : Fin 3, toE a 0 c ∈ B → a = 0 ∧ c = 0 := by
      intro a c hac
      by_cases ha0 : a = 0
      · by_cases hc0 : c = 0
        · exact ⟨ha0, hc0⟩
        · subst ha0
          exact (wt2_axisC hc hc0 hac).elim
      · by_cases hc0 : c = 0
        · subst hc0
          exact (wt2_axisA ha ha0 hac).elim
        · exact (hcon ⟨a, c, ha0, hc0, hac⟩).elim
    have hcard := wt2_card_le_three (B := B) wt2_coordB fun x hx y hy hxy => by
      obtain ⟨a, b, c, rfl⟩ := mem_Ebar_iff_toE.mp (hBE hx)
      obtain ⟨a', b', c', rfl⟩ := mem_Ebar_iff_toE.mp (hBE hy)
      rw [wt2_coordB_toE, wt2_coordB_toE] at hxy
      have hmem : (toE a b c)⁻¹ * toE a' b' c' ∈ B := B.mul_mem (B.inv_mem hx) hy
      rw [wt2_toE_inv, wt2_toE_mul, ← hxy, neg_add_cancel] at hmem
      obtain ⟨h1, h2⟩ := H0 _ _ hmem
      rw [neg_add_eq_zero] at h1 h2
      rw [← h1, ← h2, ← hxy]
    omega

end CFSG.RankThree.PartTwo.Sec15.ThmD
