module

public import Certificates.Data.Kernel.BabyMonster.B9201Facts
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Sporadic.Bridge.B.R9201

open CFSG.KC.BM.B9201 TauCeti

section Group

variable {G : Type*} [Group G]

@[expose] def mExp (d : ℕ) : ℕ := if d = 0 then 1 else if d = 1 then 3 else 2

theorem conj_pow' (h x : G) : ∀ n : ℕ, (h * x * h⁻¹) ^ n = h * x ^ n * h⁻¹
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, conj_pow' h x n, pow_succ]
    group

theorem cox2_of_comm {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : x * y = y * x) :
    (x * y) ^ 2 = 1 := by
  rw [pow_two, mul_assoc, ← mul_assoc y, ← h, mul_assoc, hy, mul_one, hx]

theorem comm_of_cox2 {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 2 = 1) :
    x * y = y * x := by
  have e : x * y * (x * y) = 1 := by rw [← pow_two]; exact h
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have := eq_inv_of_mul_eq_one_left e
  rw [mul_inv_rev, hxi, hyi] at this
  exact this

theorem braid_of {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : (a * b) ^ 3 = 1) :
    a * b * a = b * a * b := by
  have e : a * b * a * (b * a * b) = 1 := by
    rw [← h, pow_succ, pow_two]
    group
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have := eq_inv_of_mul_eq_one_left e
  rw [mul_inv_rev, mul_inv_rev, hai, hbi, ← mul_assoc] at this
  exact this

theorem mid_eq {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : (a * b) ^ 3 = 1) (hac : a * c = c * a) : b = a * (b * c) * a * (b * c)⁻¹ * a := by
  have hbr := braid_of ha hb hab
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hca : ∀ X, c * (a * X) = a * (c * X) := fun X => by rw [← mul_assoc, ← hac, mul_assoc]
  have hcc : ∀ X, c * (c * X) = X := fun X => by rw [← mul_assoc, hc, one_mul]
  have hbb : ∀ X, b * (b * X) = X := fun X => by rw [← mul_assoc, hb, one_mul]
  have hbr' : ∀ X, a * (b * (a * X)) = b * (a * (b * X)) := fun X => by
    rw [← mul_assoc, ← mul_assoc, hbr, mul_assoc, mul_assoc]
  rw [mul_inv_rev, hbi, hci]
  simp only [mul_assoc]
  rw [hca, hcc, hbr', hbb, ha, mul_one]

theorem cox_symm {x y : G} {m : ℕ} (h : (x * y) ^ m = 1) : (y * x) ^ m = 1 := by
  have e : y * x = x⁻¹ * (x * y) * x⁻¹⁻¹ := by group
  rw [e, conj_pow', h]
  group

theorem chain_conj {g : ℕ → G} {c : ℕ → ℕ} {h : G}
    (hc : ∀ i < 7, h * g (c i) = g (c (i + 1)) * h) :
    ∀ i < 7, g (c (i + 1)) = h * g (c i) * h⁻¹ := fun i hi => by
  rw [eq_mul_inv_iff_mul_eq]
  exact (hc i hi).symm

theorem chain_sq {g : ℕ → G} {c : ℕ → ℕ} {h : G}
    (hc : ∀ i < 7, h * g (c i) = g (c (i + 1)) * h) (h0 : g (c 0) * g (c 0) = 1) :
    ∀ i < 8, g (c i) * g (c i) = 1 := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ i ih =>
    intro hi
    rw [chain_conj hc i (by omega)]
    calc h * g (c i) * h⁻¹ * (h * g (c i) * h⁻¹) = h * (g (c i) * g (c i)) * h⁻¹ := by group
      _ = 1 := by rw [ih (by omega)]; group

theorem chain_rel {g : ℕ → G} {c : ℕ → ℕ} {h : G}
    (hc : ∀ i < 7, h * g (c i) = g (c (i + 1)) * h)
    (hbase : ∀ d < 8, (g (c 0) * g (c d)) ^ mExp d = 1) :
    ∀ a b, a ≤ b → b < 8 → (g (c a) * g (c b)) ^ mExp (b - a) = 1 := by
  intro a
  induction a with
  | zero => exact fun b _ hb => by simpa using hbase b hb
  | succ a ih =>
    intro b hab hb
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [chain_conj hc a (by omega), chain_conj hc b' (by omega)]
    have e : h * g (c a) * h⁻¹ * (h * g (c b') * h⁻¹) = h * (g (c a) * g (c b')) * h⁻¹ := by
      group
    rw [e, conj_pow', Nat.add_sub_add_right, ih b' (by omega) (by omega)]
    group

theorem chain_base {g : ℕ → G} {c : ℕ → ℕ} (h0 : c 0 = 0) (h1 : c 1 = 1)
    (hsq : ∀ i < 8, g (c i) * g (c i) = 1) (hbr : (g 0 * g 1) ^ 3 = 1)
    (hcomm : ∀ d, 2 ≤ d → d < 8 → g 0 * g (c d) = g (c d) * g 0) :
    ∀ d < 8, (g (c 0) * g (c d)) ^ mExp d = 1 := by
  intro d hd
  match d with
  | 0 => simpa [mExp] using hsq 0 (by norm_num)
  | 1 =>
    rw [h0, h1]
    simpa [mExp] using hbr
  | d + 2 =>
    have hg0 := hsq 0 (by norm_num)
    rw [h0] at hg0 ⊢
    simpa [mExp] using cox2_of_comm hg0 (hsq _ hd) (hcomm _ (by omega) hd)

@[expose] def edgesN : List (ℕ × ℕ) :=
  [(4, 3), (3, 2), (2, 1), (1, 0), (4, 5), (5, 6), (6, 7), (4, 8), (8, 9), (9, 10)]

@[expose] def Mf (i j : ℕ) : ℕ :=
  if i = j then 1 else if (i, j) ∈ edgesN ∨ (j, i) ∈ edgesN then 3 else 2

@[expose] def pos2 (i : ℕ) : ℕ := [0, 1, 2, 3, 4, 0, 0, 0, 5, 6, 7].getD i 0

theorem classifyF : ∀ i j : Fin 11,
    (i.val ≤ j.val ∧ j.val < 8 ∧ Mf i j = mExp (j - i)) ∨ (j.val ≤ i ∧ i.val < 8 ∧ Mf i j = mExp (i - j)) ∨
    (pos2 i ≤ pos2 j ∧ pos2 j < 8 ∧ chain2.getD (pos2 i) 0 = i ∧ chain2.getD (pos2 j) 0 = j ∧
      Mf i j = mExp (pos2 j - pos2 i)) ∨
    (pos2 j ≤ pos2 i ∧ pos2 i < 8 ∧ chain2.getD (pos2 j) 0 = j ∧ chain2.getD (pos2 i) 0 = i ∧
      Mf i j = mExp (pos2 i - pos2 j)) ∨
    (i.val ∈ [5, 6, 7] ∧ j.val ∈ [8, 9, 10] ∧ Mf i j = 2) ∨
    (j.val ∈ [5, 6, 7] ∧ i.val ∈ [8, 9, 10] ∧ Mf i j = 2) := by
  decide

theorem classify : ∀ i < 11, ∀ j < 11,
    (i ≤ j ∧ j < 8 ∧ Mf i j = mExp (j - i)) ∨ (j ≤ i ∧ i < 8 ∧ Mf i j = mExp (i - j)) ∨
    (pos2 i ≤ pos2 j ∧ pos2 j < 8 ∧ chain2.getD (pos2 i) 0 = i ∧ chain2.getD (pos2 j) 0 = j ∧
      Mf i j = mExp (pos2 j - pos2 i)) ∨
    (pos2 j ≤ pos2 i ∧ pos2 i < 8 ∧ chain2.getD (pos2 j) 0 = j ∧ chain2.getD (pos2 i) 0 = i ∧
      Mf i j = mExp (pos2 i - pos2 j)) ∨
    (i ∈ [5, 6, 7] ∧ j ∈ [8, 9, 10] ∧ Mf i j = 2) ∨ (j ∈ [5, 6, 7] ∧ i ∈ [8, 9, 10] ∧ Mf i j = 2) :=
  fun i hi j hj => classifyF ⟨i, hi⟩ ⟨j, hj⟩

theorem coxeterMatrix_eq (i j : Fin 11) :
    TauCeti.Sporadic.BabyMonster.coxeterMatrix i j = Mf i.val j.val := by
  rw [TauCeti.Sporadic.BabyMonster.coxeterMatrix_apply, TauCeti.Sporadic.BabyMonster.edges_eq]
  revert i j
  decide

variable {g : ℕ → G}

theorem cox_of_relsT (hR : RelsT g) :
    (∀ i < 11, g i * g i = 1) ∧ ∀ i < 11, ∀ j < 11, (g i * g j) ^ Mf i j = 1 := by
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, -, -, -⟩ := hR
  have hc1 : ∀ i < 7, rT g * g ((fun k => k) i) = g ((fun k => k) (i + 1)) * rT g := F4
  have hc2 : ∀ i < 7, rqT g * g ((fun k => chain2.getD k 0) i) =
      g ((fun k => chain2.getD k 0) (i + 1)) * rqT g := F5
  have s1 := chain_sq hc1 F1
  have s2 := chain_sq hc2 F1
  have hsq : ∀ i < 11, g i * g i = 1 := by
    intro i hi
    by_cases h8 : i < 8
    · exact s1 i h8
    · interval_cases i
      · exact s2 5 (by norm_num)
      · exact s2 6 (by norm_num)
      · exact s2 7 (by norm_num)
  have C1 := chain_rel hc1 (chain_base rfl rfl s1 F2 (fun d hd1 hd2 => F3 d (by
    interval_cases d <;> simp)))
  have C2 := chain_rel hc2 (chain_base rfl rfl s2 F2 (fun d hd1 hd2 => F3 _ (by
    interval_cases d <;> decide)))
  have a56 : (g 5 * g 6) ^ 3 = 1 := C1 5 6 (by norm_num) (by norm_num)
  have a67 : (g 6 * g 7) ^ 3 = 1 := C1 6 7 (by norm_num) (by norm_num)
  have c57 : g 5 * g 7 = g 7 * g 5 :=
    comm_of_cox2 (hsq 5 (by norm_num)) (hsq 7 (by norm_num)) (C1 5 7 (by norm_num) (by norm_num))
  have a89 : (g 8 * g 9) ^ 3 = 1 := C2 5 6 (by norm_num) (by norm_num)
  have c810 : g 8 * g 10 = g 10 * g 8 :=
    comm_of_cox2 (hsq 8 (by norm_num)) (hsq 10 (by norm_num)) (C2 5 7 (by norm_num) (by norm_num))
  have m6 := mid_eq (hsq 5 (by norm_num)) (hsq 6 (by norm_num)) (hsq 7 (by norm_num)) a56 c57
  have m9 := mid_eq (hsq 8 (by norm_num)) (hsq 9 (by norm_num)) (hsq 10 (by norm_num)) a89 c810
  have m7 : g 7 = g 6 * (g 6 * g 7) := by rw [← mul_assoc, hsq 6 (by norm_num), one_mul]
  have m10 : g 10 = g 9 * (g 9 * g 10) := by rw [← mul_assoc, hsq 9 (by norm_num), one_mul]
  have arm2 : ∀ x : G, Commute x (g 8) → Commute x (g 9 * g 10) →
      Commute x (g 8) ∧ Commute x (g 9) ∧ Commute x (g 10) := by
    intro x h8 hv
    have h9 : Commute x (g 9) := by
      rw [m9]
      exact (((h8.mul_right hv).mul_right h8).mul_right hv.inv_right).mul_right h8
    refine ⟨h8, h9, ?_⟩
    rw [m10]
    exact h9.mul_right hv
  obtain ⟨d58, d59, d510⟩ := arm2 (g 5) F6 F7
  obtain ⟨du8, du9, du10⟩ := arm2 (g 6 * g 7) F8 F9
  have arm1 : ∀ y : G, Commute (g 5) y → Commute (g 6 * g 7) y →
      Commute (g 5) y ∧ Commute (g 6) y ∧ Commute (g 7) y := by
    intro y h5 hu
    have h6 : Commute (g 6) y := by
      rw [m6]
      exact (((h5.mul_left hu).mul_left h5).mul_left hu.inv_left).mul_left h5
    refine ⟨h5, h6, ?_⟩
    rw [m7]
    exact h6.mul_left hu
  have C3 : ∀ x ∈ [5, 6, 7], ∀ y ∈ [8, 9, 10], (g x * g y) ^ 2 = 1 := by
    obtain ⟨-, e68, e78⟩ := arm1 (g 8) d58 du8
    obtain ⟨-, e69, e79⟩ := arm1 (g 9) d59 du9
    obtain ⟨-, e610, e710⟩ := arm1 (g 10) d510 du10
    intro x hx y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hy
    have hc : Commute (g x) (g y) := by
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> assumption
    exact cox2_of_comm (hsq x (by omega)) (hsq y (by omega)) hc
  refine ⟨hsq, fun i hi j hj => ?_⟩
  rcases classify i hi j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h4, h5, h6⟩ |
    ⟨h1, h2, h4, h5, h6⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h3]
    exact C1 i j h1 h2
  · rw [h3]
    exact cox_symm (C1 j i h1 h2)
  · have := C2 (pos2 i) (pos2 j) h1 h2
    rwa [h4, h5, ← h6] at this
  · have := cox_symm (C2 (pos2 j) (pos2 i) h1 h2)
    rwa [h4, h5, ← h6] at this
  · rw [h3]
    exact C3 i h1 j h2
  · rw [h3]
    exact cox_symm (C3 j h1 i h2)

theorem lp_eq_prod (l : List ℕ) : lp g l = (l.map g).prod := rfl

theorem relator_eval (hR : RelsT g) : ∀ t ∈ TauCeti.Sporadic.BabyMonster.relatorList,
    FreeGroup.lift (fun i : Fin 11 => g i.val) t.toFreeGroup = 1 := by
  have hcox := (cox_of_relsT hR).2
  obtain ⟨-, -, -, -, -, -, -, -, -, F10, F11, F12⟩ := hR
  intro t ht
  rw [TauCeti.Sporadic.BabyMonster.relatorList_def, List.mem_append, mem_coxeterRelators_iff,
    TauCeti.Sporadic.BabyMonster.adjoinedRelators_def] at ht
  rcases ht with ⟨i, j, rfl⟩ | ht
  · rw [toFreeGroup_coxeterRelator]
    simp only [CoxeterMatrix.relation, map_pow, map_mul, FreeGroup.lift_apply_of]
    rw [coxeterMatrix_eq]
    exact hcox _ (Fin.isLt _) _ (Fin.isLt _)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · rw [TauCeti.Sporadic.BabyMonster.spiderRelator_eq]
      simp only [lp_eq_prod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at F10
      simpa [mul_assoc] using F10
    · rw [TauCeti.Sporadic.BabyMonster.extraRelatorOne_eq]
      simp only [lp_eq_prod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at F11
      simpa [mul_assoc] using F11
    · rw [TauCeti.Sporadic.BabyMonster.extraRelatorTwo_eq]
      simp only [lp_eq_prod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at F12
      simpa [mul_assoc] using F12

theorem rels_of_relsT (hR : RelsT g) : ∀ v ∈ pres.relatorLetters, wordProd g v = 1 := by
  intro v hv
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def, List.map_map,
    List.mem_map] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  rw [Function.comp_apply, ← lift_mk, Relator.toWord_toFreeGroup]
  exact relator_eval hR t ht

end Group

end CFSG.Sporadic.Bridge.B.R9201

end
