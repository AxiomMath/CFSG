module

public import CFSG.Sporadic.Th.Recog.NormT

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords

theorem wprod_congr_letters {X : Type*} [Group X] {n : ℕ} {x y : Fin n → X}
    {w : List (Fin n × Bool)} (h : ∀ l ∈ w, x l.1 = y l.1) : wprod x w = wprod y w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [wprod_cons, wprod_cons, h l (by simp), ih (fun l' hl' => h l' (by simp [hl']))]

theorem wY_letters (k : Twist) (j : Fin 6) : ∀ l ∈ wY k j, l.1 ≠ 1 ∧ l.1 ≠ 5 := by
  cases k <;> fin_cases j <;> decide

theorem xw_letters (c : Config) (j : Fin 2) : ∀ l ∈ xw c j, l.1 ≠ 5 := by
  obtain ⟨k, i⟩ := c
  cases k <;> fin_cases i <;> fin_cases j <;> decide

theorem wY_eq (k : Twist) :
    wY k 0 = [(0, false)] ∧ wY k 1 = [(2, false)] ∧ wY k 2 = [(3, false)] ∧
      wY k 3 = [(4, false)] ∧ wY k 5 = [(6, true)] := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hsK_getD_dLet (k : Twist) (j : Fin 6) : (hsK k).getD (dLet j) [] = wY k j := by
  cases k <;> fin_cases j <;> rfl

theorem hsK_getD_one (k : Twist) : (hsK k).getD ((1 : Fin 8) : ℕ) [] = [(1, true)] := by
  cases k <;> rfl

theorem dLet_ne (j : Fin 6) : dLet j ≠ 1 ∧ dLet j ≠ 5 := by
  fin_cases j <;> decide

theorem exists_dLet (i : Fin 8) (h1 : i ≠ 1) (h5 : i ≠ 5) : ∃ j : Fin 6, dLet j = i := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact absurd rfl h1
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact absurd rfl h5
  · exact ⟨5, rfl⟩
  · exact ⟨4, rfl⟩

theorem mem_bfree {w : List (Fin 8 × Bool)} (hw : w ∈ bfree) :
    w ∈ R0' ∧ ∀ l ∈ w, l.1 ≠ 1 := by
  rw [bfree, List.mem_filter] at hw
  exact ⟨hw.1, fun l hl => by simpa using List.all_eq_true.mp hw.2 l hl⟩

theorem mem_brel {w : List (Fin 8 × Bool)} (hw : w ∈ brel) :
    w ∈ R0' ∧ ∀ l ∈ w, l.1 ≠ 5 := by
  rw [brel, List.mem_filter, Bool.and_eq_true] at hw
  exact ⟨hw.1, fun l hl => by simpa using List.all_eq_true.mp hw.2.2 l hl⟩

theorem relators_mem :
    ([[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
      [(3, true), (3, true)], [(4, true), (4, true)],
      [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
      [(5, false), (2, false), (5, true), (2, true)],
      [(5, true), (3, true), (5, true), (3, true)],
      [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true)],
      [(6, true), (6, true), (6, true)],
      [(6, false), (0, false), (6, true), (0, true)],
      [(6, false), (1, false), (6, true), (1, true)],
      [(6, false), (2, false), (6, true), (2, true)],
      [(6, false), (3, false), (6, true), (3, true)],
      [(6, false), (4, false), (6, true), (4, true)],
      [(6, false), (5, true), (6, true), (5, false), (5, false)],
      [(7, false), (6, true), (7, true), (6, true)]] : List (List (Fin 8 × Bool))).all
      (fun w => decide (w ∈ R0')) = true := by
  simp only [R0', TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
    TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.relatorsTwo,
    TauCeti.Sporadic.Thompson.relatorsThree, TauCeti.Sporadic.Thompson.relatorsFour,
    TauCeti.Sporadic.Thompson.relatorsFive, TauCeti.Sporadic.Thompson.relatorsSix,
    TauCeti.Sporadic.Thompson.genA, TauCeti.Sporadic.Thompson.genB,
    TauCeti.Sporadic.Thompson.genC, TauCeti.Sporadic.Thompson.genD,
    TauCeti.Sporadic.Thompson.genE, TauCeti.Sporadic.Thompson.genS,
    TauCeti.Sporadic.Thompson.genT, TauCeti.Sporadic.Thompson.genU,
    TauCeti.Relator.toWord_gen, TauCeti.Relator.toWord_pow, TauCeti.Relator.toWord_mul,
    TauCeti.Relator.toWord_inv, TauCeti.Relator.toWord_div, TauCeti.Relator.toWord_conj,
    TauCeti.Relator.toWord_commInvInv, List.map_cons, List.map_append, List.map_nil]
  decide

section Basic

theorem wprod_hswJ_of_mem {w : List (Fin 8 × Bool)} (hw : w ∈ R0') : wprod hswJ w = 1 :=
  hswJ_rel w hw

private theorem rel (w : List (Fin 8 × Bool)) (hw : w ∈
    ([[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
      [(3, true), (3, true)], [(4, true), (4, true)],
      [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
      [(5, false), (2, false), (5, true), (2, true)],
      [(5, true), (3, true), (5, true), (3, true)],
      [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true)],
      [(6, true), (6, true), (6, true)],
      [(6, false), (0, false), (6, true), (0, true)],
      [(6, false), (1, false), (6, true), (1, true)],
      [(6, false), (2, false), (6, true), (2, true)],
      [(6, false), (3, false), (6, true), (3, true)],
      [(6, false), (4, false), (6, true), (4, true)],
      [(6, false), (5, true), (6, true), (5, false), (5, false)],
      [(7, false), (6, true), (7, true), (6, true)]] : List (List (Fin 8 × Bool)))) :
    wprod hswJ w = 1 :=
  wprod_hswJ_of_mem (by simpa using List.all_eq_true.mp relators_mem w hw)

theorem hswJ_mul_self (i : Fin 8) (hi : i.val < 5) : hswJ i * hswJ i = 1 := by
  have h : wprod hswJ [(i, true), (i, true)] = 1 := by
    apply rel
    fin_cases i <;> first | (simp at hi; done) | decide
  simpa [wprod] using h

theorem hswJ_ab_cube : (hswJ 0 * hswJ 1) ^ 3 = 1 := by
  have h := rel [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] (by simp)
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    mul_one] at h
  rw [pow_succ, pow_two, ← h]
  group

theorem hswJ_comm_six (i : Fin 8) (hi : i.val < 5) : hswJ i * hswJ 6 = hswJ 6 * hswJ i := by
  have h : wprod hswJ [(6, false), (i, false), (6, true), (i, true)] = 1 := by
    apply rel
    fin_cases i <;> first | (simp at hi; done) | decide
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    Bool.false_eq_true, if_false, mul_one] at h
  calc hswJ i * hswJ 6
      = hswJ 6 * hswJ i * ((hswJ 6)⁻¹ * ((hswJ i)⁻¹ * (hswJ 6 * hswJ i)))⁻¹ := by group
    _ = hswJ 6 * hswJ i := by rw [h, inv_one, mul_one]

theorem hswJ_three_conj_five : hswJ 3 * hswJ 5 * (hswJ 3)⁻¹ = (hswJ 5)⁻¹ := by
  have h := rel [(5, true), (3, true), (5, true), (3, true)] (by simp)
  have hd := hswJ_mul_self 3 (by decide)
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    mul_one] at h
  have hd' : (hswJ 3)⁻¹ = hswJ 3 := inv_eq_of_mul_eq_one_right hd
  rw [hd']
  calc hswJ 3 * hswJ 5 * hswJ 3 = (hswJ 5)⁻¹ * (hswJ 5 * (hswJ 3 * (hswJ 5 * hswJ 3))) := by
        group
    _ = (hswJ 5)⁻¹ := by rw [h, mul_one]

theorem hswJ_two_comm_five : hswJ 2 * hswJ 5 = hswJ 5 * hswJ 2 := by
  have h := rel [(5, false), (2, false), (5, true), (2, true)] (by simp)
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    Bool.false_eq_true, if_false, mul_one] at h
  calc hswJ 2 * hswJ 5
      = hswJ 5 * hswJ 2 * ((hswJ 5)⁻¹ * ((hswJ 2)⁻¹ * (hswJ 5 * hswJ 2)))⁻¹ := by group
    _ = hswJ 5 * hswJ 2 := by rw [h, inv_one, mul_one]

theorem hswJ_six_conj_five : (hswJ 6)⁻¹ * hswJ 5 * hswJ 6 = hswJ 5 ^ 2 := by
  have h := rel [(6, false), (5, true), (6, true), (5, false), (5, false)] (by simp)
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    Bool.false_eq_true, if_false, mul_one] at h
  calc (hswJ 6)⁻¹ * hswJ 5 * hswJ 6
      = ((hswJ 6)⁻¹ * (hswJ 5 * (hswJ 6 * ((hswJ 5)⁻¹ * (hswJ 5)⁻¹)))) * hswJ 5 ^ 2 := by group
    _ = hswJ 5 ^ 2 := by rw [h, one_mul]

theorem hswJ_five_pow_seven : hswJ 5 ^ 7 = 1 := by
  have h := rel [(5, true), (5, true), (5, true), (5, true), (5, true), (5, true), (5, true)]
    (by simp)
  simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true,
    mul_one] at h
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem hswJ_five_ne_one : hswJ 5 ≠ 1 := by
  intro h
  have hk := kap_hswJ 5 (by decide)
  have h1 : (⟨hswJ 5, hswJ_mem_M 5 (by decide)⟩ : ↥Max3.M) = 1 := Subtype.ext h
  rw [h1, map_one, Subgroup.coe_one] at hk
  exact absurd hk.symm (by decide +kernel)

theorem orderOf_hswJ_five : orderOf (hswJ 5) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime hswJ_five_pow_seven hswJ_five_ne_one

theorem hswJ_zero_not_comm_one : hswJ 0 * hswJ 1 ≠ hswJ 1 * hswJ 0 := by
  intro hc
  apply hswJ_ne
  have ha := hswJ_mul_self 0 (by decide)
  have hb := hswJ_mul_self 1 (by decide)
  have h3 := hswJ_ab_cube
  have hab : (hswJ 0 * hswJ 1) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc (hswJ 1), ← hc, mul_assoc, hb, mul_one, ha]
  have h1 : hswJ 0 * hswJ 1 = 1 := by
    rw [pow_succ, hab, one_mul] at h3
    exact h3
  calc hswJ 0 = hswJ 0 * (hswJ 1 * hswJ 1) := by rw [hb, mul_one]
    _ = hswJ 1 := by rw [← mul_assoc, h1, one_mul]

theorem hswJ_mem_YJ (i : Fin 8) (hi : i ≠ 5) :
    hswJ i ∈ Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J) := by
  rw [mem_normalizer_zpowers_iff orderOf_hswJ_six]
  by_cases h7 : i = 7
  · subst h7
    exact Or.inr hswJ_seven_conj_six
  by_cases h6 : i = 6
  · subst h6
    left
    group
  left
  have hlt : i.val < 5 := by
    fin_cases i <;> simp_all
  rw [hswJ_comm_six i hlt, mul_inv_cancel_right]

@[expose] noncomputable def lettersM (i : Fin 8) : ↥Max3.M :=
  if h : i = 1 then 1 else ⟨hswJ i, hswJ_mem_M i h⟩

@[expose] noncomputable def lettersY (i : Fin 8) :
    ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) :=
  if h : i = 5 then 1 else ⟨hswJ i, hswJ_mem_YJ i h⟩

theorem coe_lettersM (i : Fin 8) (hi : i ≠ 1) : (lettersM i : J) = hswJ i := by
  rw [lettersM, dif_neg hi]

theorem coe_lettersY (i : Fin 8) (hi : i ≠ 5) : (lettersY i : J) = hswJ i := by
  rw [lettersY, dif_neg hi]

theorem coe_wprod_lettersM {w : List (Fin 8 × Bool)} (hw : ∀ l ∈ w, l.1 ≠ 1) :
    ((wprod lettersM w : ↥Max3.M) : J) = wprod hswJ w := by
  rw [← Subgroup.coe_subtype, map_wprod]
  exact wprod_congr_letters fun l hl => coe_lettersM l.1 (hw l hl)

theorem coe_wprod_lettersY {w : List (Fin 8 × Bool)} (hw : ∀ l ∈ w, l.1 ≠ 5) :
    ((wprod lettersY w : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : J) =
      wprod hswJ w := by
  rw [← Subgroup.coe_subtype, map_wprod]
  exact wprod_congr_letters fun l hl => coe_lettersY l.1 (hw l hl)

theorem wprod_lettersM_bfree {w : List (Fin 8 × Bool)} (hw : w ∈ bfree) :
    wprod lettersM w = 1 :=
  Subtype.ext ((coe_wprod_lettersM (mem_bfree hw).2).trans
    (wprod_hswJ_of_mem (mem_bfree hw).1))

theorem wprod_lettersY_brel {w : List (Fin 8 × Bool)} (hw : w ∈ brel) :
    wprod lettersY w = 1 :=
  Subtype.ext ((coe_wprod_lettersY (mem_brel hw).2).trans
    (wprod_hswJ_of_mem (mem_brel hw).1))

noncomputable abbrev tLetter : ↥Max3.M := ⟨hswJ 6, hswJ_mem_M 6 (by decide)⟩

noncomputable abbrev sLetter : ↥Max3.M := ⟨hswJ 5, hswJ_mem_M 5 (by decide)⟩

@[expose] noncomputable def D8M : Subgroup ↥Max3.M :=
  Subgroup.closure {⟨hswJ 2, hswJ_mem_M 2 (by decide)⟩,
    ⟨hswJ 3 * hswJ 2 * hswJ 3,
      Max3.M.mul_mem (Max3.M.mul_mem (hswJ_mem_M 3 (by decide)) (hswJ_mem_M 2 (by decide)))
        (hswJ_mem_M 3 (by decide))⟩}

theorem orderOf_tLetter : orderOf tLetter = 3 := by
  rw [Subgroup.orderOf_mk, orderOf_hswJ_six]

theorem orderOf_sLetter : orderOf sLetter = 7 := by
  rw [Subgroup.orderOf_mk, orderOf_hswJ_five]

theorem tLetter_conj_sLetter : tLetter⁻¹ * sLetter * tLetter ∈ Subgroup.zpowers sLetter := by
  have h : tLetter⁻¹ * sLetter * tLetter = sLetter ^ 2 := Subtype.ext hswJ_six_conj_five
  rw [h]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem D8M_le_centralizer_s : D8M ≤ Subgroup.centralizer {sLetter} := by
  rw [D8M, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hswJ_two_comm_five
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have h1 : hswJ 3 * hswJ 5 = (hswJ 5)⁻¹ * hswJ 3 := by
      rw [← hswJ_three_conj_five]; group
    have h2 : hswJ 2 * (hswJ 5)⁻¹ = (hswJ 5)⁻¹ * hswJ 2 := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hswJ_two_comm_five, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have h3 : hswJ 3 * (hswJ 5)⁻¹ = hswJ 5 * hswJ 3 := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, mul_inv_cancel, one_mul]
    show hswJ 3 * hswJ 2 * hswJ 3 * hswJ 5 = hswJ 5 * (hswJ 3 * hswJ 2 * hswJ 3)
    calc hswJ 3 * hswJ 2 * hswJ 3 * hswJ 5
        = hswJ 3 * (hswJ 2 * (hswJ 3 * hswJ 5)) := by simp only [mul_assoc]
      _ = hswJ 3 * (hswJ 2 * (hswJ 5)⁻¹) * hswJ 3 := by rw [h1]; simp only [mul_assoc]
      _ = hswJ 3 * (hswJ 5)⁻¹ * (hswJ 2 * hswJ 3) := by rw [h2]; simp only [mul_assoc]
      _ = hswJ 5 * (hswJ 3 * hswJ 2 * hswJ 3) := by rw [h3]; simp only [mul_assoc]

theorem D8M_le_centralizer_t : D8M ≤ Subgroup.centralizer {tLetter} := by
  rw [D8M, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hswJ_comm_six 2 (by decide)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    show hswJ 3 * hswJ 2 * hswJ 3 * hswJ 6 = hswJ 6 * (hswJ 3 * hswJ 2 * hswJ 3)
    calc hswJ 3 * hswJ 2 * hswJ 3 * hswJ 6
        = hswJ 3 * (hswJ 2 * (hswJ 3 * hswJ 6)) := by simp only [mul_assoc]
      _ = hswJ 3 * (hswJ 2 * hswJ 6) * hswJ 3 := by
        rw [hswJ_comm_six 3 (by decide)]; simp only [mul_assoc]
      _ = hswJ 3 * hswJ 6 * (hswJ 2 * hswJ 3) := by
        rw [hswJ_comm_six 2 (by decide)]; simp only [mul_assoc]
      _ = hswJ 6 * (hswJ 3 * hswJ 2 * hswJ 3) := by
        rw [hswJ_comm_six 3 (by decide)]; simp only [mul_assoc]

theorem D8M_comm_t : ∀ x ∈ D8M, Commute tLetter x := fun _ hx =>
  (Subgroup.mem_centralizer_singleton_iff.mp (D8M_le_centralizer_t hx)).symm

structure E8Facts (E₀ : Subgroup ↥Max3.M) (e₀ : ↥Max3.M) : Prop where
  mem : e₀ ∈ E₀
  ne_one : e₀ ≠ 1
  ne_z : (e₀ : J) ≠ Max3.z
  comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x
  sq : ∀ x ∈ E₀, x * x = 1
  card : Nat.card E₀ = 8
  z_mem : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ E₀
  comm_t : ∀ x ∈ E₀, x * tLetter = tLetter * x
  cent : ∀ m : ↥Max3.M, m * tLetter = tLetter * m → (∀ x ∈ E₀, m * x = x * m) →
    ∃ x ∈ E₀, ∃ k : ℕ, m = x * tLetter ^ k
  trans : ∀ w ∈ E₀, w ≠ 1 → (w : J) ≠ Max3.z → ∃ n : ↥Max3.M, n * tLetter = tLetter * n ∧
    (∀ x ∈ E₀, n * x * n⁻¹ ∈ E₀) ∧ n * e₀ * n⁻¹ = w
  mem_Q : (e₀ : J) ∈ Max3.Q
  card_centralizer : Nat.card (Subgroup.centralizer ({e₀} : Set ↥Max3.M)) = 2 ^ 14 * 21
  abelian : ∀ A : Subgroup ↥Max3.M, (∀ x ∈ A, (x : J) ∈ Max3.Q ∧ x * e₀ = e₀ * x) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    (∀ c : ↥Max3.M, c * e₀ = e₀ * c → ∀ x ∈ A, c * x * c⁻¹ ∈ A) →
    (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ A → e₀ ∈ A → Nat.card A = 4 ∨ E₀ ≤ A
  three : ∃ m₁ m₂ : ↥Max3.M, m₁ * e₀ = e₀ * m₁ ∧ m₂ * e₀ = e₀ * m₂ ∧
    (∃ k : ℕ, m₁ ^ 2 ^ k = 1) ∧ (∃ k : ℕ, m₂ ^ 2 ^ k = 1) ∧ 3 ∣ orderOf (m₁ * m₂)

structure GlueMFacts : Prop where
  card_centralizer_t : Nat.card ↥(Subgroup.centralizer ({tLetter} : Set ↥Max3.M)) = 1728
  conj_three : ∀ x w : ↥Max3.M, orderOf x = 3 → w * w = 1 → w ≠ 1 → (w : J) ≠ Max3.z →
    w * x = x * w → ∃ m : ↥Max3.M, m * x * m⁻¹ = tLetter
  g1 : ∃ H₁ H₂ : Subgroup ↥Max3.M, MG1 tLetter H₁ H₂
  complement_t : ∃ D₀ : Subgroup ↥Max3.M, D₀ ⊓ Subgroup.zpowers tLetter = ⊥ ∧
    D₀ ⊔ Subgroup.zpowers tLetter = Subgroup.centralizer {tLetter}
  center_t : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * tLetter = tLetter * w → w ≠ 1 →
    (w : J) ≠ Max3.z →
      ∃ q : ↥Max3.M, (q : J) ∈ Max3.Q ∧ q * tLetter = tLetter * q ∧ q * w ≠ w * q
  e8 : ∃ (E₀ : Subgroup ↥Max3.M) (e₀ : ↥Max3.M), E8Facts E₀ e₀
  seven : ∀ x : ↥Max3.M, orderOf x = 7 →
    ∃ D : Subgroup ↥Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
      D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧ Nonempty (↥D ≃* DihedralGroup 4)
  card_D8 : Nat.card ↥D8M = 8

end Basic

end CFSG.Sporadic.Th.Recog
