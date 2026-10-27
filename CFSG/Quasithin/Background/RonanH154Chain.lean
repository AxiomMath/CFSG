module

public import CFSG.Quasithin.Background.RonanH154Gen
public import CFSG.Quasithin.Background.RonanH163Chain

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def reps6 : List ℕ := [30, 32, 62, 262, 280, 294, 312, 512, 542, 544, 574, 774, 792, 806, 824]

@[expose] def slp6 : List (ℕ × List (ℕ × ℕ × ℕ)) :=
  [(30, [(1, 0, 0), (1, 3, 0), (1, 4, 0), (0, 0, 1), (0, 6, 2), (0, 7, 4), (0, 8, 5), (0, 2, 3), (0, 10, 4), (0, 11, 5)]),
    (32, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 4), (0, 0, 2), (0, 7, 3), (0, 8, 4), (0, 9, 5), (0, 0, 3)]),
    (62, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 2), (0, 6, 4), (0, 2, 4), (0, 1, 5), (0, 0, 2), (0, 10, 3), (0, 11, 4), (0, 12, 5)]),
    (262, [(1, 0, 0), (2, 0, 0), (2, 3, 0), (0, 0, 2), (0, 6, 3), (0, 7, 4), (0, 8, 5), (0, 0, 1), (0, 10, 2), (0, 11, 3), (0, 1, 2), (0, 13, 4)]),
    (280, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 2, 3), (0, 0, 1), (0, 7, 2), (0, 8, 5), (0, 0, 2), (0, 10, 3), (0, 1, 2), (0, 12, 3), (0, 13, 4)]),
    (294, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 3), (0, 6, 4), (0, 0, 2), (0, 8, 3), (0, 9, 4), (0, 10, 5), (0, 2, 3), (0, 12, 4), (0, 13, 5), (0, 1, 4), (0, 15, 5)]),
    (312, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 1, 2), (0, 6, 3), (0, 7, 4), (0, 4, 5), (0, 0, 1), (0, 10, 2), (0, 11, 3), (0, 12, 5), (0, 1, 5)]),
    (512, [(1, 0, 0), (2, 0, 0), (1, 4, 0), (0, 1, 3), (0, 6, 4), (0, 1, 2), (0, 8, 4), (0, 9, 5)]),
    (542, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 3), (0, 6, 5), (0, 1, 2), (0, 8, 3), (0, 0, 1), (0, 10, 3), (0, 11, 4), (0, 12, 5), (0, 3, 5)]),
    (544, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 3, 5), (0, 0, 1), (0, 7, 3), (0, 8, 4), (0, 0, 2), (0, 10, 5), (0, 1, 3), (0, 12, 4)]),
    (574, [(1, 0, 0), (2, 0, 0), (2, 3, 0), (0, 0, 3), (0, 6, 4), (0, 7, 5), (0, 1, 2), (0, 9, 4), (0, 10, 5), (0, 2, 5), (0, 1, 2), (0, 13, 3)]),
    (774, [(1, 0, 0), (1, 3, 0), (1, 4, 0), (0, 0, 4), (0, 0, 1), (0, 7, 3), (0, 8, 4), (0, 0, 5)]),
    (792, [(1, 0, 0), (1, 3, 0), (2, 3, 0), (0, 0, 1), (0, 6, 2), (0, 7, 3), (0, 8, 5), (0, 1, 2), (0, 10, 3), (0, 11, 4), (0, 1, 2), (0, 13, 5)]),
    (806, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 4), (0, 2, 5), (0, 1, 2), (0, 8, 3), (0, 9, 4), (0, 10, 5), (0, 0, 1), (0, 12, 3), (0, 13, 4)]),
    (824, [(1, 0, 0), (1, 3, 0), (1, 4, 0), (0, 0, 3), (0, 2, 5), (0, 0, 1), (0, 8, 2), (0, 9, 4), (0, 10, 5), (0, 0, 1), (0, 12, 3), (0, 13, 4)])]

@[expose] def reps10 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

@[expose] def slp10 : List (ℕ × List (ℕ × ℕ × ℕ)) :=
  [(1, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 0, 1), (0, 10, 2), (0, 11, 3), (0, 12, 5), (0, 13, 7), (0, 0, 2), (0, 15, 3), (0, 16, 4), (0, 17, 7), (0, 18, 8), (0, 19, 9), (0, 0, 1), (0, 21, 2), (0, 22, 4), (0, 23, 5), (0, 24, 6), (0, 25, 7), (0, 26, 8)]),
    (2, [(1, 0, 0), (1, 7, 0), (2, 7, 0), (0, 0, 1), (0, 10, 2), (0, 11, 5), (0, 12, 6), (0, 13, 8), (0, 14, 9), (0, 0, 1), (0, 16, 5), (0, 17, 8), (0, 0, 1), (0, 19, 2), (0, 20, 5), (0, 21, 6), (0, 22, 7), (0, 23, 8), (0, 24, 9)]),
    (3, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 0, 1), (0, 10, 7), (0, 11, 8), (0, 12, 9), (0, 1, 7), (0, 14, 8), (0, 15, 9), (0, 1, 2), (0, 17, 4), (0, 18, 6), (0, 19, 9), (0, 2, 3), (0, 21, 5), (0, 22, 8), (0, 23, 9)]),
    (4, [(1, 0, 0), (2, 0, 0), (1, 7, 0), (0, 1, 4), (0, 10, 5), (0, 11, 7), (0, 3, 4), (0, 13, 6), (0, 14, 7), (0, 15, 9), (0, 2, 3), (0, 17, 4), (0, 18, 5), (0, 19, 8)]),
    (5, [(1, 0, 0), (2, 0, 0), (1, 8, 0), (0, 0, 1), (0, 10, 3), (0, 11, 4), (0, 12, 5), (0, 13, 6), (0, 14, 7), (0, 15, 9), (0, 2, 3), (0, 17, 4), (0, 18, 7), (0, 1, 3), (0, 20, 4), (0, 21, 5), (0, 22, 6), (0, 23, 7), (0, 24, 9), (0, 0, 3), (0, 26, 6), (0, 27, 7), (0, 28, 8), (0, 29, 9)]),
    (6, [(1, 0, 0), (2, 0, 0), (1, 7, 0), (0, 0, 1), (0, 10, 2), (0, 11, 4), (0, 12, 5), (0, 13, 6), (0, 14, 7), (0, 15, 8), (0, 16, 9), (0, 1, 2), (0, 18, 3), (0, 19, 4), (0, 20, 5), (0, 21, 7), (0, 22, 8), (0, 0, 1), (0, 24, 2), (0, 25, 3), (0, 26, 4), (0, 27, 5), (0, 28, 7), (0, 29, 8), (0, 1, 4), (0, 31, 5), (0, 32, 7)]),
    (7, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 1, 3), (0, 10, 6), (0, 11, 8), (0, 12, 9), (0, 0, 1), (0, 14, 2), (0, 15, 6), (0, 16, 7), (0, 17, 9), (0, 2, 3), (0, 19, 7), (0, 20, 8), (0, 0, 4), (0, 22, 8)]),
    (8, [(1, 0, 0), (2, 0, 0), (1, 7, 0), (0, 1, 2), (0, 10, 6), (0, 11, 7), (0, 12, 8), (0, 2, 5), (0, 14, 6), (0, 15, 9), (0, 1, 3), (0, 17, 6), (0, 18, 8)]),
    (9, [(1, 0, 0), (2, 0, 0), (1, 7, 0), (0, 0, 2), (0, 10, 3), (0, 11, 4), (0, 12, 5), (0, 13, 9), (0, 0, 1), (0, 15, 3), (0, 16, 4), (0, 17, 6), (0, 18, 7), (0, 19, 8), (0, 20, 9), (0, 0, 3), (0, 22, 4), (0, 23, 5), (0, 24, 6), (0, 25, 8), (0, 26, 9), (0, 2, 3), (0, 28, 4), (0, 29, 5), (0, 30, 9)]),
    (10, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 3, 6), (0, 10, 9), (0, 0, 1), (0, 12, 3), (0, 13, 6), (0, 14, 7), (0, 15, 8), (0, 1, 2), (0, 17, 6), (0, 18, 8), (0, 1, 3), (0, 20, 6), (0, 21, 7), (0, 22, 8)]),
    (11, [(1, 0, 0), (2, 0, 0), (1, 7, 0), (0, 2, 3), (0, 10, 4), (0, 11, 5), (0, 12, 7), (0, 13, 9), (0, 0, 1), (0, 15, 3), (0, 16, 5), (0, 17, 6), (0, 18, 8), (0, 19, 9), (0, 0, 1), (0, 21, 5), (0, 22, 7), (0, 1, 2), (0, 24, 4), (0, 25, 6), (0, 26, 7), (0, 27, 8)]),
    (12, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 1, 2), (0, 10, 3), (0, 11, 8), (0, 1, 2), (0, 13, 4), (0, 14, 5), (0, 15, 6), (0, 16, 8), (0, 17, 9), (0, 1, 2), (0, 19, 3), (0, 20, 4), (0, 21, 5), (0, 22, 7), (0, 0, 1), (0, 24, 2), (0, 25, 3), (0, 26, 4), (0, 27, 5), (0, 28, 7)]),
    (13, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 0, 1), (0, 10, 2), (0, 11, 6), (0, 12, 7), (0, 13, 8), (0, 0, 1), (0, 15, 4), (0, 16, 9), (0, 2, 6), (0, 18, 8), (0, 19, 9), (0, 1, 7), (0, 21, 9)]),
    (14, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 1, 2), (0, 10, 4), (0, 11, 6), (0, 12, 7), (0, 13, 8), (0, 14, 9), (0, 0, 3), (0, 16, 5), (0, 17, 6), (0, 18, 8), (0, 19, 9), (0, 0, 1), (0, 21, 4), (0, 22, 7), (0, 23, 8), (0, 0, 1), (0, 25, 3), (0, 26, 4), (0, 27, 5), (0, 28, 6), (0, 29, 7), (0, 30, 9)]),
    (15, [(1, 0, 0), (1, 7, 0), (1, 8, 0), (0, 0, 4), (0, 10, 7), (0, 0, 2), (0, 12, 4), (0, 13, 5), (0, 14, 6), (0, 15, 8), (0, 1, 3), (0, 17, 6), (0, 18, 7), (0, 19, 8), (0, 20, 9), (0, 0, 1), (0, 22, 2), (0, 23, 3), (0, 24, 5), (0, 25, 9)])]

@[expose] def gensc10 : List (ℕ → ℕ) := [act10 g1Arr, act10 g2Arr]

theorem chc_act_mem {W' : Subgroup W10}
    (hinv : IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W') {g : MulAut W10}
    (hg : g ∈ rImg Rc (MY mog22plus Qstd)) {u : W10} (hu : u ∈ W') : g u ∈ W' :=
  hinv (fun v => g v) ⟨g, hg, rfl⟩ u hu

theorem chc_Rc_g1_mem : Rc g1Elt ∈ rImg Rc (MY mog22plus Qstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem Rc
    (show g1Elt ∈ (MY mog22plus Qstd).subgroupOf mog22plus from
      g1Perm_mem_MY g1Perm_mem_mog22plus)

theorem chc_Rc_g2_mem : Rc g2Elt ∈ rImg Rc (MY mog22plus Qstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem Rc
    (show g2Elt ∈ (MY mog22plus Qstd).subgroupOf mog22plus from
      g2Perm_mem_MY g2Perm_mem_mog22plus)

theorem chc_gens_closed (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W') :
    ∀ f ∈ gensc10, ∀ a, toW 10 a ∈ W' → toW 10 (f a) ∈ W' := by
  intro f hf a ha
  unfold gensc10 at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [← Rc_g1 a]
    exact chc_act_mem hinv chc_Rc_g1_mem ha
  · rw [List.mem_singleton] at hf
    subst hf
    rw [← Rc_g2 a]
    exact chc_act_mem hinv chc_Rc_g2_mem ha

theorem chc_basis_of_slp (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W')
    (items : List ℕ) (prog : List (ℕ × ℕ × ℕ)) (hi : ∀ a ∈ items, toW 10 a ∈ W')
    (l : List ℕ) (hl : ∀ b ∈ l, b ∈ slpRun gensc10 items prog) :
    ∀ b ∈ l, toW 10 b ∈ W' :=
  fun b hb => ch_slpRun_sound gensc10 (fun a => toW 10 a ∈ W') (ch_zero_mem W')
    (ch_xor_closed W') (chc_gens_closed W' hinv) prog items hi b (hl b hb)

theorem chc_cert6 : ∀ r ∈ reps6,
    ∃ p ∈ slp6, p.1 = r ∧ ∀ b ∈ w6, b ∈ slpRun gensc10 (r :: w2) p.2 := by
  decide +kernel

theorem chc_cert6comb : ∀ m ∈ combos w6, m ∉ combos w2 → ∃ r ∈ reps6, m ^^^ r ∈ combos w2 := by
  decide +kernel

theorem chc_cert10 : ∀ r ∈ reps10,
    ∃ p ∈ slp10, p.1 = r ∧ ∀ b ∈ w10, b ∈ slpRun gensc10 (r :: w6) p.2 := by
  decide +kernel

theorem chc_cert10comb : ∀ m < 2 ^ 10, m ∉ combos w6 → ∃ r ∈ reps10, m ^^^ r ∈ combos w6 := by
  decide +kernel

theorem chc_w2_mem : ∀ b ∈ w2, b ∈ combos w2 := by decide +kernel

theorem chc_w6_mem : ∀ b ∈ w6, b ∈ combos w6 := by decide +kernel

theorem chc_isActsInv_of_inv (U : Subgroup W10)
    (h : ∀ g ∈ rImg Rc (MY mog22plus Qstd), ∀ u ∈ U, g u ∈ U) :
    IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) U := by
  rintro f ⟨g, hg, rfl⟩ u hu
  exact h g hg u hu

theorem chc_isActsInv_bot :
    IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) (⊥ : Subgroup W10) := by
  rintro f ⟨g, -, rfl⟩ u hu
  rw [Subgroup.mem_bot] at hu ⊢
  subst hu
  exact ch_mulAut_map_one g

theorem chc_isActsInv_top :
    IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) (⊤ : Subgroup W10) :=
  fun _ _ _ _ => Subgroup.mem_top _

theorem chc_chief_of (X Y : Subgroup W10) (hlt : X < Y)
    (hX : IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) X)
    (hY : IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) Y)
    (hmin : ∀ W : Subgroup W10, X ≤ W → W ≤ Y →
      IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W → W = X ∨ W = Y) :
    IsChiefFactorUnder (actsOnModule (rImg Rc (MY mog22plus Qstd))) X Y := by
  unfold IsChiefFactorUnder
  exact ⟨hlt, hX, hY, hmin⟩

theorem chc_minimal_of_card {A : Type*} [Group A] [Finite A] (X Y : Subgroup A) {k : ℕ}
    (hX : Nat.card ↥X = 2 ^ k) (hY : Nat.card ↥Y = 2 ^ (k + 1)) (W : Subgroup A) (h1 : X ≤ W)
    (h2 : W ≤ Y) : W = X ∨ W = Y := by
  have hd1 : Nat.card X ∣ Nat.card W := Subgroup.card_dvd_of_le h1
  have hd2 : Nat.card W ∣ Nat.card Y := Subgroup.card_dvd_of_le h2
  rw [hY] at hd2
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  rw [hX, hci] at hd1
  have hik : k ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hd1
  rcases (show i = k ∨ i = k + 1 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (le_of_eq (by rw [hci, hX]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (le_of_eq (by rw [hci, hY]))

theorem chc_card_W10 : Nat.card W10 = 2 ^ 10 := by
  rw [Nat.card_eq_fintype_card]
  exact card_Wn 10

theorem chc_bot_lt_X1 : (⊥ : Subgroup W10) < X1 := by
  refine lt_of_le_of_ne bot_le (fun h => ?_)
  have h1 := card_X1
  rw [← h, Subgroup.card_bot] at h1
  norm_num at h1

theorem chc_X1_lt_X2 : X1 < X2 := by
  refine lt_of_le_of_ne X1_le_X2 (fun h => ?_)
  have h1 : Nat.card X1 = Nat.card X2 := by rw [h]
  rw [card_X1, card_X2] at h1
  norm_num at h1

theorem chc_X2_lt_X6 : X2 < X6 := by
  refine lt_of_le_of_ne X2_le_X6 (fun h => ?_)
  have h1 : Nat.card X2 = Nat.card X6 := by rw [h]
  rw [card_X2, card_X6] at h1
  norm_num at h1

theorem chc_X6_lt_top : X6 < ⊤ := by
  refine lt_top_iff_ne_top.2 (fun h => ?_)
  have h1 : Nat.card X6 = Nat.card W10 := by rw [h, Subgroup.card_top]
  rw [card_X6, chc_card_W10] at h1
  norm_num at h1

theorem maskSub_w10_eq_top : maskSub 10 w10 = ⊤ :=
  Subgroup.eq_top_of_card_eq _ (by rw [card_X10, chc_card_W10])

theorem X1_minimal :
    ∀ W' : Subgroup W10, ⊥ ≤ W' → W' ≤ X1 → W' = ⊥ ∨ W' = X1 := by
  intro W' h1 h2
  exact chc_minimal_of_card (⊥ : Subgroup W10) X1 (k := 0) (by rw [Subgroup.card_bot]; norm_num)
    (by rw [card_X1]) W' h1 h2

theorem X2_minimal :
    ∀ W' : Subgroup W10, X1 ≤ W' → W' ≤ X2 → W' = X1 ∨ W' = X2 := by
  intro W' h1 h2
  exact chc_minimal_of_card X1 X2 (k := 1) card_X1 card_X2 W' h1 h2

theorem X6_minimal :
    ∀ W' : Subgroup W10, X2 ≤ W' → W' ≤ X6 →
      IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W' → W' = X2 ∨ W' = X6 := by
  intro W' h2 h6 hinv
  by_cases heq : W' = X2
  · exact Or.inl heq
  right
  obtain ⟨v, hvW, hvX2⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h2 (Ne.symm heq))
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hm6 : m ∈ combos w6 := (toW_mem_X6_iff hm).1 (h6 hvW)
  have hm2 : m ∉ combos w2 := fun h => hvX2 ((toW_mem_X2_iff hm).2 h)
  obtain ⟨r, hr, hsr⟩ := chc_cert6comb m hm6 hm2
  have hrW : toW 10 r ∈ W' := by
    have hs : toW 10 (m ^^^ r) ∈ W' := h2 (toW_mem_maskSub (n := 10) hsr)
    have hid : toW 10 r = toW 10 m * toW 10 (m ^^^ r) := by
      rw [← toW_xor, ch_xor_cancel]
    rw [hid]
    exact W'.mul_mem hvW hs
  obtain ⟨p, _, _, hgen⟩ := chc_cert6 r hr
  have hi : ∀ a ∈ r :: w2, toW 10 a ∈ W' := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hrW
    · exact h2 (toW_mem_maskSub (n := 10) (chc_w2_mem a ha))
  exact le_antisymm h6 (ch_maskSub_le W' w6 (chc_basis_of_slp W' hinv (r :: w2) p.2 hi w6 hgen))

theorem top_minimal_X6 :
    ∀ W' : Subgroup W10, X6 ≤ W' →
      IsActsInv (actsOnModule (rImg Rc (MY mog22plus Qstd))) W' → W' = X6 ∨ W' = ⊤ := by
  intro W' h6 hinv
  by_cases heq : W' = X6
  · exact Or.inl heq
  right
  obtain ⟨v, hvW, hvX6⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h6 (Ne.symm heq))
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hm6 : m ∉ combos w6 := fun h => hvX6 ((toW_mem_X6_iff hm).2 h)
  obtain ⟨r, hr, hsr⟩ := chc_cert10comb m hm hm6
  have hrW : toW 10 r ∈ W' := by
    have hs : toW 10 (m ^^^ r) ∈ W' := h6 (toW_mem_maskSub (n := 10) hsr)
    have hid : toW 10 r = toW 10 m * toW 10 (m ^^^ r) := by
      rw [← toW_xor, ch_xor_cancel]
    rw [hid]
    exact W'.mul_mem hvW hs
  obtain ⟨p, _, _, hgen⟩ := chc_cert10 r hr
  have hi : ∀ a ∈ r :: w6, toW 10 a ∈ W' := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hrW
    · exact h6 (toW_mem_maskSub (n := 10) (chc_w6_mem a ha))
  have hle : maskSub 10 w10 ≤ W' :=
    ch_maskSub_le W' w10 (chc_basis_of_slp W' hinv (r :: w6) p.2 hi w10 hgen)
  rw [maskSub_w10_eq_top] at hle
  exact top_le_iff.1 hle

theorem chain_std_X :
    IsChiefFactorUnder (actsOnModule (rImg Rc (MY mog22plus Qstd))) ⊥ X1 ∧
    IsChiefFactorUnder (actsOnModule (rImg Rc (MY mog22plus Qstd))) X1 X2 ∧
    IsChiefFactorUnder (actsOnModule (rImg Rc (MY mog22plus Qstd))) X2 X6 ∧
    IsChiefFactorUnder (actsOnModule (rImg Rc (MY mog22plus Qstd))) X6 ⊤ := by
  have hA := chc_isActsInv_of_inv X1 inv_X1
  have hB := chc_isActsInv_of_inv X2 inv_X2
  have hC := chc_isActsInv_of_inv X6 inv_X6
  exact ⟨chc_chief_of _ _ chc_bot_lt_X1 chc_isActsInv_bot hA (fun W h1 h2 _ => X1_minimal W h1 h2),
    chc_chief_of _ _ chc_X1_lt_X2 hA hB (fun W h1 h2 _ => X2_minimal W h1 h2),
    chc_chief_of _ _ chc_X2_lt_X6 hB hC (fun W h1 h2 h3 => X6_minimal W h1 h2 h3),
    chc_chief_of _ _ chc_X6_lt_top hC chc_isActsInv_top (fun W h1 _ h3 => top_minimal_X6 W h1 h3)⟩

end CFSG.Quasithin.RonanH154
