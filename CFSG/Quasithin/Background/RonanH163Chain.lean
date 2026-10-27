module

public import CFSG.Quasithin.Background.RonanH163Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def slpRun (gens : List (ℕ → ℕ)) : List ℕ → List (ℕ × ℕ × ℕ) → List ℕ
  | items, [] => items
  | items, (op, i, j) :: prog =>
    slpRun gens (items ++ [if op = 0 then items.getD i 0 ^^^ items.getD j 0
      else (gens.getD (op - 1) (fun _ => 0)) (items.getD i 0)]) prog

@[expose] def slp4 : List (ℕ × List (ℕ × ℕ × ℕ)) :=
  [(1, [(1, 0, 0), (1, 1, 0), (0, 0, 1), (1, 3, 0), (2, 4, 0)]),
    (6, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 1), (0, 1, 2), (0, 3, 5)]),
    (7, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (2, 1, 0), (0, 0, 1), (0, 0, 2), (1, 4, 0), (1, 5, 0), (0, 0, 3), (0, 3, 6)]),
    (88, [(1, 0, 0), (1, 1, 0), (0, 0, 1), (1, 2, 0), (0, 0, 2), (0, 2, 3), (1, 6, 0), (0, 4, 5)]),
    (89, [(1, 0, 0), (2, 0, 0), (2, 1, 0), (1, 2, 0), (0, 0, 1), (1, 5, 0), (0, 2, 4)]),
    (94, [(1, 0, 0), (1, 1, 0), (0, 0, 1), (1, 2, 0), (2, 2, 0), (0, 0, 2), (2, 6, 0), (0, 3, 4)]),
    (95, [(1, 0, 0), (1, 1, 0), (0, 0, 1), (1, 2, 0), (1, 3, 0), (1, 5, 0), (0, 3, 4)]),
    (266, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (1, 3, 0), (0, 0, 3), (0, 2, 4)]),
    (267, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 2), (0, 1, 2), (1, 3, 0), (1, 5, 0), (0, 0, 3), (0, 3, 4), (1, 9, 0)]),
    (268, [(1, 0, 0), (1, 1, 0), (2, 1, 0), (1, 2, 0), (0, 0, 2), (0, 2, 3), (1, 4, 0), (1, 5, 0), (1, 6, 0), (0, 4, 5)]),
    (269, [(1, 0, 0), (1, 1, 0), (2, 1, 0), (0, 0, 1), (2, 2, 0), (2, 4, 0), (0, 3, 4)]),
    (338, [(1, 0, 0), (1, 1, 0), (0, 0, 1), (1, 2, 0), (2, 3, 0), (1, 4, 0)]),
    (339, [(1, 0, 0), (1, 1, 0), (2, 1, 0), (1, 2, 0), (0, 0, 2), (1, 5, 0), (0, 0, 4)]),
    (340, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 1), (0, 1, 2), (0, 3, 4), (0, 3, 5)]),
    (341, [(1, 0, 0), (2, 0, 0), (1, 2, 0), (0, 0, 1), (0, 1, 2), (2, 3, 0), (0, 0, 5)])]

@[expose] def reps8 : List ℕ := [10, 16, 26, 32, 42, 48, 58, 512, 522, 528, 538, 544, 554, 560, 570]

@[expose] def slp8 : List (ℕ × List (ℕ × ℕ × ℕ)) :=
  [(10, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 4), (1, 5, 0), (0, 6, 7), (0, 7, 8), (0, 5, 11), (0, 6, 9)]),
    (16, [(2, 0, 0), (1, 1, 0), (0, 0, 2), (1, 5, 0), (0, 5, 6), (0, 5, 7), (1, 10, 0), (0, 0, 9), (0, 5, 8)]),
    (26, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (1, 4, 0), (0, 0, 1), (0, 0, 2), (0, 0, 4), (1, 6, 0), (1, 7, 0), (2, 9, 0), (1, 10, 0), (0, 5, 6), (0, 6, 8), (0, 6, 11), (0, 12, 14), (0, 12, 17), (0, 13, 16), (0, 15, 18), (1, 19, 0)]),
    (32, [(1, 0, 0), (1, 2, 0), (0, 0, 2), (1, 5, 0), (1, 7, 0), (0, 0, 6), (1, 8, 0), (2, 9, 0), (1, 10, 0), (0, 7, 11)]),
    (42, [(1, 0, 0), (2, 0, 0), (0, 0, 2), (0, 0, 4), (1, 5, 0), (1, 6, 0), (1, 8, 0), (0, 2, 5), (0, 5, 6), (1, 11, 0), (1, 12, 0), (0, 7, 9), (0, 10, 13), (2, 15, 0)]),
    (48, [(2, 0, 0), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 2, 4), (1, 6, 0), (1, 7, 0), (0, 0, 9), (0, 5, 8), (1, 10, 0), (2, 12, 0), (1, 13, 0), (0, 0, 11)]),
    (58, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 4), (0, 2, 3), (1, 6, 0), (0, 1, 5), (0, 5, 8), (0, 5, 9), (0, 6, 7), (1, 13, 0), (1, 14, 0), (0, 10, 12)]),
    (512, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 2), (0, 0, 3), (2, 5, 0), (1, 8, 0), (0, 6, 7), (0, 6, 9), (1, 10, 0), (0, 11, 13), (2, 14, 0)]),
    (522, [(1, 0, 0), (2, 0, 0), (0, 0, 1), (1, 5, 0), (1, 6, 0), (1, 7, 0), (0, 1, 5), (0, 5, 6), (1, 8, 0), (1, 9, 0), (2, 10, 0), (1, 12, 0), (0, 8, 11), (1, 14, 0), (1, 17, 0), (0, 13, 15)]),
    (528, [(1, 0, 0), (2, 0, 0), (1, 2, 0), (0, 0, 3), (0, 0, 4), (1, 6, 0), (0, 2, 6), (0, 5, 8), (0, 7, 9), (1, 10, 0), (1, 11, 0), (2, 12, 0), (1, 13, 0)]),
    (538, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 1), (1, 6, 0), (1, 8, 0), (0, 6, 7), (2, 10, 0), (0, 0, 11), (0, 8, 9)]),
    (544, [(1, 0, 0), (2, 0, 0), (1, 1, 0), (0, 0, 2), (0, 0, 4), (0, 1, 4), (1, 5, 0), (1, 6, 0), (0, 0, 6), (0, 5, 8), (0, 5, 10), (0, 7, 9), (1, 12, 0), (1, 15, 0), (0, 11, 13), (0, 11, 16), (1, 18, 0), (1, 20, 0), (0, 14, 17)]),
    (554, [(1, 0, 0), (0, 0, 3), (0, 2, 3), (0, 2, 4), (1, 5, 0), (2, 5, 0), (1, 6, 0), (0, 5, 7), (0, 5, 8), (2, 12, 0), (0, 0, 11), (0, 9, 13), (0, 10, 13), (1, 15, 0), (2, 16, 0)]),
    (560, [(1, 0, 0), (2, 0, 0), (1, 3, 0), (0, 0, 3), (0, 0, 4), (1, 5, 0), (1, 8, 0), (1, 9, 0), (0, 5, 8), (0, 6, 7), (1, 11, 0), (1, 13, 0), (0, 0, 12), (0, 10, 14)]),
    (570, [(1, 0, 0), (2, 0, 0), (0, 0, 1), (0, 0, 3), (0, 2, 3), (0, 5, 8), (0, 6, 7), (0, 6, 9), (2, 10, 0), (1, 11, 0), (1, 12, 0), (0, 0, 12)])]

@[expose] def gensC10 : List (ℕ → ℕ) := [actC10 g1Arr, actC10 g2Arr]

theorem ch_getD_T (T : ℕ → Prop) (h0 : T 0) (items : List ℕ) (hi : ∀ a ∈ items, T a) (k : ℕ) :
    T (items.getD k 0) := by
  by_cases hk : k < items.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hi _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (show items.length ≤ k by omega)]
    exact h0

theorem ch_getD_gen (gens : List (ℕ → ℕ)) (T : ℕ → Prop) (h0 : T 0)
    (hg : ∀ f ∈ gens, ∀ a, T a → T (f a)) (k a : ℕ) (ha : T a) :
    T ((gens.getD k (fun _ => 0)) a) := by
  by_cases hk : k < gens.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hg _ (List.getElem_mem hk) a ha
  · rw [List.getD_eq_default _ _ (show gens.length ≤ k by omega)]
    exact h0

theorem ch_slpRun_sound (gens : List (ℕ → ℕ)) (T : ℕ → Prop) (h0 : T 0)
    (hx : ∀ a b, T a → T b → T (a ^^^ b)) (hg : ∀ f ∈ gens, ∀ a, T a → T (f a)) :
    ∀ (prog : List (ℕ × ℕ × ℕ)) (items : List ℕ), (∀ a ∈ items, T a) →
      ∀ a ∈ slpRun gens items prog, T a
  | [], items, hi => hi
  | (op, i, j) :: prog, items, hi => by
    rw [slpRun]
    refine ch_slpRun_sound gens T h0 hx hg prog _ fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · exact hi a ha
    · rw [List.mem_singleton] at ha
      rw [ha]
      split
      · exact hx _ _ (ch_getD_T T h0 items hi i) (ch_getD_T T h0 items hi j)
      · exact ch_getD_gen gens T h0 hg _ _ (ch_getD_T T h0 items hi i)

theorem ch_xor_cancel (m r : ℕ) : m ^^^ (m ^^^ r) = r := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem ch_zero_mem (W' : Subgroup W10) : toW 10 0 ∈ W' := by
  rw [toW_zero]
  exact W'.one_mem

theorem ch_xor_closed (W' : Subgroup W10) (a b : ℕ) (ha : toW 10 a ∈ W') (hb : toW 10 b ∈ W') :
    toW 10 (a ^^^ b) ∈ W' := by
  rw [toW_xor]
  exact W'.mul_mem ha hb

theorem ch_act_mem {W' : Subgroup W10}
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W') {g : MulAut W10}
    (hg : g ∈ rImg R (MY mog22plus Qstd)) {u : W10} (hu : u ∈ W') : g u ∈ W' :=
  hinv (fun v => g v) ⟨g, hg, rfl⟩ u hu

theorem ch_R_g1_mem : R g1Elt ∈ rImg R (MY mog22plus Qstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem R
    (show g1Elt ∈ (MY mog22plus Qstd).subgroupOf mog22plus from
      g1Perm_mem_MY g1Perm_mem_mog22plus)

theorem ch_R_g2_mem : R g2Elt ∈ rImg R (MY mog22plus Qstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem R
    (show g2Elt ∈ (MY mog22plus Qstd).subgroupOf mog22plus from
      g2Perm_mem_MY g2Perm_mem_mog22plus)

theorem ch_gens_closed (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W') :
    ∀ f ∈ gensC10, ∀ a, toW 10 a ∈ W' → toW 10 (f a) ∈ W' := by
  intro f hf a ha
  unfold gensC10 at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [← R_g1 a]
    exact ch_act_mem hinv ch_R_g1_mem ha
  · rw [List.mem_singleton] at hf
    subst hf
    rw [← R_g2 a]
    exact ch_act_mem hinv ch_R_g2_mem ha

theorem ch_basis_of_slp (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W')
    (items : List ℕ) (prog : List (ℕ × ℕ × ℕ)) (hi : ∀ a ∈ items, toW 10 a ∈ W')
    (l : List ℕ) (hl : ∀ b ∈ l, b ∈ slpRun gensC10 items prog) :
    ∀ b ∈ l, toW 10 b ∈ W' :=
  fun b hb => ch_slpRun_sound gensC10 (fun a => toW 10 a ∈ W') (ch_zero_mem W')
    (ch_xor_closed W') (ch_gens_closed W' hinv) prog items hi b (hl b hb)

theorem ch_maskSub_le (W' : Subgroup W10) (l : List ℕ) (hl : ∀ b ∈ l, toW 10 b ∈ W') :
    maskSub 10 l ≤ W' := by
  intro u hu
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hu
  exact mem_of_combos (fun a => toW 10 a ∈ W') (ch_zero_mem W') (ch_xor_closed W') l hl m hm

theorem ch_cert4 : ∀ x ∈ combos b4, x ≠ 0 →
    ∃ p ∈ slp4, p.1 = x ∧ ∀ b ∈ b4, b ∈ slpRun gensC10 [x] p.2 := by
  decide +kernel

theorem ch_cert8 : ∀ r ∈ reps8,
    ∃ p ∈ slp8, p.1 = r ∧ ∀ b ∈ b8, b ∈ slpRun gensC10 (r :: b4) p.2 := by
  decide +kernel

theorem ch_cert8comb : ∀ m ∈ combos b8, m ∉ combos b4 → ∃ r ∈ reps8, m ^^^ r ∈ combos b4 := by
  decide +kernel

theorem ch_b4_mem : ∀ b ∈ b4, b ∈ combos b4 := by decide +kernel

theorem ch_isActsInv_of_inv (U : Subgroup W10)
    (h : ∀ g ∈ rImg R (MY mog22plus Qstd), ∀ u ∈ U, g u ∈ U) :
    IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) U := by
  rintro f ⟨g, hg, rfl⟩ u hu
  exact h g hg u hu

theorem ch_mulAut_map_one {V : Type*} [CommGroup V] (g : MulAut V) : g 1 = 1 := map_one g

theorem ch_isActsInv_bot :
    IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) (⊥ : Subgroup W10) := by
  rintro f ⟨g, -, rfl⟩ u hu
  rw [Subgroup.mem_bot] at hu ⊢
  subst hu
  exact ch_mulAut_map_one g

theorem ch_isActsInv_top :
    IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) (⊤ : Subgroup W10) :=
  fun _ _ _ _ => Subgroup.mem_top _

theorem ch_chief_of (X Y : Subgroup W10) (hlt : X < Y)
    (hX : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) X)
    (hY : IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) Y)
    (hmin : ∀ W : Subgroup W10, X ≤ W → W ≤ Y →
      IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W → W = X ∨ W = Y) :
    IsChiefFactorUnder (actsOnModule (rImg R (MY mog22plus Qstd))) X Y := by
  unfold IsChiefFactorUnder
  exact ⟨hlt, hX, hY, hmin⟩

theorem ch_card_W10 : Nat.card W10 = 2 ^ 10 := by
  rw [Nat.card_eq_fintype_card]
  exact card_Wn 10

theorem ch_bot_lt_U4 : (⊥ : Subgroup W10) < U4 := by
  refine lt_of_le_of_ne bot_le (fun h => ?_)
  have h1 := card_U4
  rw [← h, Subgroup.card_bot] at h1
  norm_num at h1

theorem ch_U4_lt_U8 : U4 < U8 := by
  refine lt_of_le_of_ne U4_le_U8 (fun h => ?_)
  have h1 : Nat.card U4 = Nat.card U8 := by rw [h]
  rw [card_U4, card_U8] at h1
  norm_num at h1

theorem ch_U8_lt_U9 : U8 < U9 := by
  refine lt_of_le_of_ne U8_le_U9 (fun h => ?_)
  have h1 : Nat.card U8 = Nat.card U9 := by rw [h]
  rw [card_U8, card_U9] at h1
  norm_num at h1

theorem ch_U9_lt_top : U9 < ⊤ := by
  refine lt_top_iff_ne_top.2 (fun h => ?_)
  have h1 : Nat.card U9 = Nat.card W10 := by rw [h, Subgroup.card_top]
  rw [card_U9, ch_card_W10] at h1
  norm_num at h1

theorem U4_minimal :
    ∀ W' : Subgroup W10, W' ≤ U4 → IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W' →
      W' = ⊥ ∨ W' = U4 := by
  intro W' hle hinv
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ W', v ≠ 1 := by
    by_contra h
    apply hbot
    refine (Subgroup.eq_bot_iff_forall W').2 fun v hv => ?_
    by_contra hv1
    exact h ⟨v, hv, hv1⟩
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hmU4 : m ∈ combos b4 := (toW_mem_U4_iff hm).1 (hle hv)
  have hm0 : m ≠ 0 := fun h => hv1 (by rw [h, toW_zero])
  obtain ⟨p, _, _, hgen⟩ := ch_cert4 m hmU4 hm0
  have hi : ∀ a ∈ [m], toW 10 a ∈ W' := fun a ha => by
    rw [List.mem_singleton.1 ha]
    exact hv
  exact le_antisymm hle (ch_maskSub_le W' b4 (ch_basis_of_slp W' hinv [m] p.2 hi b4 hgen))

theorem U8_minimal :
    ∀ W' : Subgroup W10, U4 ≤ W' → W' ≤ U8 →
      IsActsInv (actsOnModule (rImg R (MY mog22plus Qstd))) W' → W' = U4 ∨ W' = U8 := by
  intro W' h4 h8 hinv
  by_cases heq : W' = U4
  · exact Or.inl heq
  right
  obtain ⟨v, hvW, hvU4⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h4 (Ne.symm heq))
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hmU8 : m ∈ combos b8 := (toW_mem_U8_iff hm).1 (h8 hvW)
  have hmU4 : m ∉ combos b4 := fun h => hvU4 ((toW_mem_U4_iff hm).2 h)
  obtain ⟨r, hr, hsr⟩ := ch_cert8comb m hmU8 hmU4
  have hrW : toW 10 r ∈ W' := by
    have hs : toW 10 (m ^^^ r) ∈ W' := h4 (toW_mem_maskSub (n := 10) hsr)
    have hid : toW 10 r = toW 10 m * toW 10 (m ^^^ r) := by
      rw [← toW_xor, ch_xor_cancel]
    rw [hid]
    exact W'.mul_mem hvW hs
  obtain ⟨p, _, _, hgen⟩ := ch_cert8 r hr
  have hi : ∀ a ∈ r :: b4, toW 10 a ∈ W' := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hrW
    · exact h4 (toW_mem_maskSub (n := 10) (ch_b4_mem a ha))
  exact le_antisymm h8 (ch_maskSub_le W' b8 (ch_basis_of_slp W' hinv (r :: b4) p.2 hi b8 hgen))

theorem U9_minimal :
    ∀ W' : Subgroup W10, U8 ≤ W' → W' ≤ U9 → W' = U8 ∨ W' = U9 := by
  intro W' h8 h9
  have hd1 : Nat.card U8 ∣ Nat.card W' := Subgroup.card_dvd_of_le h8
  have hd2 : Nat.card W' ∣ Nat.card U9 := Subgroup.card_dvd_of_le h9
  rw [card_U9] at hd2
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  rw [card_U8, hci] at hd1
  have hi8 : 8 ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hd1
  rcases (show i = 8 ∨ i = 9 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h8 (le_of_eq (by rw [hci, card_U8]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h9 (le_of_eq (by rw [hci, card_U9]))

theorem top_minimal : ∀ W' : Subgroup W10, U9 ≤ W' → W' = U9 ∨ W' = ⊤ := by
  intro W' h9
  have hd1 : Nat.card U9 ∣ Nat.card W' := Subgroup.card_dvd_of_le h9
  have hd2 : Nat.card W' ∣ Nat.card W10 := by
    have h := Subgroup.card_dvd_of_le (le_top : W' ≤ ⊤)
    rwa [Subgroup.card_top] at h
  rw [ch_card_W10] at hd2
  rw [card_U9] at hd1
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  rw [hci] at hd1
  have hi9 : 9 ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hd1
  rcases (show i = 9 ∨ i = 10 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h9 (le_of_eq (by rw [hci, card_U9]))).symm
  · right
    exact Subgroup.eq_top_of_card_eq _ (by rw [hci, ch_card_W10])

theorem chain_std :
    Chain163 R Qstd U8 U9 := by
  unfold Chain163
  rw [KY_Q_L2, fixV_NQ2]
  have hA := ch_isActsInv_of_inv U4 inv_U4
  have hB := ch_isActsInv_of_inv U8 inv_U8
  have hC := ch_isActsInv_of_inv U9 inv_U9
  refine ⟨ch_chief_of _ _ ch_bot_lt_U4 ch_isActsInv_bot hA
      (fun W _ h1 h2 => U4_minimal W h1 h2),
    rk_U4, ch_chief_of _ _ ch_U4_lt_U8 hA hB (fun W h1 h2 h3 => U8_minimal W h1 h2 h3),
    rk_U8, ch_chief_of _ _ ch_U8_lt_U9 hB hC (fun W h1 h2 _ => U9_minimal W h1 h2),
    rk_U9, ch_chief_of _ _ ch_U9_lt_top hC ch_isActsInv_top (fun W h1 _ _ => top_minimal W h1)⟩

end CFSG.Quasithin.RonanH163
