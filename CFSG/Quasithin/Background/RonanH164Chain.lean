module

public import CFSG.Quasithin.Background.RonanH164Gen
public import CFSG.Quasithin.Background.RonanH164Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def slpRun4 (gens : List (ℕ → ℕ)) : List ℕ → List (ℕ × ℕ × ℕ) → List ℕ
  | items, [] => items
  | items, (op, i, j) :: prog =>
    slpRun4 gens (items ++ [if op = 0 then items.getD i 0 ^^^ items.getD j 0
      else (gens.getD (op - 1) (fun _ => 0)) (items.getD i 0)]) prog

@[expose] def gensH : List (ℕ → ℕ) := [actC10 x6Arr, actC10 tauArr]

theorem ch4_getD_T (T : ℕ → Prop) (h0 : T 0) (items : List ℕ) (hi : ∀ a ∈ items, T a) (k : ℕ) :
    T (items.getD k 0) := by
  by_cases hk : k < items.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hi _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (show items.length ≤ k by omega)]
    exact h0

theorem ch4_getD_gen (gens : List (ℕ → ℕ)) (T : ℕ → Prop) (h0 : T 0)
    (hg : ∀ f ∈ gens, ∀ a, T a → T (f a)) (k a : ℕ) (ha : T a) :
    T ((gens.getD k (fun _ => 0)) a) := by
  by_cases hk : k < gens.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hg _ (List.getElem_mem hk) a ha
  · rw [List.getD_eq_default _ _ (show gens.length ≤ k by omega)]
    exact h0

theorem ch4_slpRun_sound (gens : List (ℕ → ℕ)) (T : ℕ → Prop) (h0 : T 0)
    (hx : ∀ a b, T a → T b → T (a ^^^ b)) (hg : ∀ f ∈ gens, ∀ a, T a → T (f a)) :
    ∀ (prog : List (ℕ × ℕ × ℕ)) (items : List ℕ), (∀ a ∈ items, T a) →
      ∀ a ∈ slpRun4 gens items prog, T a
  | [], items, hi => hi
  | (op, i, j) :: prog, items, hi => by
    rw [slpRun4]
    refine ch4_slpRun_sound gens T h0 hx hg prog _ fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · exact hi a ha
    · rw [List.mem_singleton] at ha
      rw [ha]
      split
      · exact hx _ _ (ch4_getD_T T h0 items hi i) (ch4_getD_T T h0 items hi j)
      · exact ch4_getD_gen gens T h0 hg _ _ (ch4_getD_T T h0 items hi i)

theorem ch4_xor_cancel (m r : ℕ) : m ^^^ (m ^^^ r) = r := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem ch4_zero_mem (W' : Subgroup W10) : toW 10 0 ∈ W' := by
  rw [toW_zero]
  exact W'.one_mem

theorem ch4_xor_closed (W' : Subgroup W10) (a b : ℕ) (ha : toW 10 a ∈ W') (hb : toW 10 b ∈ W') :
    toW 10 (a ^^^ b) ∈ W' := by
  rw [toW_xor]
  exact W'.mul_mem ha hb

theorem ch4_R_x6_mem : R x6Elt ∈ rImg R (MY mog22plus Hstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem R
    (show x6Elt ∈ (MY mog22plus Hstd).subgroupOf mog22plus from x6_mem_MY_H)

theorem ch4_R_tau_mem : R tauElt ∈ rImg R (MY mog22plus Hstd) := by
  unfold rImg
  exact Subgroup.mem_map_of_mem R
    (show tauElt ∈ (MY mog22plus Hstd).subgroupOf mog22plus from tau_mem_MY_H)

theorem ch4_act_memH {W' : Subgroup W10}
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) W') {g : MulAut W10}
    (hg : g ∈ rImg R (MY mog22plus Hstd)) {u : W10} (hu : u ∈ W') : g u ∈ W' :=
  hinv (fun v => g v) ⟨g, hg, rfl⟩ u hu

theorem ch4_gens_closedH (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) W') :
    ∀ f ∈ gensH, ∀ a, toW 10 a ∈ W' → toW 10 (f a) ∈ W' := by
  intro f hf a ha
  unfold gensH at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [← R_x6 a]
    exact ch4_act_memH hinv ch4_R_x6_mem ha
  · rw [List.mem_singleton] at hf
    subst hf
    rw [← R_tau a]
    exact ch4_act_memH hinv ch4_R_tau_mem ha

theorem ch4_basis_of_slpH (W' : Subgroup W10)
    (hinv : IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) W')
    (items : List ℕ) (prog : List (ℕ × ℕ × ℕ)) (hi : ∀ a ∈ items, toW 10 a ∈ W')
    (l : List ℕ) (hl : ∀ b ∈ l, b ∈ slpRun4 gensH items prog) :
    ∀ b ∈ l, toW 10 b ∈ W' :=
  fun b hb => ch4_slpRun_sound gensH (fun a => toW 10 a ∈ W') (ch4_zero_mem W')
    (ch4_xor_closed W') (ch4_gens_closedH W' hinv) prog items hi b (hl b hb)

theorem ch4_maskSub_le (W' : Subgroup W10) (l : List ℕ) (hl : ∀ b ∈ l, toW 10 b ∈ W') :
    maskSub 10 l ≤ W' := by
  intro u hu
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hu
  exact mem_of_combos (fun a => toW 10 a ∈ W') (ch4_zero_mem W') (ch4_xor_closed W') l hl m hm

theorem ch4_cert5comb : ∀ m ∈ combos c5, m ∉ combos c1 → ∃ r ∈ reps5, m ^^^ r ∈ combos c1 := by
  decide +kernel

theorem ch4_cert5 : ∀ r ∈ reps5,
    ∃ p ∈ slp5, p.1 = r ∧ ∀ b ∈ c5, b ∈ slpRun4 gensH (r :: c1) p.2 := by
  decide +kernel

theorem ch4_cert10comb : ∀ m ∈ combos c10, m ∉ combos c6 → ∃ r ∈ reps10, m ^^^ r ∈ combos c6 := by
  decide +kernel

theorem ch4_cert10 : ∀ r ∈ reps10,
    ∃ p ∈ slp10, p.1 = r ∧ ∀ b ∈ c10, b ∈ slpRun4 gensH (r :: c6) p.2 := by
  decide +kernel

theorem ch4_c1_mem : ∀ b ∈ c1, b ∈ combos c1 := by decide +kernel

theorem ch4_c6_mem : ∀ b ∈ c6, b ∈ combos c6 := by decide +kernel

theorem ch4_mask_lt_c10 : ∀ a ∈ c10, a < 2 ^ 10 := by decide +kernel

theorem ch4_nodup_c10 : (combos c10).Nodup :=
  (nodup_of_nodupB (combos c10) 0 (by decide +kernel)).1

theorem ch4_card_W10 : Nat.card W10 = 2 ^ 10 := by
  rw [Nat.card_eq_fintype_card]
  exact card_Wn 10

theorem ch4_card_c10 : Nat.card ↥(maskSub 10 c10) = 2 ^ 10 :=
  card_maskSub ch4_mask_lt_c10 ch4_nodup_c10

theorem ch4_c10_top : maskSub 10 c10 = (⊤ : Subgroup W10) :=
  Subgroup.eq_top_of_card_eq _ (by rw [ch4_card_c10, ch4_card_W10])

theorem ch4_mem_c10 {m : ℕ} (hm : m < 2 ^ 10) : m ∈ combos c10 := by
  have h : toW 10 m ∈ maskSub 10 c10 := by
    rw [ch4_c10_top]
    exact Subgroup.mem_top _
  obtain ⟨m', hm', he⟩ := mem_maskSub.1 h
  rw [toW_inj (combos_lt (n := 10) ch4_mask_lt_c10 m' hm') hm he] at hm'
  exact hm'

theorem ch4_isActsInv_of_invH (U : Subgroup W10)
    (h : ∀ g ∈ rImg R (MY mog22plus Hstd), ∀ u ∈ U, g u ∈ U) :
    IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) U := by
  rintro f ⟨g, hg, rfl⟩ u hu
  exact h g hg u hu

theorem ch4_mulAut_map_one {V : Type*} [CommGroup V] (g : MulAut V) : g 1 = 1 := map_one g

theorem ch4_isActsInv_bot {Y : Subgroup (MulAut W10)} :
    IsActsInv (actsOnModule Y) (⊥ : Subgroup W10) := by
  rintro f ⟨g, -, rfl⟩ u hu
  rw [Subgroup.mem_bot] at hu ⊢
  subst hu
  exact ch4_mulAut_map_one g

theorem ch4_isActsInv_top {Y : Subgroup (MulAut W10)} :
    IsActsInv (actsOnModule Y) (⊤ : Subgroup W10) :=
  fun _ _ _ _ => Subgroup.mem_top _

theorem ch4_chief_of {A : Type*} [Group A] (acts : Set (A → A)) (X Y : Subgroup A) (hlt : X < Y)
    (hX : IsActsInv acts X) (hY : IsActsInv acts Y)
    (hmin : ∀ W : Subgroup A, X ≤ W → W ≤ Y → IsActsInv acts W → W = X ∨ W = Y) :
    IsChiefFactorUnder acts X Y := by
  unfold IsChiefFactorUnder
  exact ⟨hlt, hX, hY, hmin⟩

theorem ch4_bot_lt_V1 : (⊥ : Subgroup W10) < V1 := by
  refine lt_of_le_of_ne bot_le (fun h => ?_)
  have h1 := card_V1
  rw [← h, Subgroup.card_bot] at h1
  norm_num at h1

theorem ch4_V1_lt_V5 : V1 < V5 := by
  refine lt_of_le_of_ne V1_le_V5 (fun h => ?_)
  have h1 : Nat.card V1 = Nat.card V5 := by rw [h]
  rw [card_V1, card_V5] at h1
  norm_num at h1

theorem ch4_V5_lt_V6 : V5 < V6 := by
  refine lt_of_le_of_ne V5_le_V6 (fun h => ?_)
  have h1 : Nat.card V5 = Nat.card V6 := by rw [h]
  rw [card_V5, card_V6] at h1
  norm_num at h1

theorem ch4_V6_lt_top : V6 < ⊤ := by
  refine lt_top_iff_ne_top.2 (fun h => ?_)
  have h1 : Nat.card V6 = Nat.card W10 := by rw [h, Subgroup.card_top]
  rw [card_V6, ch4_card_W10] at h1
  norm_num at h1

theorem V1_minimal : ∀ W' : Subgroup W10, W' ≤ V1 → W' = ⊥ ∨ W' = V1 := by
  intro W' hle
  have hd : Nat.card W' ∣ 2 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [card_V1, pow_one] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
  · exact Or.inl (Subgroup.card_eq_one.1 h1)
  · right
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h1, card_V1, pow_one]))

theorem V5_minimal :
    ∀ W' : Subgroup W10, V1 ≤ W' → W' ≤ V5 →
      IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) W' → W' = V1 ∨ W' = V5 := by
  intro W' h1 h5 hinv
  by_cases heq : W' = V1
  · exact Or.inl heq
  right
  obtain ⟨v, hvW, hvV1⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h1 (Ne.symm heq))
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hmV5 : m ∈ combos c5 := (toW_mem_V5_iff hm).1 (h5 hvW)
  have hmV1 : m ∉ combos c1 := fun h => hvV1 ((toW_mem_V1_iff hm).2 h)
  obtain ⟨r, hr, hsr⟩ := ch4_cert5comb m hmV5 hmV1
  have hrW : toW 10 r ∈ W' := by
    have hs : toW 10 (m ^^^ r) ∈ W' := h1 (toW_mem_maskSub (n := 10) hsr)
    have hid : toW 10 r = toW 10 m * toW 10 (m ^^^ r) := by
      rw [← toW_xor, ch4_xor_cancel]
    rw [hid]
    exact W'.mul_mem hvW hs
  obtain ⟨p, _, _, hgen⟩ := ch4_cert5 r hr
  have hi : ∀ a ∈ r :: c1, toW 10 a ∈ W' := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hrW
    · exact h1 (toW_mem_maskSub (n := 10) (ch4_c1_mem a ha))
  exact le_antisymm h5 (ch4_maskSub_le W' c5 (ch4_basis_of_slpH W' hinv (r :: c1) p.2 hi c5 hgen))

theorem V6_minimal : ∀ W' : Subgroup W10, V5 ≤ W' → W' ≤ V6 → W' = V5 ∨ W' = V6 := by
  intro W' h5 h6
  have hd1 : Nat.card V5 ∣ Nat.card W' := Subgroup.card_dvd_of_le h5
  have hd2 : Nat.card W' ∣ Nat.card V6 := Subgroup.card_dvd_of_le h6
  rw [card_V6] at hd2
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
  rw [card_V5, hci] at hd1
  have hi5 : 5 ≤ i := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hd1
  rcases (show i = 5 ∨ i = 6 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h5 (le_of_eq (by rw [hci, card_V5]))).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h6 (le_of_eq (by rw [hci, card_V6]))

theorem top6_minimal :
    ∀ W' : Subgroup W10, V6 ≤ W' → IsActsInv (actsOnModule (rImg R (MY mog22plus Hstd))) W' →
      W' = V6 ∨ W' = ⊤ := by
  intro W' h6 hinv
  by_cases heq : W' = V6
  · exact Or.inl heq
  right
  obtain ⟨v, hvW, hvV6⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h6 (Ne.symm heq))
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  have hmC10 : m ∈ combos c10 := ch4_mem_c10 hm
  have hmC6 : m ∉ combos c6 := fun h => hvV6 ((toW_mem_V6_iff hm).2 h)
  obtain ⟨r, hr, hsr⟩ := ch4_cert10comb m hmC10 hmC6
  have hrW : toW 10 r ∈ W' := by
    have hs : toW 10 (m ^^^ r) ∈ W' := h6 (toW_mem_maskSub (n := 10) hsr)
    have hid : toW 10 r = toW 10 m * toW 10 (m ^^^ r) := by
      rw [← toW_xor, ch4_xor_cancel]
    rw [hid]
    exact W'.mul_mem hvW hs
  obtain ⟨p, _, _, hgen⟩ := ch4_cert10 r hr
  have hi : ∀ a ∈ r :: c6, toW 10 a ∈ W' := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hrW
    · exact h6 (toW_mem_maskSub (n := 10) (ch4_c6_mem a ha))
  have hT : (⊤ : Subgroup W10) ≤ W' := by
    rw [← ch4_c10_top]
    exact ch4_maskSub_le W' c10 (ch4_basis_of_slpH W' hinv (r :: c6) p.2 hi c10 hgen)
  exact le_antisymm le_top hT

theorem chain164_std :
    Chain164 R Hstd V5 V6 := by
  unfold Chain164
  rw [KY_H_L2, fixV_fixO]
  have hA := ch4_isActsInv_of_invH V1 inv_V1
  have hB := ch4_isActsInv_of_invH V5 inv_V5
  have hC := ch4_isActsInv_of_invH V6 inv_V6
  refine ⟨ch4_chief_of _ _ _ ch4_bot_lt_V1 ch4_isActsInv_bot hA
      (fun W _ h1 _ => V1_minimal W h1),
    rk_V1, ch4_chief_of _ _ _ ch4_V1_lt_V5 hA hB (fun W h1 h2 h3 => V5_minimal W h1 h2 h3),
    rk_V5, commV_fixO.symm, ch4_chief_of _ _ _ ch4_V5_lt_V6 hB hC (fun W h1 h2 _ => V6_minimal W h1 h2),
    rk_V6, ch4_chief_of _ _ _ ch4_V6_lt_top hC ch4_isActsInv_top (fun W h1 _ h3 => top6_minimal W h1 h3)⟩

end CFSG.Quasithin.RonanH163
