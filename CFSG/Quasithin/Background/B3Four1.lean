module

public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Quasithin.Background.B3Flag
public import CFSG.Quasithin.Background.B3O2
public import CFSG.Quasithin.Background.B3VMod

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}

theorem mem_tab_iff (σ : Gp n) (x : ℕ) : x ∈ tab σ ↔ x < n := by
  simp only [tab, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact (σ i).isLt
  · intro hx
    exact ⟨σ.symm ⟨x, hx⟩, by simp⟩

theorem tab_perm_range (σ : Gp n) : (tab σ).Perm (List.range n) :=
  List.perm_of_nodup_nodup_toFinset_eq (nodup_tab σ) List.nodup_range
    (by ext x; simp [mem_tab_iff, List.mem_range])

theorem tab_mem_allTabs (σ : Gp n) : tab σ ∈ allTabs n :=
  List.mem_permutations.2 (tab_perm_range σ)

theorem isTab_of_mem_allTabs {t : Tab} (h : t ∈ allTabs n) : isTab n t = true := by
  have h' : t.Perm (List.range n) := List.mem_permutations.1 h
  simp only [isTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨by simpa using h'.length_eq, fun x hx => ?_⟩, ?_⟩
  · have := h'.mem_iff.1 hx
    simpa using this
  · exact h'.nodup_iff.2 List.nodup_range

@[expose] def Hg (n : ℕ) (b : Bool) : Subgroup (Gp n) :=
  if b then ⊤ else alternatingGroup (Fin n)

theorem Hl_spec (b : Bool) :
    (∀ σ : Gp n, σ ∈ Hg n b ↔ tab σ ∈ Hl n b) ∧ ∀ t ∈ Hl n b, ∃ σ ∈ Hg n b, tab σ = t := by
  cases b
  · refine ⟨fun σ => ?_, fun t ht => ?_⟩
    · simp only [Hg, Hl, evenTabs, Bool.false_eq_true, ↓reduceIte, List.mem_filter]
      rw [mem_alternatingGroup_iff]
      exact ⟨fun h => ⟨tab_mem_allTabs σ, h⟩, fun h => h.2⟩
    · simp only [Hg, Hl, evenTabs, Bool.false_eq_true, ↓reduceIte, List.mem_filter] at ht ⊢
      obtain ⟨σ, rfl⟩ := exists_tab_eq (isTab_of_mem_allTabs ht.1)
      exact ⟨σ, (mem_alternatingGroup_iff σ).2 ht.2, rfl⟩
  · refine ⟨fun σ => ?_, fun t ht => ?_⟩
    · simp only [Hg, Hl, ↓reduceIte, Subgroup.mem_top, true_iff]
      exact tab_mem_allTabs σ
    · simp only [Hg, Hl, ↓reduceIte] at ht ⊢
      obtain ⟨σ, rfl⟩ := exists_tab_eq (isTab_of_mem_allTabs ht)
      exact ⟨σ, Subgroup.mem_top _, rfl⟩

@[expose] noncomputable def Tgrp (n : ℕ) (b : Bool) : Subgroup (Gp n) := subOf n (Tgl n b)

theorem mem_Tgrp (b : Bool) (hT : subOK n (Tgl n b) = true) {σ : Gp n} :
    σ ∈ Tgrp n b ↔ tab σ ∈ Tgl n b := mem_subOf hT

theorem Tgl_spec (b : Bool) (hT : subOK n (Tgl n b) = true) :
    ∀ t ∈ Tgl n b, ∃ σ ∈ Tgrp n b, tab σ = t := by
  intro t ht
  obtain ⟨σ, rfl⟩ := exists_tab_eq ((subOK_spec hT).1 t ht)
  exact ⟨σ, (mem_Tgrp b hT).2 ht, rfl⟩

@[expose] noncomputable def flagCV (n : ℕ) (k : Mod) (b : Bool) : Subgroup (Mod.V n k) :=
  fixV ((Hg n b).map (Mod.act n k))

@[expose] noncomputable def flagF1V (n : ℕ) (k : Mod) (b : Bool) : Subgroup (Mod.V n k) :=
  Fm (Tgrp n b) (flagCV n k b)

@[expose] noncomputable def flagF2V (n : ℕ) (k : Mod) (b : Bool) : Subgroup (Mod.V n k) :=
  Fm (Tgrp n b) (flagF1V n k b)

theorem mask_Fm (b : Bool) (hT : subOK n (Tgl n b) = true) {S : Subgroup (Mod.V n k)}
    {p : ℕ → Bool} (hp : ∀ m, inWk n k m = true → (toV n k m ∈ S ↔ p m = true))
    {m : ℕ} (hm : inWk n k m = true) :
    toV n k m ∈ Fm (Tgrp n b) S ↔ fmask n (Tgl n b) p m = true := by
  unfold fmask
  simp only [List.all_eq_true]
  rw [mem_Fm]
  constructor
  · intro h t ht
    obtain ⟨σ, hσ, rfl⟩ := Tgl_spec b hT t ht
    have h1 := h σ hσ
    rw [toV_ratio σ hm] at h1
    exact (hp _ (inWk_xor (inWk_actM σ hm) hm)).1 h1
  · intro h σ hσ
    rw [toV_ratio σ hm]
    exact (hp _ (inWk_xor (inWk_actM σ hm) hm)).2 (h _ ((mem_Tgrp b hT).1 hσ))

theorem mask_C (b : Bool) {m : ℕ} (hm : inWk n k m = true) :
    toV n k m ∈ flagCV n k b ↔ flagC n k b m = true := by
  unfold flagCV flagC
  unfold cmask
  simp only [List.all_eq_true]
  rw [mem_fixV]
  constructor
  · intro h t ht
    obtain ⟨σ, hσ, rfl⟩ := (Hl_spec b).2 t ht
    have h1 := h (Mod.act n k σ) (Subgroup.mem_map_of_mem _ hσ)
    have h2 : toV n k (actM n (tab σ) m ^^^ m) = 1 := by
      rw [← toV_ratio σ hm, h1, mul_inv_cancel]
    exact (toV_eq_one_iff (inWk_xor (inWk_actM σ hm) hm)).1 h2
  · intro h x hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 := h (tab σ) (((Hl_spec b).1 σ).1 hσ)
    have h2 : toV n k (actM n (tab σ) m ^^^ m) = 1 :=
      (toV_eq_one_iff (inWk_xor (inWk_actM σ hm) hm)).2 h1
    rw [← toV_ratio σ hm] at h2
    exact mul_inv_eq_one.1 h2

theorem mask_F1 (b : Bool) (hT : subOK n (Tgl n b) = true) {m : ℕ} (hm : inWk n k m = true) :
    toV n k m ∈ flagF1V n k b ↔ flagF1 n k b m = true := by
  unfold flagF1V flagF1
  exact mask_Fm b hT (fun m' hm' => mask_C b hm') hm

theorem mask_F2 (b : Bool) (hT : subOK n (Tgl n b) = true) {m : ℕ} (hm : inWk n k m = true) :
    toV n k m ∈ flagF2V n k b ↔ flagF2 n k b m = true := by
  unfold flagF2V flagF2
  exact mask_Fm b hT (fun m' hm' => mask_F1 b hT hm') hm

theorem card_flag (b : Bool) (hT : subOK n (Tgl n b) = true) (h : flagOK n k b = true) :
    Nat.card (flagF1V n k b) = 2 * Nat.card (flagCV n k b) ∧
      Nat.card (flagF2V n k b) = 2 * Nat.card (flagF1V n k b) := by
  simp only [flagOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨sC, sF1, sF2⟩ := flagTabs_spec n k b
  rw [sF1, sC, cntT_tabOf, cntT_tabOf] at h1
  rw [sF2, sF1, cntT_tabOf, cntT_tabOf] at h2
  have e0 := card_S_cnt k (flagCV n k b) (flagC n k b) (fun m hm => mask_C b hm)
  have e1 := card_S_cnt k (flagF1V n k b) (flagF1 n k b) (fun m hm => mask_F1 b hT hm)
  have e2 := card_S_cnt k (flagF2V n k b) (flagF2 n k b) (fun m hm => mask_F2 b hT hm)
  have hc : 0 < cN n k := cN_pos k
  have e0' : Nat.card (flagCV n k b) * cN n k = cntS n k (flagC n k b) := e0
  have e1' : Nat.card (flagF1V n k b) * cN n k = cntS n k (flagF1 n k b) := e1
  have e2' : Nat.card (flagF2V n k b) * cN n k = cntS n k (flagF2 n k b) := e2
  refine ⟨?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_right hc
    calc Nat.card (flagF1V n k b) * cN n k = cntS n k (flagF1 n k b) := e1'
      _ = 2 * cntS n k (flagC n k b) := h1
      _ = 2 * (Nat.card (flagCV n k b) * cN n k) := by rw [e0']
      _ = 2 * Nat.card (flagCV n k b) * cN n k := by ring
  · apply Nat.eq_of_mul_eq_mul_right hc
    calc Nat.card (flagF2V n k b) * cN n k = cntS n k (flagF2 n k b) := e2'
      _ = 2 * cntS n k (flagF1 n k b) := h2
      _ = 2 * (Nat.card (flagF1V n k b) * cN n k) := by rw [e1']
      _ = 2 * Nat.card (flagF1V n k b) * cN n k := by ring

@[expose] noncomputable def stabW (H : Subgroup (Gp n)) (W : Subgroup (Mod.V n k)) :
    Subgroup (Gp n) where
  carrier := {h | h ∈ H ∧ ∀ w, w ∈ W ↔ Mod.act n k h w ∈ W}
  one_mem' := ⟨H.one_mem, fun w => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun w => by
    rw [map_mul, MulAut.mul_apply]
    exact (hb.2 w).trans (ha.2 _)⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun w => by
    have h1 := ha.2 (Mod.act n k a⁻¹ w)
    have h2 : Mod.act n k a (Mod.act n k a⁻¹ w) = w := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [h2] at h1
    exact h1.symm⟩

theorem mem_stabW_iff (b : Bool) {F : Subgroup (Mod.V n k)} {p : ℕ → Bool}
    (hp : ∀ m, inWk n k m = true → (toV n k m ∈ F ↔ p m = true)) {σ : Gp n} :
    σ ∈ stabW (Hg n b) F ↔ tab σ ∈ stabTab n k (Hl n b) p := by
  unfold stabTab
  rw [List.mem_filter]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨((Hl_spec b).1 σ).1 hσ, fun m hm => ?_⟩
    by_cases hw : inWk n k m = true
    · right
      have h1 := h (toV n k m)
      rw [act_toV σ hw, hp m hw, hp _ (inWk_actM σ hw)] at h1
      exact Bool.eq_iff_iff.2 h1
    · left
      simpa using hw
  · rintro ⟨hσ, h⟩
    refine ⟨((Hl_spec b).1 σ).2 hσ, fun w => ?_⟩
    obtain ⟨m, hm2, hw, rfl⟩ := toV_surj k w
    rw [act_toV σ hw, hp m hw, hp _ (inWk_actM σ hw)]
    rcases h m hm2 with h1 | h1
    · exact absurd hw (by simpa using h1)
    · rw [h1]

theorem stabW_eq_subOf (b : Bool) {F : Subgroup (Mod.V n k)} {p : ℕ → Bool}
    (hp : ∀ m, inWk n k m = true → (toV n k m ∈ F ↔ p m = true))
    (hS : subOK n (stabTab n k (Hl n b) p) = true) :
    stabW (Hg n b) F = subOf n (stabTab n k (Hl n b) p) := by
  ext σ
  rw [mem_stabW_iff b hp, mem_subOf hS]

theorem sylow_of_cards {G : Type*} [Group G] [Finite G] {T X : Subgroup G} (hTX : T ≤ X)
    {e m : ℕ} (hT : Nat.card T = 2 ^ e) (hX : Nat.card X = 2 ^ e * m) (hm : m % 2 = 1) :
    IsPGroup 2 T ∧ ¬ 2 ∣ (T.subgroupOf X).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨IsPGroup.of_card hT, ?_⟩
  have h1 := Subgroup.card_mul_index (T.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hT, hX] at h1
  have h2 : (T.subgroupOf X).index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h2]
  omega

theorem sylow_tabs {X T : List Tab} (hX : subOK n X = true) (hT : subOK n T = true)
    (hTX : subsetT T X = true) {e m : ℕ} (hc : T.length = 2 ^ e) (hXc : X.length = 2 ^ e * m)
    (hm : m % 2 = 1) :
    subOf n T ≤ subOf n X ∧ IsPGroup 2 (subOf n T) ∧
      ¬ 2 ∣ ((subOf n T).subgroupOf (subOf n X)).index := by
  have hle : subOf n T ≤ subOf n X := by
    intro x hx
    rw [mem_subOf hT] at hx
    rw [mem_subOf hX]
    simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hTX
    exact hTX _ hx
  refine ⟨hle, sylow_of_cards (e := e) hle ?_ ?_ hm⟩
  · rw [card_subOf hT, hc]
  · rw [card_subOf hX, hXc]

theorem O2s_subOf {X T : List Tab} (hX : subOK n X = true) (hT : subOK n T = true)
    (hTX : subsetT T X = true) {e m : ℕ} (hc : T.length = 2 ^ e) (hXc : X.length = 2 ^ e * m)
    (hm : m % 2 = 1) (hR : subOK n (rTab X T) = true) :
    O2s (subOf n X) = subOf n (rTab X T) := by
  obtain ⟨hle, hp, hidx⟩ := sylow_tabs hX hT hTX hc hXc hm
  refine O2s_eq _ _ _ hle hp hidx (fun r => ?_)
  rw [mem_subOf hR, mem_subOf hX]
  simp only [rTab, List.mem_filter, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨hrT, hall⟩
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hTX
      exact hTX _ hrT
    · rw [mem_subOf hX] at hx
      rw [mem_subOf hT, tab_mul, tab_mul, tab_inv]
      exact hall _ hx
  · rintro ⟨hrX, hall⟩
    refine ⟨?_, fun x hx => ?_⟩
    · have h1 := hall 1 (Subgroup.one_mem _)
      rw [inv_one, one_mul, mul_one, mem_subOf hT] at h1
      exact h1
    · obtain ⟨σ, rfl⟩ := exists_tab_eq ((subOK_spec hX).1 x hx)
      have h1 := hall σ ((mem_subOf hX).2 hx)
      rw [mem_subOf hT, tab_mul, tab_mul, tab_inv] at h1
      exact h1

end CFSG.Quasithin.B3
