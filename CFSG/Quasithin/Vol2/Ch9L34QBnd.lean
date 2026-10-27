module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

section Coords

variable {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)

@[expose] def ActsBy (s : MulAut V) (cs : List ℕ) : Prop :=
  ∀ m < 2 ^ n, s (c.vm m) = c.vm (actM cs m)

@[expose] def AllLt (n : ℕ) (l : List ℕ) : Bool := l.all (· < 2 ^ n)

theorem allLt_spec {l : List ℕ} (h : AllLt n l = true) : ∀ x ∈ l, x < 2 ^ n := by
  intro x hx
  have := List.all_eq_true.1 h x hx
  simpa using this

theorem mul_self_of_coords (c : MaskCoords V n) (v : V) : v * v = 1 := by
  obtain ⟨m, -, rfl⟩ := c.vm_surj v
  rw [← c.vm_xor, Nat.xor_self, c.vm_zero]

theorem finite_of_coords (c : MaskCoords V n) : Finite V := by
  refine Finite.of_surjective (fun m : Fin (2 ^ n) => c.vm m) fun v => ?_
  obtain ⟨m, hm, hmv⟩ := c.vm_surj v
  exact ⟨⟨m, hm⟩, hmv⟩

theorem card_of_coords (c : MaskCoords V n) : Nat.card V = 2 ^ n := by
  have h := c.card_eq ⊤ (fun _ => true) (fun m _ => by simp)
  rw [Subgroup.card_top, List.filter_true, List.length_range] at h
  exact h

variable {c}

theorem actsBy_unique {s t : MulAut V} {cs : List ℕ} (hs : ActsBy c s cs) (ht : ActsBy c t cs) :
    s = t := by
  ext v
  obtain ⟨m, hm, rfl⟩ := c.vm_surj v
  rw [hs m hm, ht m hm]

@[expose] def comp (cs ds : List ℕ) : List ℕ := ds.map (actM cs)

theorem actsBy_mul {s t : MulAut V} {cs ds : List ℕ} (hs : ActsBy c s cs) (ht : ActsBy c t ds)
    (hds : AllLt n ds = true) : ActsBy c (s * t) (comp cs ds) := by
  intro m hm
  rw [MulAut.mul_apply, ht m hm, hs _ (actM_lt (allLt_spec hds) m), comp,
    actM_map (actM_xor cs)]

@[expose] def commHom (t : MulAut V) : V →* V where
  toFun v := t v * v
  map_one' := by rw [map_one, mul_one]
  map_mul' v w := by
    rw [map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem commHom_apply (t : MulAut V) (v : V) : commHom t v = t v * v := rfl

theorem two_pow_mul_card_le {t : MulAut V} {cs ws : List ℕ} (ht : ActsBy c t cs)
    (hcs : AllLt n cs = true) (hws : AllLt n ws = true)
    (hnd : (combos (ws.map fun w => actM cs w ^^^ w)).Nodup) {F : Subgroup V}
    (hF : ∀ v ∈ F, t v = v) : 2 ^ ws.length * Nat.card F ≤ 2 ^ n := by
  have := finite_of_coords c
  have hFk : F ≤ (commHom t).ker := fun v hv => by
    rw [MonoidHom.mem_ker, commHom_apply, hF v hv, mul_self_of_coords c]
  have hlt : ∀ a ∈ ws.map (fun w => actM cs w ^^^ w), a < 2 ^ n := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact Nat.xor_lt_two_pow (actM_lt (allLt_spec hcs) w) (allLt_spec hws w hw)
  have hmem : ∀ a ∈ ws.map (fun w => actM cs w ^^^ w), c.vm a ∈ (commHom t).range := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    refine ⟨c.vm w, ?_⟩
    rw [commHom_apply, ht w (allLt_spec hws w hw), c.vm_xor]
  have h1 := c.pow_le_card (commHom t).range _ hnd hlt hmem
  rw [List.length_map] at h1
  have h2 : Nat.card (commHom t).ker * Nat.card (commHom t).range = 2 ^ n := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_of_coords c]
  have h3 : Nat.card F ≤ Nat.card (commHom t).ker := Subgroup.card_le_of_le hFk
  calc 2 ^ ws.length * Nat.card F ≤ Nat.card (commHom t).range * Nat.card (commHom t).ker :=
        Nat.mul_le_mul h1 h3
    _ = 2 ^ n := by rw [mul_comm, h2]

@[expose] def nonQuad (n : ℕ) (cs ds : List ℕ) : Bool :=
  (List.range n).any fun i => actM cs (actM ds (2 ^ i) ^^^ 2 ^ i) != (actM ds (2 ^ i) ^^^ 2 ^ i)

theorem false_of_nonQuad {s t : MulAut V} {cs ds : List ℕ} (hs : ActsBy c s cs)
    (ht : ActsBy c t ds) (hcs : AllLt n cs = true) (hds : AllLt n ds = true)
    (hq : ∀ v, s (t v * v) = t v * v) (h : nonQuad n cs ds = true) : False := by
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hi' : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hi
  have hw : actM ds (2 ^ i) ^^^ 2 ^ i < 2 ^ n :=
    Nat.xor_lt_two_pow (actM_lt (allLt_spec hds) _) hi'
  have h1 := hq (c.vm (2 ^ i))
  rw [ht _ hi', ← c.vm_xor, hs _ hw] at h1
  have h2 := c.vm_inj _ _ (actM_lt (allLt_spec hcs) _) hw h1
  simp [h2] at hne

@[expose] def rankOK (r n : ℕ) (cs ws : List ℕ) : Bool :=
  decide (r ≤ ws.length) && AllLt n ws && decide (combos (ws.map fun w => actM cs w ^^^ w)).Nodup

theorem rankOK_spec {r n : ℕ} {cs ws : List ℕ} (h : rankOK r n cs ws = true) :
    r ≤ ws.length ∧ AllLt n ws = true ∧ (combos (ws.map fun w => actM cs w ^^^ w)).Nodup := by
  simp only [rankOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] def chk1 (n : ℕ) (dat : List (List ℕ × List ℕ)) : Bool :=
  dat.all (fun d => AllLt n d.1 && rankOK 3 n d.1 d.2) &&
    dat.all fun d => dat.all fun d' => d.1 == d'.1 || nonQuad n d.1 d'.1

@[expose] def chk2 (n : ℕ) (dat : List (List ℕ × List ℕ)) : Bool :=
  dat.all (fun d => AllLt n d.1 && rankOK 6 n d.1 d.2) &&
    dat.all fun d => dat.all fun d' => d.1 == d'.1 || nonQuad n d.1 d'.1 ||
      dat.all fun d'' => d''.1 == d.1 || d''.1 == d'.1 || d''.1 == comp d.1 d'.1 ||
        nonQuad n d.1 d''.1 || nonQuad n d'.1 d''.1

theorem chk1_spec {n : ℕ} {dat : List (List ℕ × List ℕ)} (h : chk1 n dat = true) :
    (∀ d ∈ dat, AllLt n d.1 = true ∧ rankOK 3 n d.1 d.2 = true) ∧
      ∀ d ∈ dat, ∀ d' ∈ dat, d.1 = d'.1 ∨ nonQuad n d.1 d'.1 = true := by
  simp only [chk1, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

theorem chk2_spec {n : ℕ} {dat : List (List ℕ × List ℕ)} (h : chk2 n dat = true) :
    (∀ d ∈ dat, AllLt n d.1 = true ∧ rankOK 6 n d.1 d.2 = true) ∧
      ∀ d ∈ dat, ∀ d' ∈ dat, d.1 = d'.1 ∨ nonQuad n d.1 d'.1 = true ∨
        ∀ d'' ∈ dat, d''.1 = d.1 ∨ d''.1 = d'.1 ∨ d''.1 = comp d.1 d'.1 ∨
          nonQuad n d.1 d''.1 = true ∨ nonQuad n d'.1 d''.1 = true := by
  simp only [chk2, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun d hd d' hd' => ?_⟩
  rcases h.2 d hd d' hd' with ((h1 | h1) | h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr fun d'' hd'' => ?_)
    rcases h1 d'' hd'' with ((((h2 | h2) | h2) | h2) | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))

theorem card_le_of_subset {G : Type*} [Group G] (B : Subgroup G) (s : Finset G)
    (h : ∀ x ∈ B, x ∈ s) : Nat.card B ≤ s.card := by
  classical
  have : (B : Set G) ⊆ (s : Set G) := fun x hx => h x hx
  calc Nat.card B = (B : Set G).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ (s : Set G).ncard := Set.ncard_le_ncard this (Finset.finite_toSet s)
    _ = s.card := Set.ncard_coe_finset s

theorem cube_bound_one {S B : Subgroup (MulAut V)} (hBS : B ≤ S) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v)
    (dat : List (List ℕ × List ℕ))
    (hcov : ∀ s ∈ S, s * s = 1 → s ≠ 1 → ∃ d ∈ dat, ActsBy c s d.1)
    (hchk : chk1 n dat = true) : Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ n := by
  classical
  obtain ⟨hdat, hpair⟩ := chk1_spec hchk
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨d, hd, htd⟩ := hcov t (hBS htB) (hsq t htB) ht1'
  have hsub : ∀ s ∈ B, s ∈ ({1, (t : MulAut V)} : Finset (MulAut V)) := by
    intro s hs
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    push Not at hc
    obtain ⟨d', hd', hsd'⟩ := hcov s (hBS hs) (hsq s hs) hc.1
    rcases hpair d' hd' d hd with he | hn
    · exact hc.2 (actsBy_unique hsd' (he ▸ htd))
    · exact false_of_nonQuad hsd' htd (hdat d' hd').1 (hdat d hd).1 (hq s hs t htB) hn
  have hB : Nat.card B ≤ 2 := (card_le_of_subset B _ hsub).trans (Finset.card_le_two)
  obtain ⟨hr, hws, hnd⟩ := rankOK_spec (hdat d hd).2
  have hfix := two_pow_mul_card_le htd (hdat d hd).1 hws hnd (F := fixV B)
    (fun v hv => hv t htB)
  have h8 : 2 ^ 3 * Nat.card (fixV B) ≤ 2 ^ n :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hr)).trans hfix
  calc Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ 3 * Nat.card (fixV B) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 3)
    _ ≤ 2 ^ n := h8

theorem cube_bound_two {S B : Subgroup (MulAut V)} (hBS : B ≤ S) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v)
    (dat : List (List ℕ × List ℕ))
    (hcov : ∀ s ∈ S, s * s = 1 → s ≠ 1 → ∃ d ∈ dat, ActsBy c s d.1)
    (hchk : chk2 n dat = true) : Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ n := by
  classical
  obtain ⟨hdat, htri⟩ := chk2_spec hchk
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨d, hd, htd⟩ := hcov t (hBS htB) (hsq t htB) ht1'
  obtain ⟨hr, hws, hnd⟩ := rankOK_spec (hdat d hd).2
  have hfix := two_pow_mul_card_le htd (hdat d hd).1 hws hnd (F := fixV B)
    (fun v hv => hv t htB)
  have h64 : 2 ^ 6 * Nat.card (fixV B) ≤ 2 ^ n :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hr)).trans hfix
  suffices hB : Nat.card B ≤ 4 by
    calc Nat.card B ^ 3 * Nat.card (fixV B) ≤ 4 ^ 3 * Nat.card (fixV B) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 3)
      _ = 2 ^ 6 * Nat.card (fixV B) := by norm_num
      _ ≤ 2 ^ n := h64
  by_cases hall : ∀ s ∈ B, s = 1 ∨ s = (t : MulAut V)
  · have hsub : ∀ s ∈ B, s ∈ ({1, (t : MulAut V)} : Finset (MulAut V)) := by
      intro s hs
      rcases hall s hs with h | h <;> simp [h]
    exact (card_le_of_subset B _ hsub).trans (Finset.card_le_two.trans (by norm_num))
  push Not at hall
  obtain ⟨s, hsB, hs1, hst⟩ := hall
  obtain ⟨d', hd', hsd'⟩ := hcov s (hBS hsB) (hsq s hsB) hs1
  have hdd' : d'.1 ≠ d.1 := fun he => hst (actsBy_unique hsd' (he ▸ htd))
  have hsub : ∀ u ∈ B, u ∈ ({1, s, (t : MulAut V), s * t} : Finset (MulAut V)) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc
    push Not at hc
    obtain ⟨hu1, hus, hut, hust⟩ := hc
    obtain ⟨d'', hd'', hud''⟩ := hcov u (hBS hu) (hsq u hu) hu1
    rcases htri d' hd' d hd with he | hn | h3
    · exact hdd' he
    · exact false_of_nonQuad hsd' htd (hdat d' hd').1 (hdat d hd).1 (hq s hsB t htB) hn
    · rcases h3 d'' hd'' with h | h | h | h | h
      · exact hus (actsBy_unique hud'' (h ▸ hsd'))
      · exact hut (actsBy_unique hud'' (h ▸ htd))
      · exact hust (actsBy_unique hud'' (h ▸ actsBy_mul hsd' htd (hdat d hd).1))
      · exact false_of_nonQuad hsd' hud'' (hdat d' hd').1 (hdat d'' hd'').1 (hq s hsB u hu) h
      · exact false_of_nonQuad htd hud'' (hdat d hd).1 (hdat d'' hd'').1 (hq t htB u hu) h
  exact (card_le_of_subset B _ hsub).trans Finset.card_le_four

end Coords

end CFSG.Quasithin.H13.Ch9.L34M
