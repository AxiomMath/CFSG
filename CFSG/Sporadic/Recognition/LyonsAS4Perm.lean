module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def x1p : Perm (Fin 11) := swap 0 2 * swap 0 1

@[expose] def x2p : Perm (Fin 11) := swap 3 5 * swap 3 4

@[expose] def x3p : Perm (Fin 11) := swap 6 8 * swap 6 7

@[expose] def y12p : Perm (Fin 11) := x1p * x2p

@[expose] def u123p : Perm (Fin 11) := x1p * x2p * x3p

@[expose] def CA (σ : Perm (Fin 11)) : Subgroup (Perm (Fin 11)) :=
  centralizer ({σ} : Set (Perm (Fin 11))) ⊓ alternatingGroup (Fin 11)

theorem cycleType_x1p : x1p.cycleType = {3} :=
  (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem cycleType_x2p : x2p.cycleType = {3} :=
  (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem cycleType_x3p : x3p.cycleType = {3} :=
  (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem disjoint_x1p_x2p : Disjoint x1p x2p := by
  show ∀ x : Fin 11, x1p x = x ∨ x2p x = x
  decide

theorem disjoint_y12p_x3p : Disjoint y12p x3p := by
  show ∀ x : Fin 11, y12p x = x ∨ x3p x = x
  decide

theorem cycleType_y12p : y12p.cycleType = {3, 3} := by
  rw [y12p, disjoint_x1p_x2p.cycleType_mul, cycleType_x1p, cycleType_x2p]
  rfl

theorem cycleType_u123p : u123p.cycleType = {3, 3, 3} := by
  rw [u123p, show x1p * x2p * x3p = y12p * x3p from rfl, disjoint_y12p_x3p.cycleType_mul,
    cycleType_y12p, cycleType_x3p]
  rfl

theorem x1p_pow_three : x1p ^ 3 = 1 := by decide
theorem x2p_pow_three : x2p ^ 3 = 1 := by decide
theorem x3p_pow_three : x3p ^ 3 = 1 := by decide
theorem y12p_pow_three : y12p ^ 3 = 1 := by decide
theorem u123p_pow_three : u123p ^ 3 = 1 := by decide

theorem x1p_pow_apply_zero {k : ℕ} (h : (x1p ^ k) 0 = 0) : x1p ^ k = 1 := by
  have hk : x1p ^ k = x1p ^ (k % 3) := by
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, x1p_pow_three, one_pow, mul_one]
  rw [hk] at h ⊢
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize k % 3 = r at h hlt ⊢
  interval_cases r
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem two_mul_card_CA {σ τ : Perm (Fin 11)} (hτ : τ * σ = σ * τ) (hodd : sign τ = -1) :
    2 * Nat.card ↥(CA σ) = Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 11)))) := by
  have h : (alternatingGroup (Fin 11)).relIndex
      (centralizer ({σ} : Set (Perm (Fin 11)))) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨τ, mem_centralizer_singleton_iff.2 hτ, fun b _ => ?_⟩
    rcases Int.units_eq_one_or (sign b) with hb | hb <;>
      simp [Xor, mem_alternatingGroup, sign_mul, hb, hodd]
  rw [← relIndex_mul_card (H := alternatingGroup (Fin 11))
    (K := centralizer ({σ} : Set (Perm (Fin 11)))), h, CA, inf_comm]

theorem card_CA_x1p : Nat.card ↥(CA x1p) = 60480 := by
  have h := two_mul_card_CA (σ := x1p) (τ := swap 3 4) (by decide) (sign_swap (by decide))
  have hc : Nat.card ↥(centralizer ({x1p} : Set (Perm (Fin 11)))) = 120960 := by
    rw [nat_card_centralizer, cycleType_x1p]; decide
  omega

theorem card_CA_y12p : Nat.card ↥(CA y12p) = 1080 := by
  have h := two_mul_card_CA (σ := y12p) (τ := swap 6 7) (by decide) (sign_swap (by decide))
  have hc : Nat.card ↥(centralizer ({y12p} : Set (Perm (Fin 11)))) = 2160 := by
    rw [nat_card_centralizer, cycleType_y12p]; decide
  omega

theorem card_CA_u123p : Nat.card ↥(CA u123p) = 162 := by
  have h := two_mul_card_CA (σ := u123p) (τ := swap 9 10) (by decide) (sign_swap (by decide))
  have hc : Nat.card ↥(centralizer ({u123p} : Set (Perm (Fin 11)))) = 324 := by
    rw [nat_card_centralizer, cycleType_u123p]; decide
  omega

theorem cycleType_of_pow_three {σ : Perm (Fin 11)} (h : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} ∨ σ.cycleType = {3, 3, 3} := by
  have hmem : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h3 : n ∣ 3 := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h)
    have h2 := two_le_of_mem_cycleType hn
    exact ((Nat.dvd_prime Nat.prime_three).1 h3).resolve_left (by omega)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate_card.2 hmem
  have hsum : σ.cycleType.sum = 3 * Multiset.card σ.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : σ.cycleType.sum ≤ 11 := by simpa using sum_cycleType_le σ
  have hpos : 0 < Multiset.card σ.cycleType := card_cycleType_pos.2 h1
  obtain ⟨c, hc⟩ : ∃ c, Multiset.card σ.cycleType = c := ⟨_, rfl⟩
  rw [hc] at hrep hsum hpos
  have hc3 : c ≤ 3 := by omega
  interval_cases c
  · exact Or.inl (hrep.trans rfl)
  · exact Or.inr (Or.inl (hrep.trans rfl))
  · exact Or.inr (Or.inr (hrep.trans rfl))

theorem card_support_le_nine_of_pow_three {σ : Perm (Fin 11)} (h : σ ^ 3 = 1) :
    σ.support.card ≤ 9 := by
  by_cases h1 : σ = 1
  · simp [h1]
  · rw [← sum_cycleType]
    rcases cycleType_of_pow_three h h1 with h2 | h2 | h2 <;> rw [h2] <;> decide

theorem exists_even_conj_of_cycleType_eq {σ τ : Perm (Fin 11)} (hσ : σ ^ 3 = 1)
    (h : σ.cycleType = τ.cycleType) : ∃ g : Perm (Fin 11), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 h)
  rcases Int.units_eq_one_or (sign π) with h1 | h1
  · exact ⟨π, h1, hπ⟩
  · have h2 : 2 ≤ σ.supportᶜ.card := by
      have := card_support_le_nine_of_pow_three hσ
      rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    obtain ⟨a, ha, b, hb, ab⟩ := Finset.one_lt_card.1 h2
    refine ⟨π * swap a b, ?_, ?_⟩
    · rw [map_mul, h1, sign_swap ab]
      rfl
    · have hd : Disjoint (swap a b) σ := by
        rw [disjoint_iff_disjoint_support, support_swap ab, Finset.disjoint_insert_left,
          Finset.disjoint_singleton_left]
        exact ⟨Finset.mem_compl.1 ha, Finset.mem_compl.1 hb⟩
      rw [← hπ]
      simp [mul_assoc, hd.commute.eq]

theorem x1p_apply_of_ne {x : Fin 11} (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) : x1p x = x := by
  revert x
  decide

theorem commute_x1p_of_fix {σ : Perm (Fin 11)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 2) :
    σ * x1p = x1p * σ := by
  have hd : Disjoint σ x1p := by
    intro x
    by_cases hx : x = 0 ∨ x = 1 ∨ x = 2
    · left
      rcases hx with rfl | rfl | rfl <;> assumption
    · right
      push Not at hx
      exact x1p_apply_of_ne hx.1 hx.2.1 hx.2.2
  exact hd.commute

theorem exists_pow_fix_of_commute {σ : Perm (Fin 11)} (h : σ * x1p = x1p * σ) :
    ∃ k : ℕ, ((x1p ^ k)⁻¹ * σ) 0 = 0 ∧ ((x1p ^ k)⁻¹ * σ) 1 = 1 ∧ ((x1p ^ k)⁻¹ * σ) 2 = 2 := by
  have hc : ∀ x, σ (x1p x) = x1p (σ x) := fun x => DFunLike.congr_fun h x
  have h0 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 2 := by
    by_contra hne
    push Not at hne
    have hfix : x1p (σ 0) = σ 0 := x1p_apply_of_ne hne.1 hne.2.1 hne.2.2
    have e : σ (x1p 0) = x1p (σ 0) := hc 0
    rw [hfix, show x1p 0 = 1 from by decide] at e
    exact absurd (σ.injective e) (by decide)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (x1p ^ k) 0 = σ 0 := by
    rcases h0 with h0 | h0 | h0
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨1, by rw [pow_one, h0]; decide⟩
    · exact ⟨2, by rw [h0, pow_two]; decide⟩
  refine ⟨k, ?_⟩
  have hτc : Commute ((x1p ^ k)⁻¹ * σ) x1p :=
    (((Commute.refl x1p).pow_left k).inv_left).mul_left h
  have hτ0 : ((x1p ^ k)⁻¹ * σ) 0 = 0 := by
    rw [mul_apply, ← hk]
    simp
  have hτ : ∀ x, ((x1p ^ k)⁻¹ * σ) (x1p x) = x1p (((x1p ^ k)⁻¹ * σ) x) :=
    fun x => DFunLike.congr_fun hτc x
  have hτ1 : ((x1p ^ k)⁻¹ * σ) 1 = 1 := by
    have e := hτ 0
    rw [hτ0, show x1p 0 = 1 from by decide] at e
    exact e
  refine ⟨hτ0, hτ1, ?_⟩
  have e := hτ 1
  rw [hτ1, show x1p 1 = 2 from by decide] at e
  exact e

theorem nat_card_subgroup_of_mem_list {H : Subgroup (Perm (Fin 11))} {L : List (Perm (Fin 11))}
    (h : ∀ σ, σ ∈ H ↔ σ ∈ L) (hL : L.Nodup) : Nat.card ↥H = L.length := by
  calc Nat.card ↥H = Nat.card {σ // σ ∈ L.toFinset} :=
        Nat.card_congr (Equiv.subtypeEquivRight (by simpa using h))
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = L.length := List.toFinset_card_of_nodup hL

@[expose] def ea : Perm (Fin 11) := swap 3 4 * swap 5 6 * swap 7 8 * swap 9 10

@[expose] def eb : Perm (Fin 11) := swap 3 5 * swap 4 6 * swap 7 9 * swap 8 10

@[expose] def ec : Perm (Fin 11) := swap 3 7 * swap 4 8 * swap 5 9 * swap 6 10

@[expose] def E8List : List (Perm (Fin 11)) :=
  [1, ea, eb, ec, ea * eb, ea * ec, eb * ec, ea * eb * ec]

theorem E8List_mul : ∀ a ∈ E8List, ∀ b ∈ E8List, a * b ∈ E8List := by
  have h : E8List.all (fun a => E8List.all (fun b => decide (a * b ∈ E8List))) = true := by
    decide
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb)

theorem E8List_inv : ∀ a ∈ E8List, a⁻¹ ∈ E8List := by
  have h : E8List.all (fun a => decide (a⁻¹ ∈ E8List)) = true := by decide
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.1 h a ha)

theorem E8List_nodup : E8List.Nodup := by decide

@[expose] def E8 : Subgroup (Perm (Fin 11)) where
  carrier := {σ | σ ∈ E8List}
  mul_mem' := fun {a b} ha hb => E8List_mul a ha b hb
  one_mem' := List.mem_cons_self
  inv_mem' := fun {a} ha => E8List_inv a ha

theorem mem_E8_iff {σ : Perm (Fin 11)} : σ ∈ E8 ↔ σ ∈ E8List := Iff.rfl

theorem card_E8 : Nat.card ↥E8 = 8 :=
  (nat_card_subgroup_of_mem_list (fun _ => mem_E8_iff) E8List_nodup).trans rfl

theorem E8_sq {σ : Perm (Fin 11)} (h : σ ∈ E8) : σ ^ 2 = 1 := by
  have hall : E8List.all (fun a => decide (a ^ 2 = 1)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 hall σ h)

theorem E8_support {σ : Perm (Fin 11)} (h : σ ∈ E8) (h1 : σ ≠ 1) : σ.support.card = 8 := by
  have hall : E8List.all (fun a => decide (a ≠ 1 → a.support.card = 8)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 hall σ h) h1

theorem E8_fix {σ : Perm (Fin 11)} (h : σ ∈ E8) : σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 := by
  have hall : E8List.all (fun a => decide (a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 hall σ h)

theorem E8_even {σ : Perm (Fin 11)} (h : σ ∈ E8) : sign σ = 1 := by
  have hall : E8List.all (fun a => decide (sign a = 1)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.1 hall σ h)

theorem E8_eq_closure : E8 = closure ({ea, eb, ec} : Set (Perm (Fin 11))) := by
  have ha : ea ∈ closure ({ea, eb, ec} : Set (Perm (Fin 11))) := subset_closure (by simp)
  have hb : eb ∈ closure ({ea, eb, ec} : Set (Perm (Fin 11))) := subset_closure (by simp)
  have hc : ec ∈ closure ({ea, eb, ec} : Set (Perm (Fin 11))) := subset_closure (by simp)
  refine le_antisymm (fun σ hσ => ?_) ((closure_le _).2 ?_)
  · simp only [mem_E8_iff, E8List, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha
    · exact hb
    · exact hc
    · exact mul_mem ha hb
    · exact mul_mem ha hc
    · exact mul_mem hb hc
    · exact mul_mem (mul_mem ha hb) hc
  · intro σ hσ
    have hmem : ea ∈ E8List ∧ eb ∈ E8List ∧ ec ∈ E8List := by decide
    rcases hσ with rfl | rfl | rfl
    · exact mem_E8_iff.2 hmem.1
    · exact mem_E8_iff.2 hmem.2.1
    · exact mem_E8_iff.2 hmem.2.2

@[expose] def s0a : Perm (Fin 11) := swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7

@[expose] def s0b : Perm (Fin 11) := swap 6 7 * swap 8 9

@[expose] def s0c : Perm (Fin 11) := swap 6 8 * swap 7 9

@[expose] def S0List : List (Perm (Fin 11)) :=
  [1, s0a, s0b, s0c, s0a * s0b, s0a * s0c, s0b * s0c, s0a * s0b * s0c]

theorem S0List_mul : ∀ a ∈ S0List, ∀ b ∈ S0List, a * b ∈ S0List := by
  have h : S0List.all (fun a => S0List.all (fun b => decide (a * b ∈ S0List))) = true := by
    decide
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb)

theorem S0List_inv : ∀ a ∈ S0List, a⁻¹ ∈ S0List := by
  have h : S0List.all (fun a => decide (a⁻¹ ∈ S0List)) = true := by decide
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.1 h a ha)

theorem S0List_nodup : S0List.Nodup := by decide

@[expose] def S0 : Subgroup (Perm (Fin 11)) where
  carrier := {σ | σ ∈ S0List}
  mul_mem' := fun {a b} ha hb => S0List_mul a ha b hb
  one_mem' := List.mem_cons_self
  inv_mem' := fun {a} ha => S0List_inv a ha

theorem mem_S0_iff {σ : Perm (Fin 11)} : σ ∈ S0 ↔ σ ∈ S0List := Iff.rfl

theorem S0_le_CA : S0 ≤ CA y12p := by
  have hall : S0List.all (fun a => decide (a * y12p = y12p * a ∧ sign a = 1)) = true := by
    decide
  intro σ hσ
  have h := of_decide_eq_true (List.all_eq_true.1 hall σ hσ)
  exact ⟨mem_centralizer_singleton_iff.2 h.1, mem_alternatingGroup.2 h.2⟩

theorem card_S0 : Nat.card ↥S0 = 8 :=
  (nat_card_subgroup_of_mem_list (fun _ => mem_S0_iff) S0List_nodup).trans rfl

theorem S0_center {c : Perm (Fin 11)} (hc : c ∈ S0) (hcen : ∀ s ∈ S0, s * c = c * s) :
    c = 1 ∨ (c ^ 2 = 1 ∧ c.support.card = 4) := by
  have hall : S0List.all (fun a => decide (a = 1 ∨ (a ^ 2 = 1 ∧ a.support.card = 4)) ||
      S0List.any (fun s => decide (s * a ≠ a * s))) = true := by decide
  have h := List.all_eq_true.1 hall c hc
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨s, hs, hne⟩
  · exact h
  · exact absurd (hcen s hs) hne

theorem S0_eq_closure : S0 = closure ({s0a, s0c} : Set (Perm (Fin 11))) := by
  have ha : s0a ∈ closure ({s0a, s0c} : Set (Perm (Fin 11))) := subset_closure (by simp)
  have hc : s0c ∈ closure ({s0a, s0c} : Set (Perm (Fin 11))) := subset_closure (by simp)
  have hb : s0b ∈ closure ({s0a, s0c} : Set (Perm (Fin 11))) := by
    have : s0b = (s0a * s0c) ^ 2 := by decide
    rw [this]
    exact pow_mem (mul_mem ha hc) 2
  refine le_antisymm (fun σ hσ => ?_) ((closure_le _).2 ?_)
  · simp only [mem_S0_iff, S0List, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha
    · exact hb
    · exact hc
    · exact mul_mem ha hb
    · exact mul_mem ha hc
    · exact mul_mem hb hc
    · exact mul_mem (mul_mem ha hb) hc
  · intro σ hσ
    have hmem : s0a ∈ S0List ∧ s0c ∈ S0List := by decide
    rcases hσ with rfl | rfl
    · exact mem_S0_iff.2 hmem.1
    · exact mem_S0_iff.2 hmem.2

end CFSG.Sporadic.Recognition.LyonsSims
