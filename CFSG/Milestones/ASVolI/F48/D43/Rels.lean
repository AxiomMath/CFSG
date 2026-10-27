module

public import CFSG.Milestones.ASVolI.F48.D43.Stab2

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

section Model

theorem burnsideF48d_frob_rep :
    CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_toT (burnsideF48d_phi ())) burnsideF48d_frob :=
  Classical.epsilon_spec burnsideF48d_phi_rep

theorem burnsideF48d_letter_rep' : ∀ j < 17,
    CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_letters ())[2 * j]! (burnsideF48d_σ j) ∧
      CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_letters ())[2 * j + 1]! (burnsideF48d_σ j)⁻¹ :=
  fun _ hj => ⟨burnsideF48d_rep_X_iff.1 (burnsideF48d_letter_rep hj).1,
    burnsideF48d_rep_X_iff.1 (burnsideF48d_letter_rep hj).2⟩

theorem burnsideF48d_rel_parts :
    (∀ r ∈ burnsideF48d_R1 ++ burnsideF48d_R2 ++
        [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2],
      burnsideF48s_ev burnsideF48d_L r = 1) ∧
    (burnsideF48d_KW.map (burnsideF48s_ev burnsideF48d_L)).Nodup ∧
    (∀ c ∈ burnsideF48d_KW.tail, burnsideF48s_ev burnsideF48d_L (burnsideF48d_xyW ++ c) ≠
      burnsideF48s_ev burnsideF48d_L (c ++ burnsideF48d_xyW)) :=
  Certificates.certificate7803.2.2.2.2

theorem burnsideF48d_rels : ∀ r ∈ burnsideF48d_R1 ++ burnsideF48d_R2 ++
    [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2],
    burnsideF48s_ev burnsideF48d_L r = 1 :=
  burnsideF48d_rel_parts.1

theorem burnsideF48d_ev_xyW :
    burnsideF48s_ev burnsideF48d_L burnsideF48d_xyW = burnsideF48d_L 0 * burnsideF48d_L 1 := by
  rw [burnsideF48s_ev_cons, burnsideF48s_ev_cons, burnsideF48s_ev_nil, mul_one]
  rfl

theorem burnsideF48d_KW_letters : ∀ w ∈ burnsideF48d_KW, ∀ l ∈ w,
    l = ((2 : Fin 17), true) ∨ l = ((3 : Fin 17), true) := by decide

theorem burnsideF48d_KW_length : burnsideF48d_KW.length = 52 := by decide

theorem burnsideF48d_KW_cons : burnsideF48d_KW = [] :: burnsideF48d_KW.tail := by decide

theorem burnsideF48d_KW_mem_T {w : List (Fin 17 × Bool)} (hw : w ∈ burnsideF48d_KW) :
    burnsideF48s_ev burnsideF48d_L w ∈ burnsideF48d_T := by
  apply burnsideF48s_ev_mem
  intro l hl
  rcases burnsideF48d_KW_letters w hw l hl with h | h <;> subst h
  · exact burnsideF48d_L_mem_T (j := 2) (by norm_num) (by norm_num)
  · exact burnsideF48d_L_mem_T (j := 3) (by norm_num) (by norm_num)

theorem burnsideF48d_KW_cov : ∀ c ∈ burnsideF48d_T, ∃ w ∈ burnsideF48d_KW,
    burnsideF48s_ev burnsideF48d_L w = c := by
  have hlen := burnsideF48d_KW_length
  let f : Fin 52 → ↥burnsideF48d_T := fun i =>
    ⟨burnsideF48s_ev burnsideF48d_L (burnsideF48d_KW[i.val]'(by rw [hlen]; exact i.2)),
      burnsideF48d_KW_mem_T (List.getElem_mem _)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 := congrArg Subtype.val hij
    have hnd := burnsideF48d_rel_parts.2.1
    have hi : i.val < (burnsideF48d_KW.map (burnsideF48s_ev burnsideF48d_L)).length := by
      rw [List.length_map, hlen]; exact i.2
    have hj : j.val < (burnsideF48d_KW.map (burnsideF48s_ev burnsideF48d_L)).length := by
      rw [List.length_map, hlen]; exact j.2
    have := (hnd.getElem_inj_iff (hi := hi) (hj := hj)).1 (by
      rw [List.getElem_map, List.getElem_map]; exact h1)
    exact Fin.ext this
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [burnsideF48d_card_T, Nat.card_eq_fintype_card, Fintype.card_fin])
  intro c hc
  obtain ⟨i, hi⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨_, List.getElem_mem _, congrArg Subtype.val hi⟩

theorem burnsideF48d_comm_T : ∀ t ∈ burnsideF48d_T, burnsideF48d_L 0 * burnsideF48d_L 1 * t =
    t * (burnsideF48d_L 0 * burnsideF48d_L 1) → t = 1 := by
  intro t ht hc
  obtain ⟨w, hw, rfl⟩ := burnsideF48d_KW_cov t ht
  rw [burnsideF48d_KW_cons, List.mem_cons] at hw
  rcases hw with rfl | hw
  · rfl
  · exfalso
    apply burnsideF48d_rel_parts.2.2 w hw
    rw [burnsideF48s_ev_append, burnsideF48s_ev_append, burnsideF48d_ev_xyW]
    exact hc

theorem burnsideF48d_TU_rels : ∀ t ∈ ([2, 3, 4] : List (Fin 17)),
    ∀ u ∈ ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List (Fin 17)),
    ∃ r ∈ burnsideF48d_R1, r.take 3 = [(t, false), (u, true), (t, true)] ∧
      ∀ l ∈ r.drop 3, 5 ≤ l.1.val := by decide

theorem burnsideF48d_U_le : burnsideF48d_U ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
  rw [burnsideF48d_B_eq_closure, burnsideF48d_U]
  exact Subgroup.closure_mono (Set.image_mono fun j hj => by
    simp only [Set.mem_setOf_eq] at hj ⊢; omega)

theorem burnsideF48d_T_le : burnsideF48d_T ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
  rw [burnsideF48d_B_eq_closure, burnsideF48d_T]
  exact Subgroup.closure_mono (Set.image_mono fun j hj => by
    simp only [Set.mem_setOf_eq] at hj ⊢; omega)

theorem burnsideF48d_conj_letter {t u : Fin 17} (ht2 : 2 ≤ t.val) (ht4 : t.val ≤ 4)
    (hu : 5 ≤ u.val) :
    (burnsideF48d_L t)⁻¹ * burnsideF48d_L u * burnsideF48d_L t ∈ burnsideF48d_U := by
  have ht : t ∈ ([2, 3, 4] : List (Fin 17)) := by
    have : ∀ t : Fin 17, 2 ≤ t.val → t.val ≤ 4 → t ∈ ([2, 3, 4] : List (Fin 17)) := by decide
    exact this t ht2 ht4
  have hu' : u ∈ ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List (Fin 17)) := by
    have : ∀ u : Fin 17, 5 ≤ u.val →
        u ∈ ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List (Fin 17)) := by decide
    exact this u hu
  obtain ⟨r, hr, htake, hdrop⟩ := burnsideF48d_TU_rels t ht u hu'
  have hr1 : burnsideF48s_ev burnsideF48d_L r = 1 :=
    burnsideF48d_rels r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hsplit : r = [(t, false), (u, true), (t, true)] ++ r.drop 3 := by
    rw [← htake, List.take_append_drop]
  rw [hsplit, burnsideF48s_ev_append] at hr1
  have hev3 : burnsideF48s_ev burnsideF48d_L [(t, false), (u, true), (t, true)] =
      (burnsideF48d_L t)⁻¹ * burnsideF48d_L u * burnsideF48d_L t := by
    rw [burnsideF48s_ev_cons, burnsideF48s_ev_cons, burnsideF48s_ev_cons, burnsideF48s_ev_nil,
      mul_one, ← mul_assoc]
    rfl
  rw [hev3] at hr1
  have htail : burnsideF48s_ev burnsideF48d_L (r.drop 3) ∈ burnsideF48d_U :=
    burnsideF48s_ev_mem _ _ fun l hl => Subgroup.subset_closure ⟨l.1, hdrop l hl, rfl⟩
  rw [eq_inv_of_mul_eq_one_left hr1]
  exact burnsideF48d_U.inv_mem htail

theorem burnsideF48d_conj_U {t : Fin 17} (ht2 : 2 ≤ t.val) (ht4 : t.val ≤ 4) :
    ∀ z ∈ burnsideF48d_U, (burnsideF48d_L t)⁻¹ * z * burnsideF48d_L t ∈ burnsideF48d_U := by
  intro z hz
  have hz' := hz
  rw [burnsideF48d_U] at hz'
  induction hz' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact burnsideF48d_conj_letter ht2 ht4 hu
  | one => simpa using burnsideF48d_U.one_mem
  | mul x y _ _ hx hy =>
    have e : (burnsideF48d_L t)⁻¹ * (x * y) * burnsideF48d_L t =
        ((burnsideF48d_L t)⁻¹ * x * burnsideF48d_L t) *
          ((burnsideF48d_L t)⁻¹ * y * burnsideF48d_L t) := by group
    rw [e]
    exact burnsideF48d_U.mul_mem (hx (by assumption)) (hy (by assumption))
  | inv x _ hx =>
    have e : (burnsideF48d_L t)⁻¹ * x⁻¹ * burnsideF48d_L t =
        ((burnsideF48d_L t)⁻¹ * x * burnsideF48d_L t)⁻¹ := by group
    rw [e]
    exact burnsideF48d_U.inv_mem (hx (by assumption))

theorem burnsideF48d_U_normal : ∀ b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2, ∀ u ∈ burnsideF48d_U,
    b * u * b⁻¹ ∈ burnsideF48d_U := by
  intro b hb
  rw [burnsideF48d_B_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    by_cases h5 : 5 ≤ j.val
    · have hj' : burnsideF48d_L j ∈ burnsideF48d_U := Subgroup.subset_closure ⟨j, h5, rfl⟩
      intro u hu
      exact burnsideF48d_U.mul_mem (burnsideF48d_U.mul_mem hj' hu) (burnsideF48d_U.inv_mem hj')
    · have h2 : 2 ≤ j.val := hj
      have h4 : j.val ≤ 4 := by omega
      have := burnsideF48d_norm_inv (H := burnsideF48d_U) (g := (burnsideF48d_L j)⁻¹)
        (fun k hk => by rw [inv_inv]; exact burnsideF48d_conj_U h2 h4 k hk)
      intro u hu
      have h' := this u hu
      rwa [inv_inv] at h'
  | one => intro u hu; simpa using hu
  | mul x y _ _ hx hy =>
    intro u hu
    have e : x * y * u * (x * y)⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy u hu)
  | inv x _ hx =>
    intro u hu
    rw [inv_inv]
    exact burnsideF48d_norm_inv hx u hu

theorem burnsideF48d_B_le_normalizer :
    burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact fun hu => burnsideF48d_U_normal b hb u hu
  · intro h
    have := burnsideF48d_U_normal b⁻¹ (Subgroup.inv_mem _ hb) _ h
    simpa [mul_assoc] using this

@[expose] noncomputable def burnsideF48d_ol (Y : Subgroup ↥burnsideF48d_X) (p : Fin 26572) : ℕ :=
  Nat.card (MulAction.orbit ↥Y p)

theorem burnsideF48d_ol_of_mem {Y : Subgroup ↥burnsideF48d_X} {p q : Fin 26572}
    (h : ∃ y ∈ Y, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q) :
    burnsideF48d_ol Y q = burnsideF48d_ol Y p := by
  obtain ⟨y, hy, rfl⟩ := h
  unfold burnsideF48d_ol
  have : ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = (⟨y, hy⟩ : ↥Y) • p := rfl
  rw [this, MulAction.orbit_smul]

theorem burnsideF48d_ol_fix {Y : Subgroup ↥burnsideF48d_X} {p : Fin 26572}
    (h : ∀ y ∈ Y, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = p) :
    burnsideF48d_ol Y p = 1 := by
  unfold burnsideF48d_ol
  have : MulAction.orbit ↥Y p = {p} := by
    ext q
    rw [burnsideF48d_orbit_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact h y hy
    · rintro rfl
      exact ⟨1, Y.one_mem, rfl⟩
  rw [this, Nat.card_unique]

theorem burnsideF48d_ol_le {Y : Subgroup ↥burnsideF48d_X} {S : Finset (Fin 26572)}
    (hS : ∀ y ∈ Y, ∀ q ∈ S, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S)
    {p : Fin 26572} (hp : p ∈ S) : burnsideF48d_ol Y p ≤ S.card := by
  unfold burnsideF48d_ol
  have hsub : MulAction.orbit ↥Y p ⊆ (S : Set (Fin 26572)) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := (burnsideF48d_orbit_iff p q).1 hq
    exact hS y hy p hp
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)

theorem burnsideF48d_ol_norm {Y : Subgroup ↥burnsideF48d_X} {n : ↥burnsideF48d_X}
    (hn : n ∈ Subgroup.normalizer (Y : Set ↥burnsideF48d_X)) (p : Fin 26572) :
    burnsideF48d_ol Y ((n : Equiv.Perm (Fin 26572)) p) = burnsideF48d_ol Y p := by
  unfold burnsideF48d_ol
  have himg : MulAction.orbit ↥Y ((n : Equiv.Perm (Fin 26572)) p) =
      (fun q => (n : Equiv.Perm (Fin 26572)) q) '' MulAction.orbit ↥Y p := by
    ext q
    rw [burnsideF48d_orbit_iff, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨((n⁻¹ * y * n : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p,
        (burnsideF48d_orbit_iff _ _).2 ⟨n⁻¹ * y * n, ?_, rfl⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
        rwa [inv_inv] at this
      · rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
        congr 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (burnsideF48d_orbit_iff p q).1 hq
      refine ⟨n * y * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, ?_⟩
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  rw [himg, Nat.card_image_of_injective (n : Equiv.Perm (Fin 26572)).injective]

theorem burnsideF48d_B_126 {y : ↥burnsideF48d_X} (hy : y ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2)
    {p : Fin 26572} (hp : p = 1 ∨ p = 2 ∨ p = 6) :
    ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = 1 ∨
      ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = 2 ∨
      ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = 6 := by
  have h0 : ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 := (burnsideF48d_mem_P1 y).1 hy.1
  have hl := (burnsideF48d_mem_P2 y).1 hy.2 p (by
    simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hne : ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ 0 := by
    intro h
    rw [← h0] at h
    have := (y : Equiv.Perm (Fin 26572)).injective h
    rcases hp with rfl | rfl | rfl <;> exact absurd this (by decide)
  simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with h | h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem burnsideF48d_ol_U (q : Fin 26572) : q = 0 ∨ ((q = 1 ∨ q = 2 ∨ q = 6) ∧
    burnsideF48d_ol burnsideF48d_U q = 3) ∨ 81 ≤ burnsideF48d_ol burnsideF48d_U q := by
  obtain ⟨sU6, sU186, sU479, sU15916, sU26571, covU, -⟩ := burnsideF48d_orb_U
  by_cases h0 : q = 0
  · exact Or.inl h0
  right
  rcases covU q h0 with h | h | h | h | h <;>
    have hol := burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 h)
  · left
    refine ⟨?_, hol.trans sU6⟩
    obtain ⟨y, hy, hyq⟩ := (burnsideF48d_orbit_iff _ _).1 h
    rw [← hyq]
    exact burnsideF48d_B_126 (burnsideF48d_U_le hy) (Or.inr (Or.inr rfl))
  · right
    rw [hol]
    exact sU186.ge
  · right
    rw [hol]
    unfold burnsideF48d_ol
    omega
  · right
    rw [hol]
    unfold burnsideF48d_ol
    omega
  · right
    rw [hol]
    unfold burnsideF48d_ol
    omega

theorem burnsideF48d_U_fix0 : ∀ y ∈ burnsideF48d_U,
    ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 :=
  fun y hy => (burnsideF48d_mem_P1 y).1 (burnsideF48d_U_le hy).1

theorem burnsideF48d_ol_U_126 {q : Fin 26572} (hq : q = 1 ∨ q = 2 ∨ q = 6) :
    burnsideF48d_ol burnsideF48d_U q = 3 := by
  obtain ⟨sU6, -, -, -, -, -, mU1, mU2⟩ := burnsideF48d_orb_U
  rcases hq with rfl | rfl | rfl
  · rw [burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 mU1)]
    exact sU6
  · rw [burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 mU2)]
    exact sU6
  · exact sU6

theorem burnsideF48d_normalizer_le_B :
    Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X) ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
  intro n hn
  have hol0 : burnsideF48d_ol burnsideF48d_U 0 = 1 := burnsideF48d_ol_fix burnsideF48d_U_fix0
  refine ⟨(burnsideF48d_mem_P1 n).2 ?_, (burnsideF48d_mem_P2 n).2 ?_⟩
  · have h1 := burnsideF48d_ol_norm hn 0
    rw [hol0] at h1
    rcases burnsideF48d_ol_U ((n : Equiv.Perm (Fin 26572)) 0) with h | ⟨-, h⟩ | h
    · exact h
    · omega
    · omega
  · intro p hp
    have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 6 := by
      simpa only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] using hp
    have hle : burnsideF48d_ol burnsideF48d_U p ≤ 3 := by
      rcases hp' with rfl | hp'
      · rw [hol0]; norm_num
      · rw [burnsideF48d_ol_U_126 hp']
    have h1 := burnsideF48d_ol_norm hn p
    simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton]
    rcases burnsideF48d_ol_U ((n : Equiv.Perm (Fin 26572)) p) with h | ⟨h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h
    · omega

theorem burnsideF48d_B_eq' : burnsideF48d_P1 ⊓ burnsideF48d_P2 =
    ⊤ ⊓ Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X) := by
  rw [top_inf_eq]
  exact le_antisymm burnsideF48d_B_le_normalizer burnsideF48d_normalizer_le_B

theorem burnsideF48d_fix_P1 : ∀ p : Fin 26572,
    (∀ z ∈ burnsideF48d_P1, ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = p) → p = 0 := by
  intro p hp
  obtain ⟨sA6, sA479, sA26571, covP1, -⟩ := burnsideF48d_orb_P1
  have hol := burnsideF48d_ol_fix hp
  by_contra h0
  rcases covP1 p h0 with h | h | h <;>
    rw [burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 h)] at hol <;>
    unfold burnsideF48d_ol at hol <;> omega

theorem burnsideF48d_line_orbit {p : Fin 26572} (hp : p ∈ burnsideF48d_line) :
    ∃ w ∈ burnsideF48d_P2, ((w : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = p := by
  refine (burnsideF48d_orbit_iff _ _).1 ?_
  rw [burnsideF48d_orb_P2.1]
  exact hp

theorem burnsideF48d_inv_P2 : ∀ S : Finset (Fin 26572), S.Nonempty → S.card ≤ 4 →
    (∀ z ∈ burnsideF48d_P2, ∀ q ∈ S, ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) →
      S = burnsideF48d_line := by
  intro S ⟨q, hq⟩ hcard hinv
  have hle := burnsideF48d_ol_le hinv hq
  obtain ⟨-, s186, s26571, cov⟩ := burnsideF48d_orb_P2
  have hq0 : ∃ z ∈ burnsideF48d_P2, ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = q := by
    rcases cov q with h | h | h
    · exact (burnsideF48d_orbit_iff _ _).1 h
    · rw [burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 h)] at hle
      unfold burnsideF48d_ol at hle
      omega
    · rw [burnsideF48d_ol_of_mem ((burnsideF48d_orbit_iff _ _).1 h)] at hle
      unfold burnsideF48d_ol at hle
      omega
  obtain ⟨z, hz, rfl⟩ := hq0
  have hsub : burnsideF48d_line ⊆ S := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := burnsideF48d_line_orbit hp
    have e : ((w : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 =
        ((w * z⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572))
          (((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0) := by
      rw [← Equiv.Perm.mul_apply]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hinv _ (burnsideF48d_P2.mul_mem hw (burnsideF48d_P2.inv_mem hz)) _ hq
  have hl4 : burnsideF48d_line.card = 4 := by decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hl4]; exact hcard)).symm

theorem burnsideF48d_P1_ne_P2 : burnsideF48d_P1 ≠ burnsideF48d_P2 := by
  intro h
  have h1 : burnsideF48d_L 1 ∈ burnsideF48d_P2 := Subgroup.subset_closure ⟨1, by decide, rfl⟩
  rw [← h, burnsideF48d_mem_P1, burnsideF48d_xy_apt.2.2.2.2.2.2.1] at h1
  exact absurd h1 (by decide)

end Model

end CFSG.ASVolI
