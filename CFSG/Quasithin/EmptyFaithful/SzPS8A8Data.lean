module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace SzPS8

abbrev Perm8 : Type := Equiv.Perm (Fin 8)

@[expose] def t1 : Perm8 := Equiv.swap 0 1

@[expose] def t2 : Perm8 := Equiv.swap 2 3

@[expose] def t3 : Perm8 := Equiv.swap 4 5

@[expose] def t4 : Perm8 := Equiv.swap 6 7

@[expose] def t5 : Perm8 := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def t6 : Perm8 := Equiv.swap 4 6 * Equiv.swap 5 7

@[expose] def t7 : Perm8 := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

@[expose] def c8 : Perm8 := Equiv.swap 2 4 * Equiv.swap 3 5

@[expose] def x8 : Perm8 := c8 * t5 * c8

@[expose] def e1 : Perm8 := t1 * t2

@[expose] def e2 : Perm8 := t2 * t3

@[expose] def e3 : Perm8 := t3 * t4

@[expose] def tgens : List Perm8 := [t1, t5, t7]

@[expose] def Tlist : List Perm8 :=
  (List.range 2).flatMap fun a => (List.range 2).flatMap fun b => (List.range 2).flatMap fun c =>
  (List.range 2).flatMap fun d => (List.range 2).flatMap fun e => (List.range 2).flatMap fun f =>
  (List.range 2).map fun g => t1 ^ a * t2 ^ b * t3 ^ c * t4 ^ d * t5 ^ e * t6 ^ f * t7 ^ g

@[expose] def Dlist8 : List Perm8 :=
  (List.range 2).flatMap fun a => (List.range 2).flatMap fun b => (List.range 2).flatMap fun c =>
  (List.range 2).flatMap fun f => (List.range 2).flatMap fun g => (List.range 2).map fun h =>
    e1 ^ a * e2 ^ b * e3 ^ c * t5 ^ f * t6 ^ g * t7 ^ h

@[expose] def Jgens : List Perm8 := [e2, t5, t7, c8]

@[expose] def Jlist8 : List Perm8 := Dlist8.flatMap fun d => [d, d * c8, d * x8]

section Facts

theorem T_len : Tlist.length = 128 := by decide +kernel

theorem T_nodup : Tlist.Nodup := by decide +kernel

theorem D_len : Dlist8.length = 64 := by decide +kernel

theorem D_nodup : Dlist8.Nodup := by decide +kernel

theorem J_len : Jlist8.length = 192 := by decide +kernel

theorem J_nodup : Jlist8.Nodup := by decide +kernel

theorem D_alt : (Dlist8.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem D_inT : (Dlist8.all fun a => decide (a ∈ Tlist)) = true := by decide +kernel

theorem T_even_inD :
    (Tlist.all fun a => !decide (Equiv.Perm.sign a = 1) || decide (a ∈ Dlist8)) = true := by
  decide +kernel

theorem T_closed : (Tlist.all fun a => tgens.all fun g => decide (a * g ∈ Tlist)) = true := by
  decide +kernel

theorem T_invol : (tgens.all fun g => decide (g⁻¹ = g)) = true := by decide +kernel

theorem J_closed : (Jlist8.all fun a => Jgens.all fun g => decide (a * g ∈ Jlist8)) = true := by
  decide +kernel

theorem J_invol : (Jgens.all fun g => decide (g⁻¹ = g)) = true := by decide +kernel

theorem J_alt : (Jlist8.all fun a => decide (Equiv.Perm.sign a = 1)) = true := by decide +kernel

theorem J_conj :
    (tgens.all fun s => Jgens.all fun j => decide (s * j * s⁻¹ ∈ Jlist8)) = true := by
  decide +kernel

theorem J_inf : (Dlist8.all fun a => decide (a ∈ Jlist8)) = true := by decide +kernel

theorem one_mem_Tlist : (1 : Perm8) ∈ Tlist := by decide +kernel

theorem one_mem_Jlist : (1 : Perm8) ∈ Jlist8 := by decide +kernel

theorem w_t2 : t2 = t5 * t1 * t5⁻¹ := by decide +kernel

theorem w_t3 : t3 = t7 * t1 * t7⁻¹ := by decide +kernel

theorem w_t4 : t4 = t7 * t2 * t7⁻¹ := by decide +kernel

theorem w_t6 : t6 = t7 * t5 * t7⁻¹ := by decide +kernel

theorem w_e1 : e1 = x8 * e2 * x8⁻¹ := by decide +kernel

theorem w_e3 : e3 = (x8 * t7) * e2 * (x8 * t7)⁻¹ := by decide +kernel

theorem w_t6' : t6 = c8 * (x8 * t7) * c8⁻¹ := by decide +kernel

theorem T_closed' : ∀ a ∈ Tlist, ∀ g ∈ tgens, a * g ∈ Tlist := by
  simpa [List.all_eq_true] using T_closed

theorem T_invol' : ∀ g ∈ tgens, g⁻¹ = g := by simpa [List.all_eq_true] using T_invol

theorem J_closed' : ∀ a ∈ Jlist8, ∀ g ∈ Jgens, a * g ∈ Jlist8 := by
  simpa [List.all_eq_true] using J_closed

theorem J_invol' : ∀ g ∈ Jgens, g⁻¹ = g := by simpa [List.all_eq_true] using J_invol

theorem J_alt' : ∀ a ∈ Jlist8, Equiv.Perm.sign a = 1 := by simpa [List.all_eq_true] using J_alt

theorem D_alt' : ∀ a ∈ Dlist8, Equiv.Perm.sign a = 1 := by simpa [List.all_eq_true] using D_alt

theorem D_inT' : ∀ a ∈ Dlist8, a ∈ Tlist := by simpa [List.all_eq_true] using D_inT

theorem T_even_inD' : ∀ a ∈ Tlist, Equiv.Perm.sign a = 1 → a ∈ Dlist8 := by
  simpa [List.all_eq_true, imp_iff_not_or] using T_even_inD

theorem J_conj' : ∀ s ∈ tgens, ∀ j ∈ Jgens, s * j * s⁻¹ ∈ Jlist8 := by
  simpa [List.all_eq_true] using J_conj

theorem J_inf' : ∀ a ∈ Dlist8, a ∈ Jlist8 := by simpa [List.all_eq_true] using J_inf

theorem card_eq_length8 {G : Type*} [Group G] [Fintype G] [DecidableEq G] {H : Subgroup G}
    {l : List G} (hl : ∀ x, x ∈ H ↔ x ∈ l) (hnd : l.Nodup) : Nat.card H = l.length := by
  have e : ↥H ≃ ↥(l.toFinset) := Equiv.subtypeEquivRight fun x => by rw [hl, List.mem_toFinset]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

end Facts

section Groups

@[expose] def T8 : Subgroup Perm8 := Subgroup.closure {t1, t5, t7}

@[expose] def J8 : Subgroup Perm8 := Subgroup.closure {e2, t5, t7, c8}

theorem t1_mem : t1 ∈ T8 := Subgroup.subset_closure (by simp)

theorem t5_mem : t5 ∈ T8 := Subgroup.subset_closure (by simp)

theorem t7_mem : t7 ∈ T8 := Subgroup.subset_closure (by simp)

theorem t2_mem : t2 ∈ T8 := by
  rw [w_t2]
  exact T8.mul_mem (T8.mul_mem t5_mem t1_mem) (T8.inv_mem t5_mem)

theorem t3_mem : t3 ∈ T8 := by
  rw [w_t3]
  exact T8.mul_mem (T8.mul_mem t7_mem t1_mem) (T8.inv_mem t7_mem)

theorem t4_mem : t4 ∈ T8 := by
  rw [w_t4]
  exact T8.mul_mem (T8.mul_mem t7_mem t2_mem) (T8.inv_mem t7_mem)

theorem t6_mem : t6 ∈ T8 := by
  rw [w_t6]
  exact T8.mul_mem (T8.mul_mem t7_mem t5_mem) (T8.inv_mem t7_mem)

theorem mem_T8_iff {x : Perm8} : x ∈ T8 ↔ x ∈ Tlist := by
  constructor
  · intro hx
    have hgen : ∀ y ∈ ({t1, t5, t7} : Set Perm8), y ∈ tgens := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> simp [tgens]
    induction hx using Subgroup.closure_induction_right with
    | one => exact one_mem_Tlist
    | mul_right x hx y hy ih => exact T_closed' x ih y (hgen y hy)
    | mul_inv_cancel x hx y hy ih =>
        rw [T_invol' y (hgen y hy)]
        exact T_closed' x ih y (hgen y hy)
  · intro hx
    simp only [Tlist, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a, -, b, -, c, -, d, -, e, -, f, -, g, -, rfl⟩ := hx
    exact T8.mul_mem (T8.mul_mem (T8.mul_mem (T8.mul_mem (T8.mul_mem (T8.mul_mem
      (T8.pow_mem t1_mem a) (T8.pow_mem t2_mem b)) (T8.pow_mem t3_mem c))
      (T8.pow_mem t4_mem d)) (T8.pow_mem t5_mem e)) (T8.pow_mem t6_mem f)) (T8.pow_mem t7_mem g)

theorem mem_T8_inf_iff {x : Perm8} : x ∈ T8 ⊓ alternatingGroup (Fin 8) ↔ x ∈ Dlist8 := by
  constructor
  · rintro ⟨hx1, hx2⟩
    exact T_even_inD' x (mem_T8_iff.1 hx1) ((Equiv.Perm.mem_alternatingGroup).1 hx2)
  · intro hx
    exact ⟨mem_T8_iff.2 (D_inT' x hx), (Equiv.Perm.mem_alternatingGroup).2 (D_alt' x hx)⟩

theorem e2_mem : e2 ∈ J8 := Subgroup.subset_closure (by simp)

theorem t5_memJ : t5 ∈ J8 := Subgroup.subset_closure (by simp)

theorem t7_memJ : t7 ∈ J8 := Subgroup.subset_closure (by simp)

theorem c8_mem : c8 ∈ J8 := Subgroup.subset_closure (by simp)

theorem x8_mem : x8 ∈ J8 := J8.mul_mem (J8.mul_mem c8_mem t5_memJ) c8_mem

theorem e1_mem : e1 ∈ J8 := by
  rw [w_e1]
  exact J8.mul_mem (J8.mul_mem x8_mem e2_mem) (J8.inv_mem x8_mem)

theorem e3_mem : e3 ∈ J8 := by
  rw [w_e3]
  have h : x8 * t7 ∈ J8 := J8.mul_mem x8_mem t7_memJ
  exact J8.mul_mem (J8.mul_mem h e2_mem) (J8.inv_mem h)

theorem t6_memJ : t6 ∈ J8 := by
  rw [w_t6']
  exact J8.mul_mem (J8.mul_mem c8_mem (J8.mul_mem x8_mem t7_memJ)) (J8.inv_mem c8_mem)

theorem D_mem_J8 {d : Perm8} (hd : d ∈ Dlist8) : d ∈ J8 := by
  simp only [Dlist8, List.mem_flatMap, List.mem_map, List.mem_range] at hd
  obtain ⟨a, -, b, -, c, -, f, -, g, -, h, -, rfl⟩ := hd
  exact J8.mul_mem (J8.mul_mem (J8.mul_mem (J8.mul_mem (J8.mul_mem (J8.pow_mem e1_mem a)
    (J8.pow_mem e2_mem b)) (J8.pow_mem e3_mem c)) (J8.pow_mem t5_memJ f))
    (J8.pow_mem t6_memJ g)) (J8.pow_mem t7_memJ h)

theorem mem_J8_iff {x : Perm8} : x ∈ J8 ↔ x ∈ Jlist8 := by
  constructor
  · intro hx
    have hgen : ∀ y ∈ ({e2, t5, t7, c8} : Set Perm8), y ∈ Jgens := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp [Jgens]
    induction hx using Subgroup.closure_induction_right with
    | one => exact one_mem_Jlist
    | mul_right x hx y hy ih => exact J_closed' x ih y (hgen y hy)
    | mul_inv_cancel x hx y hy ih =>
        rw [J_invol' y (hgen y hy)]
        exact J_closed' x ih y (hgen y hy)
  · intro hx
    obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
    have hdJ : d ∈ J8 := D_mem_J8 hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hdJ
    · exact J8.mul_mem hdJ c8_mem
    · exact J8.mul_mem hdJ x8_mem

theorem J8_le_alt : J8 ≤ alternatingGroup (Fin 8) := fun x hx =>
  (Equiv.Perm.mem_alternatingGroup).2 (J_alt' x (mem_J8_iff.1 hx))

theorem card_T8 : Nat.card T8 = 128 := by
  rw [card_eq_length8 (H := T8) (l := Tlist) (fun x => mem_T8_iff) T_nodup, T_len]

theorem card_T8_inf : Nat.card ↥(T8 ⊓ alternatingGroup (Fin 8)) = 64 := by
  rw [card_eq_length8 (H := T8 ⊓ alternatingGroup (Fin 8)) (l := Dlist8)
    (fun x => mem_T8_inf_iff) D_nodup, D_len]

theorem card_J8 : Nat.card J8 = 192 := by
  rw [card_eq_length8 (H := J8) (l := Jlist8) (fun x => mem_J8_iff) J_nodup, J_len]

theorem card_perm_eight : Nat.card Perm8 = 40320 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_card_alternatingGroup (α := Fin 8)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_perm_eight] at h
  omega

theorem isSylowTwoOf_T8_top : IsSylowTwoOf T8 ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 7) (by rw [card_T8]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index T8
  rw [card_T8, card_perm_eight] at h1
  have h2 : (T8.subgroupOf ⊤).index = T8.index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  rw [h2]
  omega

theorem isSylowTwoOf_T8_inf :
    IsSylowTwoOf (T8 ⊓ alternatingGroup (Fin 8)) (alternatingGroup (Fin 8)) := by
  refine ⟨inf_le_right, IsPGroup.of_card (n := 6) (by rw [card_T8_inf]; norm_num), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (T8 ⊓ alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))
  rw [inf_eq_left.2 inf_le_right, card_T8_inf, card_alt_eight] at h1
  show ¬ 2 ∣ (T8 ⊓ alternatingGroup (Fin 8)).relIndex (alternatingGroup (Fin 8))
  omega

theorem T8_le_normalizer_J8 : T8 ≤ Subgroup.normalizer (J8 : Set Perm8) := by
  rw [T8, Subgroup.closure_le]
  intro g hg
  have hgen : g ∈ tgens := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> simp [tgens]
  have h1 : ∀ j ∈ J8, g * j * g⁻¹ ∈ J8 := by
    intro j hj
    induction hj using Subgroup.closure_induction with
    | mem y hy =>
        have hy' : y ∈ Jgens := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl | rfl <;> simp [Jgens]
        exact mem_J8_iff.2 (J_conj' g hgen y hy')
    | one => simp [J8.one_mem]
    | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact J8.mul_mem ha hb
    | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact J8.inv_mem ha
  show g ∈ Subgroup.normalizer (J8 : Set Perm8)
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨fun hj => h1 j hj, fun hj => ?_⟩
  have h2 := h1 _ hj
  have hg : g⁻¹ = g := T_invol' g hgen
  have hgg : g * g = 1 := by
    have := mul_inv_cancel g
    rwa [hg] at this
  rw [hg] at h2
  have e : g * (g * j * g) * g = j := by
    calc g * (g * j * g) * g = (g * g) * j * (g * g) := by simp only [mul_assoc]
      _ = j := by rw [hgg]; simp
  rw [e] at h2
  exact h2

theorem relIndex_T8_J8 : T8.relIndex J8 = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := T8) (K := J8)
  have h2 : T8 ⊓ J8 = T8 ⊓ alternatingGroup (Fin 8) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, J8_le_alt hx2⟩
    · intro hx
      exact ⟨hx.1, mem_J8_iff.2 (J_inf' x (mem_T8_inf_iff.1 hx))⟩
  rw [h2, card_T8_inf, card_J8] at h1
  omega

end Groups

end SzPS8

end CFSG.Quasithin
