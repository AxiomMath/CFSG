module

public import CFSG.Quasithin.Background.KG82CoverParab

public section

namespace CFSG.Quasithin.H.L34Cov

open CFSG.Open CFSG.LieType.BorelTits CFSG.PSL3Four CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts MulAction
open scoped Pointwise

theorem lrep_of_closed {gs A : List (List ℕ)} (h1 : List.range 42 ∈ A)
    (hcl : ∀ g ∈ gs, ∀ a ∈ A, lcomp (wordL g) a ∈ A)
    (hinv : ∀ g ∈ gs, ∀ a ∈ A, lcomp (wordL (invW g)) a ∈ A)
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ Subgroup.closure (wordSet gs)) : ∃ a ∈ A, LRep a x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨_, h1, lrep_range⟩
  | mul_left x hx y _ ih =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨a, ha, hay⟩ := ih
    exact ⟨_, hcl g hg a ha, (lrep_wordL g).comp hay⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨a, ha, hay⟩ := ih
    refine ⟨_, hinv g hg a ha, ?_⟩
    rw [← wordPerm_invW]
    exact (lrep_wordL _).comp hay

@[expose] def e1L : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41],
    [3, 4, 2, 0, 1, 15, 6, 12, 17, 9, 20, 14, 7, 18, 11, 5, 16, 8, 13, 19, 10, 32, 35, 23, 29,
      38, 26, 39, 37, 24, 33, 31, 21, 30, 40, 22, 36, 28, 25, 27, 34, 41],
    [4, 3, 2, 1, 0, 20, 6, 13, 11, 9, 15, 8, 18, 7, 17, 10, 16, 14, 12, 19, 5, 33, 39, 23, 34,
      28, 26, 35, 25, 40, 32, 31, 30, 21, 24, 27, 36, 38, 37, 22, 29, 41],
    [1, 0, 2, 4, 3, 10, 6, 18, 14, 9, 5, 17, 13, 12, 8, 20, 16, 11, 7, 19, 15, 30, 27, 23, 40,
      37, 26, 22, 38, 34, 21, 31, 33, 32, 29, 39, 36, 25, 28, 35, 24, 41],
    [0, 1, 2, 3, 4, 15, 16, 13, 14, 19, 20, 17, 18, 7, 8, 5, 6, 11, 12, 9, 10, 29, 38, 23, 32,
      35, 26, 28, 27, 21, 34, 31, 24, 40, 30, 25, 36, 39, 22, 37, 33, 41],
    [3, 4, 2, 0, 1, 5, 16, 18, 11, 19, 10, 8, 13, 12, 17, 15, 6, 14, 7, 9, 20, 24, 25, 23, 21,
      22, 26, 37, 39, 32, 40, 31, 29, 34, 33, 38, 36, 27, 35, 28, 30, 41],
    [4, 3, 2, 1, 0, 10, 16, 7, 17, 19, 5, 14, 12, 13, 11, 20, 6, 8, 18, 9, 15, 40, 37, 23, 30,
      27, 26, 25, 35, 33, 24, 31, 34, 29, 32, 28, 36, 22, 39, 38, 21, 41],
    [1, 0, 2, 4, 3, 20, 16, 12, 8, 19, 15, 11, 7, 18, 14, 10, 6, 17, 13, 9, 5, 34, 28, 23, 33,
      39, 26, 38, 22, 30, 29, 31, 40, 24, 21, 37, 36, 35, 27, 25, 32, 41],
    [0, 1, 2, 3, 4, 10, 9, 12, 11, 6, 5, 8, 7, 18, 17, 20, 19, 14, 13, 16, 15, 27, 30, 23, 37,
      40, 26, 21, 29, 28, 22, 31, 39, 35, 38, 33, 36, 24, 34, 32, 25, 41],
    [3, 4, 2, 0, 1, 20, 9, 7, 14, 6, 15, 17, 12, 13, 8, 10, 19, 11, 18, 16, 5, 39, 33, 23, 28,
      34, 26, 32, 24, 37, 35, 31, 27, 22, 25, 30, 36, 29, 40, 21, 38, 41],
    [4, 3, 2, 1, 0, 15, 9, 18, 8, 6, 20, 11, 13, 12, 14, 5, 19, 17, 7, 16, 10, 35, 32, 23, 38,
      29, 26, 33, 40, 25, 39, 31, 22, 27, 37, 21, 36, 34, 24, 30, 28, 41],
    [1, 0, 2, 4, 3, 5, 9, 13, 17, 6, 10, 14, 18, 7, 11, 15, 19, 8, 12, 16, 20, 22, 21, 23, 25,
      24, 26, 30, 34, 38, 27, 31, 35, 39, 28, 32, 36, 40, 29, 33, 37, 41],
    [0, 1, 2, 3, 4, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 28, 34, 23, 39,
      33, 26, 29, 21, 27, 38, 31, 37, 25, 22, 40, 36, 32, 30, 24, 35, 41],
    [3, 4, 2, 0, 1, 10, 19, 13, 8, 16, 5, 11, 18, 7, 14, 20, 9, 17, 12, 6, 15, 37, 40, 23, 27,
      30, 26, 24, 32, 39, 25, 31, 28, 38, 35, 34, 36, 21, 33, 29, 22, 41],
    [4, 3, 2, 1, 0, 5, 19, 12, 14, 16, 10, 17, 7, 18, 8, 15, 9, 11, 13, 6, 20, 25, 24, 23, 22,
      21, 26, 40, 33, 35, 37, 31, 38, 28, 39, 29, 36, 30, 32, 34, 27, 41],
    [1, 0, 2, 4, 3, 15, 19, 7, 11, 16, 20, 8, 12, 13, 17, 5, 9, 14, 18, 6, 10, 38, 29, 23, 35,
      32, 26, 34, 30, 22, 28, 31, 25, 37, 27, 24, 36, 33, 21, 40, 39, 41]]

@[expose] def e2L : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41],
    [9, 6, 2, 19, 16, 5, 1, 17, 13, 0, 10, 12, 11, 8, 18, 15, 4, 7, 14, 3, 20, 22, 21, 23, 25,
      24, 31, 27, 39, 35, 30, 26, 38, 34, 33, 29, 41, 37, 32, 28, 40, 36],
    [12, 18, 2, 13, 7, 5, 14, 4, 19, 11, 10, 9, 0, 3, 6, 15, 17, 16, 1, 8, 20, 25, 24, 23, 22,
      21, 41, 27, 34, 32, 30, 36, 29, 39, 28, 38, 31, 37, 35, 33, 40, 26],
    [11, 14, 2, 8, 17, 5, 18, 16, 3, 12, 10, 0, 9, 19, 1, 15, 7, 4, 6, 13, 20, 24, 25, 23, 21,
      22, 36, 27, 33, 38, 30, 41, 35, 28, 39, 32, 26, 37, 29, 34, 40, 31],
    [8, 17, 2, 11, 14, 5, 7, 6, 0, 13, 10, 3, 19, 9, 4, 15, 18, 1, 16, 12, 20, 21, 22, 23, 24,
      25, 36, 37, 34, 35, 40, 41, 38, 39, 28, 29, 26, 27, 32, 33, 30, 31],
    [13, 7, 2, 12, 18, 5, 17, 1, 9, 8, 10, 19, 3, 0, 16, 15, 14, 6, 4, 11, 20, 22, 21, 23, 25,
      24, 41, 37, 33, 29, 40, 36, 32, 28, 39, 35, 31, 27, 38, 34, 30, 26],
    [19, 16, 2, 9, 6, 5, 4, 14, 12, 3, 10, 13, 8, 11, 7, 15, 1, 18, 17, 0, 20, 25, 24, 23, 22,
      21, 31, 37, 28, 38, 40, 26, 35, 33, 34, 32, 41, 27, 29, 39, 30, 36],
    [3, 4, 2, 0, 1, 5, 16, 18, 11, 19, 10, 8, 13, 12, 17, 15, 6, 14, 7, 9, 20, 24, 25, 23, 21,
      22, 26, 37, 39, 32, 40, 31, 29, 34, 33, 38, 36, 27, 35, 28, 30, 41],
    [6, 9, 2, 16, 19, 5, 0, 8, 7, 1, 10, 18, 14, 17, 12, 15, 3, 13, 11, 4, 20, 21, 22, 23, 24,
      25, 31, 30, 33, 32, 27, 26, 29, 28, 39, 38, 41, 40, 35, 34, 37, 36],
    [1, 0, 2, 4, 3, 5, 9, 13, 17, 6, 10, 14, 18, 7, 11, 15, 19, 8, 12, 16, 20, 22, 21, 23, 25,
      24, 26, 30, 34, 38, 27, 31, 35, 39, 28, 32, 36, 40, 29, 33, 37, 41],
    [14, 11, 2, 17, 8, 5, 12, 19, 4, 18, 10, 1, 6, 16, 0, 15, 13, 3, 9, 7, 20, 25, 24, 23, 22,
      21, 36, 30, 39, 29, 27, 41, 32, 34, 33, 35, 26, 40, 38, 28, 37, 31],
    [18, 12, 2, 7, 13, 5, 11, 3, 16, 14, 10, 6, 1, 4, 9, 15, 8, 19, 0, 17, 20, 24, 25, 23, 21,
      22, 41, 30, 28, 35, 27, 36, 38, 33, 34, 29, 31, 40, 32, 39, 37, 26],
    [7, 13, 2, 18, 12, 5, 8, 0, 6, 17, 10, 16, 4, 1, 19, 15, 11, 9, 3, 14, 20, 21, 22, 23, 24,
      25, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26],
    [17, 8, 2, 14, 11, 5, 13, 9, 1, 7, 10, 4, 16, 6, 3, 15, 12, 0, 19, 18, 20, 22, 21, 23, 25,
      24, 36, 40, 28, 32, 37, 41, 29, 33, 34, 38, 26, 30, 35, 39, 27, 31],
    [4, 3, 2, 1, 0, 5, 19, 12, 14, 16, 10, 17, 7, 18, 8, 15, 9, 11, 13, 6, 20, 25, 24, 23, 22,
      21, 26, 40, 33, 35, 37, 31, 38, 28, 39, 29, 36, 30, 32, 34, 27, 41],
    [16, 19, 2, 6, 9, 5, 3, 11, 18, 4, 10, 7, 17, 14, 13, 15, 0, 12, 8, 1, 20, 24, 25, 23, 21,
      22, 31, 40, 34, 29, 37, 26, 32, 39, 28, 35, 41, 30, 38, 33, 27, 36]]

@[expose] def v1L : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41],
    [6, 9, 2, 16, 19, 5, 0, 8, 7, 1, 10, 18, 14, 17, 12, 15, 3, 13, 11, 4, 20, 21, 22, 23, 24,
      25, 31, 30, 33, 32, 27, 26, 29, 28, 39, 38, 41, 40, 35, 34, 37, 36],
    [8, 17, 2, 11, 14, 5, 7, 6, 0, 13, 10, 3, 19, 9, 4, 15, 18, 1, 16, 12, 20, 21, 22, 23, 24,
      25, 36, 37, 34, 35, 40, 41, 38, 39, 28, 29, 26, 27, 32, 33, 30, 31],
    [7, 13, 2, 18, 12, 5, 8, 0, 6, 17, 10, 16, 4, 1, 19, 15, 11, 9, 3, 14, 20, 21, 22, 23, 24,
      25, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26]]

@[expose] def eIdx : List (List ℕ) :=
  [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3], [0], [0, 3], [0, 2], [0, 2, 3], [0, 1],
    [0, 1, 3], [0, 1, 2], [0, 1, 2, 3]]

theorem e16_closed :
    (List.range 42 ∈ e1L ∧ (∀ g ∈ std₁.eW, ∀ a ∈ e1L, lcomp (wordL g) a ∈ e1L) ∧
      ∀ g ∈ std₁.eW, ∀ a ∈ e1L, lcomp (wordL (invW g)) a ∈ e1L) ∧
    (List.range 42 ∈ e2L ∧ (∀ g ∈ std₂.eW, ∀ a ∈ e2L, lcomp (wordL g) a ∈ e2L) ∧
      ∀ g ∈ std₂.eW, ∀ a ∈ e2L, lcomp (wordL (invW g)) a ∈ e2L) ∧
    (List.range 42 ∈ v1L ∧ (∀ g ∈ std₁.vW, ∀ a ∈ v1L, lcomp (wordL g) a ∈ v1L) ∧
      ∀ g ∈ std₁.vW, ∀ a ∈ v1L, lcomp (wordL (invW g)) a ∈ v1L) := by
  decide +kernel

theorem e16_wit : ∀ k < 16,
    wordL (prodW std₁.eW (eIdx.getD k [])) = e1L.getD k [] ∧
      wordL (prodW std₂.eW (eIdx.getD k [])) = e2L.getD k [] ∧
      (∀ i ∈ eIdx.getD k [], i < 4) := by
  decide +kernel

theorem e16_len : e1L.length = 16 ∧ e2L.length = 16 := by decide

theorem e16_inv : ∀ a ∈ e1L, ∀ v ∈ v1L, lcomp (lcomp a v) (lcomp a v) = List.range 42 →
    lcomp a v ∈ e1L ∨ lcomp a v ∈ e2L := by
  decide +kernel

abbrev E1 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet std₁.eW)

abbrev E2 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet std₂.eW)

abbrev V1 : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure (wordSet std₁.vW)

theorem lrep_E1 {x : Equiv.Perm (Fin 42)} (hx : x ∈ E1) : ∃ a ∈ e1L, LRep a x :=
  lrep_of_closed e16_closed.1.1 e16_closed.1.2.1 e16_closed.1.2.2 hx

theorem lrep_E2 {x : Equiv.Perm (Fin 42)} (hx : x ∈ E2) : ∃ a ∈ e2L, LRep a x :=
  lrep_of_closed e16_closed.2.1.1 e16_closed.2.1.2.1 e16_closed.2.1.2.2 hx

theorem lrep_V1 {x : Equiv.Perm (Fin 42)} (hx : x ∈ V1) : ∃ a ∈ v1L, LRep a x :=
  lrep_of_closed e16_closed.2.2.1 e16_closed.2.2.2.1 e16_closed.2.2.2.2 hx

theorem mem_E1_of_lrep {a : List ℕ} (ha : a ∈ e1L) {x : Equiv.Perm (Fin 42)} (hx : LRep a x) :
    x ∈ E1 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨h1, -, h3⟩ := e16_wit k (e16_len.1 ▸ hk)
  rw [List.getD_eq_getElem _ _ hk] at h1
  rw [hx.perm_eq (h1 ▸ lrep_wordL _)]
  exact wordPerm_prodW_mem _ fun i hi => by simpa [std₁] using h3 i hi

theorem mem_E2_of_lrep {a : List ℕ} (ha : a ∈ e2L) {x : Equiv.Perm (Fin 42)} (hx : LRep a x) :
    x ∈ E2 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨-, h2, h3⟩ := e16_wit k (e16_len.2 ▸ hk)
  rw [List.getD_eq_getElem _ _ hk] at h2
  rw [hx.perm_eq (h2 ▸ lrep_wordL _)]
  exact wordPerm_prodW_mem _ fun i hi => by simpa [std₂] using h3 i hi

theorem card_le_of_lrep {H : Subgroup (Equiv.Perm (Fin 42))} {A : List (List ℕ)}
    (h : ∀ x ∈ H, ∃ a ∈ A, LRep a x) : Nat.card ↥H ≤ A.length := by
  classical
  choose f hf hfr using fun x : ↥H => h x x.2
  have hinj : Function.Injective fun x : ↥H =>
      (⟨f x, List.mem_toFinset.2 (hf x)⟩ : ↥A.toFinset) := by
    intro x y hxy
    have e : f x = f y := congrArg Subtype.val hxy
    exact Subtype.ext ((hfr x).perm_eq (e ▸ hfr y))
  calc Nat.card ↥H ≤ Nat.card ↥A.toFinset := Nat.card_le_card_of_injective _ hinj
    _ = A.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ A.length := List.toFinset_card_le A

theorem mem_E1_or_E2
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) (h2 : t * t = 1) : t ∈ E1 ∨ t ∈ E2 := by
  obtain ⟨hd, -⟩ := parData_std std₁_ok (p := 2) rfl P1_eq_stab card_stab_two
  obtain ⟨e, he, v, hv, hev⟩ := hd.mulF ⟨t, T0_le_S ht⟩ ht
  have hev' : t = (e : Equiv.Perm (Fin 42)) * (v : Equiv.Perm (Fin 42)) :=
    congrArg Subtype.val hev
  obtain ⟨a, ha, hae⟩ := lrep_E1 he
  obtain ⟨b, hb, hbv⟩ := lrep_V1 hv
  have htl : LRep (lcomp a b) t := hev' ▸ hae.comp hbv
  have hsq : lcomp (lcomp a b) (lcomp a b) = List.range 42 :=
    (htl.comp htl).eq (by rw [h2]; exact lrep_range)
  rcases e16_inv a ha b hb hsq with h | h
  · exact Or.inl (mem_E1_of_lrep h htl)
  · exact Or.inr (mem_E2_of_lrep h htl)

theorem e16_eq
    {A₀ : Subgroup ↥S} (hA : A₀ ≤ T0.subgroupOf S) (hsq : ∀ a ∈ A₀, a * a = 1)
    (hc : Nat.card ↥A₀ = 16) : A₀ = E1.subgroupOf S ∨ A₀ = E2.subgroupOf S := by
  have hsub : (A₀ : Set ↥S) ⊆ ↑(E1.subgroupOf S) ∪ ↑(E2.subgroupOf S) := fun a ha =>
    mem_E1_or_E2 (hA ha) (congrArg Subtype.val (hsq a ha))
  rcases SubgroupClass.subset_union.1 hsub with h | h
  · refine Or.inl (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [hc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (closure_wordSet_le _)).toEquiv]
    exact (card_le_of_lrep fun x hx => lrep_E1 hx).trans e16_len.1.le
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [hc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (closure_wordSet_le _)).toEquiv]
    exact (card_le_of_lrep fun x hx => lrep_E2 hx).trans e16_len.2.le

theorem pCoreOf_eq_of_parData {G : Type*} [Group G] [Finite G] {Q E V F : Subgroup G}
    (hd : ParData Q E V F) : pCoreOf 2 Q = E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (hd.core _ (pCoreOf_le 2 Q) (le_normalizer_pCoreOf 2 Q)
    (pCoreOf_isPGroup 2 Q)) ?_
  exact le_pCoreOf 2 hd.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hd.le).2 hd.normal)
    (isPGroup_of_mul_self hd.sq)

theorem exists_parabolic_of_e16
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 2) (A : Subgroup X)
    (_hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a ^ 2 = 1)
    (hcard : Nat.card ↥A = 16) :
    ∃ Q : Subgroup X, A ≤ Q ∧ Nat.card ↥Q = 960 ∧
      Q ≤ Subgroup.normalizer (A : Set X) ∧ pCoreOf 2 Q = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ⟩ := exact_model.2.2.2.1 X hX
  set A' := A.map ψ.toMonoidHom with hA'
  have hA'sq : ∀ a ∈ A', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← sq, hsq a ha, map_one]
  obtain ⟨T, hT⟩ := (isPGroup_of_mul_self hA'sq).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S sylowT0 T
  have hgT : MulAut.conj g • T0.subgroupOf S = (T : Subgroup ↥S) := by
    have h1 := congrArg (fun P : Sylow 2 ↥S => (P : Subgroup ↥S)) hg
    simp only [Sylow.coe_subgroup_smul, coe_sylowT0] at h1
    exact h1
  set A₀ := MulAut.conj g⁻¹ • A' with hA₀
  have hA'A₀ : A' = MulAut.conj g • A₀ := by
    rw [hA₀, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hA₀T : A₀ ≤ T0.subgroupOf S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
    have h1 : y ∈ MulAut.conj g • T0.subgroupOf S := by
      rw [hgT]
      exact hT hy
    obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using ht
  have hA₀sq : ∀ a ∈ A₀, a * a = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [← smul_mul', hA'sq y hy, smul_one]
  have hA₀c : Nat.card ↥A₀ = 16 := by
    rw [hA₀, ← hcard, ← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    exact Set.natCard_smul_set _ (A' : Set ↥S)
  set φ : ↥S ≃* X := (MulAut.conj g).trans ψ.symm with hφ
  have hAφ : A₀.map φ.toMonoidHom = A := by
    have h1 : A₀.map φ.toMonoidHom = (A₀.map (MulAut.conj g).toMonoidHom).map ψ.symm.toMonoidHom :=
      by rw [Subgroup.map_map]; rfl
    rw [h1, ← conj_smul_eq_map, ← hA'A₀, hA']
    ext x
    simp
  have key : ∀ (Q₀ E₀ V₀ F₀ : Subgroup ↥S), ParData Q₀ E₀ V₀ F₀ → Nat.card ↥Q₀ = 960 →
      A₀ = E₀ → ∃ Q : Subgroup X, A ≤ Q ∧ Nat.card ↥Q = 960 ∧
        Q ≤ Subgroup.normalizer (A : Set X) ∧ pCoreOf 2 Q = A := by
    rintro Q₀ E₀ V₀ F₀ hd hQ₀ rfl
    have hd' := hd.map_equiv φ
    rw [hAφ] at hd'
    exact ⟨_, hd'.le, by rw [Subgroup.card_map_of_injective φ.injective, hQ₀], hd'.normal,
      pCoreOf_eq_of_parData hd'⟩
  rcases e16_eq hA₀T hA₀sq hA₀c with h | h
  · exact key _ _ _ _ (parData_std std₁_ok (p := 2) rfl P1_eq_stab card_stab_two).1
      card_stab_two h
  · exact key _ _ _ _ (parData_std std₂_ok (p := 23) rfl P2_eq_stab card_stab_tt).1
      card_stab_tt h

end CFSG.Quasithin.H.L34Cov
