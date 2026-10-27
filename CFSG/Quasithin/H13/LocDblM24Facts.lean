module

public import CFSG.Quasithin.H13.LocDblM24Tab
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Data.DcM24

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Facts

open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.M24Prof CFSG.Quasithin.H13.LocDbl.M24Tab
open CFSG.Quasithin.H13.LocDbl.DcM24 (ta tb)

@[expose] def letterElt : ℕ → ↥NativeSporadic.M24
  | 0 => m24a
  | 1 => m24b
  | _ => m24b * m24b

@[expose] def wordElt (w : List ℕ) : ↥NativeSporadic.M24 := (w.map letterElt).prod

@[expose] def letterTab : ℕ → List ℕ
  | 0 => ta.toList
  | 1 => tb.toList
  | _ => compTab tb.toList tb.toList

@[expose] def wordTab (w : List ℕ) : List ℕ := (w.map letterTab).foldr compTab (List.range 24)

theorem tab_m24a : tab 24 m24a = ta.toList := by decide

theorem tab_m24b : tab 24 m24b = tb.toList := by decide

theorem tab_letterElt (l : ℕ) : tab 24 (letterElt l) = letterTab l := by
  rcases l with _ | _ | l
  · exact tab_m24a
  · exact tab_m24b
  · show tab 24 (m24b * m24b) = compTab tb.toList tb.toList
    rw [tab_mul, tab_m24b]

theorem tab_wordElt (w : List ℕ) : tab 24 (wordElt w) = wordTab w := by
  induction w with
  | nil => exact tab_one'
  | cons l w ih =>
    unfold wordElt wordTab at *
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, tab_mul, tab_letterElt, ih]

theorem hwords_of_tables (gens : List ↥NativeSporadic.M24) (gt : List (List ℕ))
    (hl : gens.length = gt.length)
    (h : ∀ i < gens.length, tab 24 (gens.getD i 1) = gt.getD i (List.range 24))
    (Lw : List (List ℕ × List ℕ))
    (hdec : ∀ q ∈ Lw, (q.2.map fun i => gt.getD i (List.range 24)).foldr compTab (List.range 24) =
      q.1) :
    ∀ q ∈ Lw, (q.2.map fun i => tab 24 (gens.getD i 1)).foldr compTab (List.range 24) = q.1 := by
  intro q hq
  rw [← hdec q hq]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < gens.length
  · exact h i hi
  · rw [List.getD_eq_default _ _ (not_lt.1 hi),
      List.getD_eq_default _ _ (by omega : gt.length ≤ i), tab_one']

theorem eq_one_of_fixCount_eq {Γ : Type} [Group Γ] [MulAction Γ (Fin 24)] [FaithfulSMul Γ (Fin 24)]
    {g : Γ} (h : fixCount g = 24) : g = 1 := by
  classical
  unfold fixCount at h
  have h1 := Finset.filter_card_eq (s := (Finset.univ : Finset (Fin 24)))
    (p := fun p : Fin 24 => g • p = p) (by simpa using h)
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin 24) fun p => ?_
  rw [one_smul]
  exact h1 p (Finset.mem_univ p)

theorem factorization_eq_of {n p k : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (h1 : p ^ k ∣ n)
    (h2 : ¬ p ^ (k + 1) ∣ n) : n.factorization p = k := by
  have a := (hp.out.pow_dvd_iff_le_factorization hn).1 h1
  have b : ¬ (k + 1 ≤ n.factorization p) := fun h =>
    h2 ((hp.out.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem m24_stab_two (p : Fin 24) :
    ¬ 2 ^ 8 ∣ Nat.card (MulAction.stabilizer ↥NativeSporadic.M24 p) := by
  have h2 : MulAction.IsMultiplyPretransitive ↥NativeSporadic.M24 (Fin 24) 2 :=
    isMultiplyPretransitive_two m24_hyp (by decide) (by norm_num)
  haveI : MulAction.IsPretransitive ↥NativeSporadic.M24 (Fin 24) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [card_stabilizer_eq p (by simp), card_M24, Nat.card_fin]
  norm_num

@[expose] def w5 : List ℕ := [2, 0, 2, 0, 1, 0, 1, 0]

@[expose] def y5 : ↥NativeSporadic.M24 := wordElt w5

@[expose] def Lw5 : List (List ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], []),
    ([8, 1, 13, 2, 5, 3, 6, 11, 12, 17, 18, 22,
      15, 4, 9, 16, 0, 21, 7, 19, 14, 20, 10, 23], [0]),
    ([12, 1, 4, 13, 3, 2, 6, 22, 15, 21, 7, 10,
      16, 5, 17, 0, 8, 20, 11, 19, 9, 14, 18, 23], [0, 0]),
    ([15, 1, 5, 4, 2, 13, 6, 10, 16, 20, 11, 18,
      0, 3, 21, 8, 12, 14, 22, 19, 17, 9, 7, 23], [0, 0, 0]),
    ([16, 1, 3, 5, 13, 4, 6, 18, 0, 14, 22, 7,
      8, 2, 20, 12, 15, 9, 10, 19, 21, 17, 11, 23], [0, 0, 0, 0])]

theorem y5_tab : tab 24 y5 = wordTab w5 := tab_wordElt _

theorem y5_pow : y5 * y5 * y5 * y5 * y5 = 1 := by
  apply tab_injective_of_faithful
  simp only [tab_mul, tab_one', y5_tab]
  decide

theorem y5_inv : y5⁻¹ = y5 * y5 * y5 * y5 := (eq_inv_of_mul_eq_one_left y5_pow).symm

theorem y5_closure :
    Nat.card (Subgroup.closure {g | g ∈ [y5]}) = 5 ∧
      ∀ x ∈ Subgroup.closure {g | g ∈ [y5]}, tab 24 x ∈ Lw5.map Prod.fst := by
  have key := card_closure_of_tables (Γ := ↥NativeSporadic.M24) [y5] Lw5 (by decide)
    (by rw [tab_one']; decide) ?_ (by decide) ?_
  · exact key
  · intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    refine ⟨by rw [y5_tab]; decide, ?_⟩
    rw [y5_inv]
    simp only [tab_mul, y5_tab]
    decide
  · refine hwords_of_tables [y5] [wordTab w5] rfl ?_ Lw5 (by decide)
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    exact y5_tab

theorem m24_fix5 :
    ∀ y : ↥NativeSporadic.M24, orderOf y = 5 → fixCount y ≤ 4 := by
  intro y hy
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : Nat.card (Subgroup.closure {g | g ∈ [y5]}) =
      5 ^ (Nat.card ↥NativeSporadic.M24).factorization 5 := by
    rw [y5_closure.1, card_M24, factorization_eq_of (k := 1) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have hfix : ∀ x ∈ Subgroup.closure {g | g ∈ [y5]}, fixCount x ∈ ({4, 24} : Set ℕ) := by
    intro x hx
    have h := y5_closure.2 x hx
    rw [fixCount_eq]
    have key : ∀ t ∈ Lw5.map Prod.fst,
        ((List.range 24).filter fun i => t.getD i 0 == i).length = 4 ∨
        ((List.range 24).filter fun i => t.getD i 0 == i).length = 24 := by decide
    exact key _ h
  have hx : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  have hmem := fixCount_mem_of_sylow 5 _ hP {4, 24} hfix hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · omega
  · exfalso
    have h1 := eq_one_of_fixCount_eq h
    rw [h1, orderOf_one] at hy
    omega


@[expose] def w3x : List ℕ := [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0]

@[expose] def w3y : List ℕ :=
  [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2]

@[expose] def g3 : List ↥NativeSporadic.M24 := [wordElt w3x, wordElt w3y]

@[expose] def Lw3 : List (List ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], []),
    ([1, 8, 4, 13, 12, 20, 6, 10, 0, 14, 23, 11,
      2, 16, 15, 9, 3, 5, 18, 19, 17, 21, 22, 7], [1]),
    ([10, 1, 2, 3, 4, 15, 22, 8, 13, 21, 16, 5,
      12, 7, 19, 11, 0, 9, 6, 20, 14, 17, 18, 23], [0]),
    ([1, 13, 4, 7, 12, 14, 22, 16, 10, 19, 23, 5,
      2, 0, 11, 21, 3, 15, 6, 20, 9, 17, 18, 8], [0, 1]),
    ([8, 0, 12, 16, 2, 17, 6, 23, 1, 15, 7, 11,
      4, 3, 9, 14, 13, 20, 18, 19, 5, 21, 22, 10], [1, 1]),
    ([16, 1, 2, 3, 4, 11, 18, 13, 7, 17, 0, 15,
      12, 8, 20, 5, 10, 21, 22, 14, 19, 9, 6, 23], [0, 0]),
    ([23, 8, 4, 13, 12, 9, 22, 0, 16, 21, 3, 20,
      2, 10, 19, 11, 1, 14, 6, 17, 15, 5, 18, 7], [1, 0]),
    ([1, 7, 4, 8, 12, 19, 18, 0, 16, 20, 23, 15,
      2, 10, 5, 17, 3, 11, 22, 14, 21, 9, 6, 13], [0, 0, 1]),
    ([3, 8, 4, 13, 12, 11, 18, 16, 10, 5, 1, 9,
      2, 0, 17, 20, 23, 21, 22, 15, 19, 14, 6, 7], [1, 0, 0]),
    ([7, 0, 12, 16, 2, 14, 22, 1, 3, 21, 13, 17,
      4, 23, 19, 11, 8, 15, 6, 5, 9, 20, 18, 10], [1, 1, 0]),
    ([8, 16, 12, 10, 2, 15, 22, 3, 23, 19, 7, 20,
      4, 1, 11, 21, 13, 9, 6, 17, 14, 5, 18, 0], [1, 0, 1]),
    ([13, 10, 12, 0, 2, 9, 22, 23, 1, 11, 8, 5,
      4, 3, 21, 19, 7, 14, 6, 20, 15, 17, 18, 16], [0, 1, 1]),
    ([23, 13, 4, 7, 12, 21, 18, 10, 0, 17, 3, 14,
      2, 16, 20, 5, 1, 19, 22, 9, 11, 15, 6, 8], [0, 1, 0]),
    ([0, 3, 2, 23, 4, 9, 22, 13, 7, 19, 10, 17,
      12, 8, 11, 21, 16, 14, 6, 5, 15, 20, 18, 1], [1, 1, 0, 1]),
    ([3, 13, 4, 7, 12, 5, 6, 0, 16, 15, 1, 21,
      2, 10, 9, 14, 23, 17, 18, 11, 20, 19, 22, 8], [0, 1, 0, 0]),
    ([7, 16, 12, 10, 2, 21, 18, 23, 1, 5, 13, 15,
      4, 3, 17, 20, 8, 19, 22, 14, 11, 9, 6, 0], [0, 0, 1, 1]),
    ([8, 10, 12, 0, 2, 19, 18, 1, 3, 17, 7, 9,
      4, 23, 20, 5, 13, 11, 22, 15, 21, 14, 6, 16], [0, 1, 1, 0]),
    ([13, 0, 12, 16, 2, 11, 18, 3, 23, 20, 8, 14,
      4, 1, 5, 17, 7, 21, 22, 9, 19, 15, 6, 10], [0, 1, 0, 1]),
    ([16, 23, 2, 1, 4, 14, 22, 7, 8, 11, 0, 20,
      12, 13, 21, 19, 10, 15, 6, 17, 9, 5, 18, 3], [1, 0, 1, 1]),
    ([23, 7, 4, 8, 12, 17, 6, 16, 10, 9, 3, 19,
      2, 0, 14, 15, 1, 20, 18, 21, 5, 11, 22, 13], [0, 0, 1, 0]),
    ([0, 23, 2, 1, 4, 19, 18, 8, 13, 5, 10, 14,
      12, 7, 17, 20, 16, 11, 22, 9, 21, 15, 6, 3], [0, 1, 0, 1, 1]),
    ([3, 7, 4, 8, 12, 15, 22, 10, 0, 11, 1, 17,
      2, 16, 21, 19, 23, 9, 6, 5, 14, 20, 18, 13], [0, 0, 1, 0, 0]),
    ([7, 10, 12, 0, 2, 5, 6, 3, 23, 14, 13, 19,
      4, 1, 15, 9, 8, 17, 18, 21, 20, 11, 22, 16], [0, 0, 1, 0, 1]),
    ([10, 3, 2, 23, 4, 21, 18, 7, 8, 20, 16, 9,
      12, 13, 5, 17, 0, 19, 22, 15, 11, 14, 6, 1], [0, 1, 1, 0, 1]),
    ([13, 16, 12, 10, 2, 20, 6, 1, 3, 9, 8, 21,
      4, 23, 14, 15, 7, 5, 18, 11, 17, 19, 22, 0], [0, 0, 1, 1, 0]),
    ([10, 23, 2, 1, 4, 20, 6, 13, 7, 15, 16, 19,
      12, 8, 9, 14, 0, 5, 18, 21, 17, 11, 22, 3], [0, 0, 1, 0, 1, 1]),
    ([16, 3, 2, 23, 4, 17, 6, 8, 13, 14, 0, 21,
      12, 7, 15, 9, 10, 20, 18, 11, 5, 19, 22, 1], [0, 0, 1, 1, 0, 1])]

theorem g3_gen : ∀ g ∈ g3, tab 24 g ∈ Lw3.map Prod.fst ∧ tab 24 g⁻¹ ∈ Lw3.map Prod.fst := by
  have key : ∀ w ∈ [w3x, w3y],
      wordTab w ∈ Lw3.map Prod.fst ∧
        compTab (wordTab w) (compTab (wordTab w) (wordTab w)) = List.range 24 ∧
        compTab (wordTab w) (wordTab w) ∈ Lw3.map Prod.fst := by decide
  intro g hg
  simp only [g3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := key w3x (by simp)
    rw [tab_wordElt]
    refine ⟨h1, ?_⟩
    rw [tab_inv_of_cube (by rw [tab_wordElt]; exact h2), tab_wordElt]
    exact h3
  · obtain ⟨h1, h2, h3⟩ := key w3y (by simp)
    rw [tab_wordElt]
    refine ⟨h1, ?_⟩
    rw [tab_inv_of_cube (by rw [tab_wordElt]; exact h2), tab_wordElt]
    exact h3

theorem g3_closure :
    Nat.card (Subgroup.closure {g | g ∈ g3}) = 27 ∧
      ∀ x ∈ Subgroup.closure {g | g ∈ g3}, tab 24 x ∈ Lw3.map Prod.fst := by
  have key := card_closure_of_tables (Γ := ↥NativeSporadic.M24) g3 Lw3 (by decide)
    (by rw [tab_one']; decide) g3_gen (by decide) ?_
  · exact key
  · refine hwords_of_tables g3 [wordTab w3x, wordTab w3y] rfl ?_ Lw3 (by decide)
    intro i hi
    have hi2 : i < 2 := by simpa [g3] using hi
    interval_cases i
    · exact tab_wordElt _
    · exact tab_wordElt _

theorem m24_fix3 :
    ∀ x : ↥NativeSporadic.M24, x ≠ 1 → x ^ 3 = 1 → fixCount x = 0 ∨ fixCount x = 6 := by
  intro x hx1 hx3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP : Nat.card (Subgroup.closure {g | g ∈ g3}) =
      3 ^ (Nat.card ↥NativeSporadic.M24).factorization 3 := by
    rw [g3_closure.1, card_M24, factorization_eq_of (k := 3) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have hfix : ∀ y ∈ Subgroup.closure {g | g ∈ g3}, fixCount y ∈ ({0, 6, 24} : Set ℕ) := by
    intro y hy
    have h := g3_closure.2 y hy
    rw [fixCount_eq]
    have key : ∀ t ∈ Lw3.map Prod.fst,
        ((List.range 24).filter fun i => t.getD i 0 == i).length = 0 ∨
        ((List.range 24).filter fun i => t.getD i 0 == i).length = 6 ∨
        ((List.range 24).filter fun i => t.getD i 0 == i).length = 24 := by decide
    simpa using key _ h
  have hx : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]; norm_num)
  have hmem := fixCount_mem_of_sylow 3 _ hP {0, 6, 24} hfix hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (eq_one_of_fixCount_eq h) hx1

end CFSG.Quasithin.H13.LocDbl.M24Facts
