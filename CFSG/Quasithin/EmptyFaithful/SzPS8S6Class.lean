module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin

namespace SzPS8

namespace S6Class

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

@[expose] def cycFive : Perm (Fin 6) := [(0 : Fin 6), 1, 2, 3, 4].formPerm

@[expose] def cycFour : Perm (Fin 6) := [(1 : Fin 6), 2, 4, 3].formPerm

@[expose] def invZeroInf : Perm (Fin 6) := swap 0 5 * swap 1 4

@[expose] def s5p : Subgroup (Perm (Fin 6)) := MulAction.stabilizer (Perm (Fin 6)) (5 : Fin 6)

@[expose] def a5p : Subgroup (Perm (Fin 6)) := s5p ⊓ alternatingGroup (Fin 6)

@[expose] def pgl25 : Subgroup (Perm (Fin 6)) :=
  Subgroup.closure {cycFive, cycFour, invZeroInf}

@[expose] def psl25 : Subgroup (Perm (Fin 6)) := pgl25 ⊓ alternatingGroup (Fin 6)

theorem mem_s5p {g : Perm (Fin 6)} : g ∈ s5p ↔ g 5 = 5 := by
  simp [s5p, MulAction.mem_stabilizer_iff]

theorem mem_a5p {g : Perm (Fin 6)} : g ∈ a5p ↔ g 5 = 5 ∧ Perm.sign g = 1 := by
  simp [a5p, mem_s5p, mem_alternatingGroup]

theorem natCard_eq_filter (H : Subgroup (Perm (Fin 6))) (P : Perm (Fin 6) → Prop)
    [DecidablePred P] (h : ∀ g, g ∈ H ↔ P g) : Nat.card H = (Finset.univ.filter P).card := by
  have : Nat.card H = Nat.card {g : Perm (Fin 6) // P g} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem six_mul_card_le (H : Subgroup (Perm (Fin 6))) (h : ∀ y : Fin 6, ∃ t ∈ H, t 5 = y) :
    6 * Nat.card ↥(H ⊓ s5p) ≤ Nat.card ↥H := by
  choose! t ht ht5 using h
  let f : Fin 6 × ↥(H ⊓ s5p) → ↥H := fun p =>
    ⟨t p.1 * p.2, H.mul_mem (ht p.1) (Subgroup.mem_inf.mp p.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ hyy
    have h5 : ∀ (z : Fin 6) (r : ↥(H ⊓ s5p)), (t z * (r : Perm (Fin 6))) 5 = z := by
      intro z r
      have : (r : Perm (Fin 6)) 5 = 5 := mem_s5p.mp (Subgroup.mem_inf.mp r.2).2
      simp [Perm.mul_apply, this, ht5]
    have h1 := congrArg (fun x : ↥H => (x : Perm (Fin 6)) 5) hyy
    simp only [f] at h1
    rw [h5, h5] at h1
    subst h1
    have h2 : (t y * (s : Perm (Fin 6))) = t y * (s' : Perm (Fin 6)) :=
      congrArg (fun x : ↥H => (x : Perm (Fin 6))) hyy
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h2))
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using this

theorem exists_pow_cycFive : ∀ x y : Fin 6, x ≠ 5 → y ≠ 5 → ∃ i : Fin 5,
    (cycFive ^ (i : ℕ)) x = y := by
  decide +kernel

theorem card_s5p : Nat.card s5p = 120 := by
  rw [natCard_eq_filter s5p (fun g => g 5 = 5) fun g => mem_s5p]
  decide +kernel

theorem card_a5p : Nat.card a5p = 60 := by
  rw [natCard_eq_filter a5p (fun g => g 5 = 5 ∧ Perm.sign g = 1) fun g => mem_a5p]
  decide +kernel

theorem card_top_six : Nat.card (⊤ : Subgroup (Perm (Fin 6))) = 720 := by
  rw [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [natCard_eq_filter _ (fun g => Perm.sign g = 1) fun g => mem_alternatingGroup]
  decide +kernel

def code (g : Perm (Fin 6)) : ℕ :=
  (g 0).val + 6 * (g 1).val + 36 * (g 2).val + 216 * (g 3).val + 1296 * (g 4).val

def pglCodes : List ℕ :=
  [310, 353, 392, 411, 491, 574, 585, 637, 710, 751, 809, 838, 933, 947, 985, 1064, 1132, 1179,
   1196, 1243, 1402, 1421, 1460, 1503, 1761, 1860, 1877, 1930, 1960, 2045, 2118, 2126, 2183,
   2235, 2300, 2352, 2402, 2466, 2488, 2535, 2657, 2710, 2769, 2791, 2835, 2946, 2975, 2992,
   3251, 3310, 3385, 3444, 3487, 3510, 3569, 3645, 3694, 3711, 3805, 3822, 3956, 3985, 4043,
   4084, 4138, 4181, 4260, 4310, 4349, 4360, 4495, 4506, 4760, 4805, 4854, 4933, 4981, 5028,
   5050, 5114, 5235, 5279, 5323, 5372, 5417, 5505, 5510, 5598, 5635, 5682, 5735, 5799, 5864,
   5873, 5910, 6025, 6273, 6320, 6337, 6384, 6538, 6561, 6614, 6637, 6716, 6792, 6820, 6843,
   6922, 6975, 7021, 7074, 7153, 7176, 7204, 7280, 7359, 7382, 7435, 7458]

theorem code_mul_mem : ∀ g : Perm (Fin 6), code g ∈ pglCodes →
    code (g * cycFive) ∈ pglCodes ∧ code (g * cycFour) ∈ pglCodes ∧
    code (g * invZeroInf) ∈ pglCodes ∧ code (g * cycFive⁻¹) ∈ pglCodes ∧
    code (g * cycFour⁻¹) ∈ pglCodes ∧ code (g * invZeroInf⁻¹) ∈ pglCodes := by
  decide +kernel

theorem card_filter_code :
    (Finset.univ.filter fun g : Perm (Fin 6) => code g ∈ pglCodes).card = 120 := by
  decide +kernel

theorem code_one : code (1 : Perm (Fin 6)) ∈ pglCodes := by
  decide +kernel

theorem code_mem_of_mem_pgl25 {g : Perm (Fin 6)} (hg : g ∈ pgl25) : code g ∈ pglCodes := by
  refine Subgroup.closure_induction_right (p := fun x _ => code x ∈ pglCodes) ?_ ?_ ?_ hg
  · exact code_one
  · intro x _ y hy ih
    rcases hy with rfl | rfl | rfl
    · exact (code_mul_mem x ih).1
    · exact (code_mul_mem x ih).2.1
    · exact (code_mul_mem x ih).2.2.1
  · intro x _ y hy ih
    rcases hy with rfl | rfl | rfl
    · exact (code_mul_mem x ih).2.2.2.1
    · exact (code_mul_mem x ih).2.2.2.2.1
    · exact (code_mul_mem x ih).2.2.2.2.2

theorem cycFive_mem_pgl25 : cycFive ∈ pgl25 := Subgroup.subset_closure (by simp)

theorem cycFour_mem_pgl25 : cycFour ∈ pgl25 := Subgroup.subset_closure (by simp)

theorem invZeroInf_mem_pgl25 : invZeroInf ∈ pgl25 := Subgroup.subset_closure (by simp)

theorem orderOf_cycFive : orderOf cycFive = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_cycFour : orderOf cycFour = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := cycFour)
    (by decide +kernel) (by decide +kernel)
  simpa using h

theorem card_pgl25_ge : 120 ≤ Nat.card pgl25 := by
  have htrans : ∀ y : Fin 6, ∃ t ∈ pgl25, t 5 = y := by
    intro y
    by_cases hy : y = 5
    · exact ⟨1, one_mem _, by simp [hy]⟩
    · obtain ⟨i, hi⟩ := exists_pow_cycFive 0 y (by decide) hy
      refine ⟨cycFive ^ (i : ℕ) * invZeroInf,
        mul_mem (pow_mem cycFive_mem_pgl25 _) invZeroInf_mem_pgl25, ?_⟩
      have h0 : invZeroInf 5 = 0 := by decide +kernel
      simp [Perm.mul_apply, h0, hi]
  have h1 := six_mul_card_le pgl25 htrans
  have h5 : 5 ∣ Nat.card ↥(pgl25 ⊓ s5p) := by
    have hmem : cycFive ∈ pgl25 ⊓ s5p :=
      Subgroup.mem_inf.mpr ⟨cycFive_mem_pgl25, mem_s5p.mpr (by decide +kernel)⟩
    have := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hmem)
    rwa [Nat.card_zpowers, orderOf_cycFive] at this
  have h4 : 4 ∣ Nat.card ↥(pgl25 ⊓ s5p) := by
    have hmem : cycFour ∈ pgl25 ⊓ s5p :=
      Subgroup.mem_inf.mpr ⟨cycFour_mem_pgl25, mem_s5p.mpr (by decide +kernel)⟩
    have := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hmem)
    rwa [Nat.card_zpowers, orderOf_cycFour] at this
  have h20 : 20 ∣ Nat.card ↥(pgl25 ⊓ s5p) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 4) h5 h4
  have hpos : 0 < Nat.card ↥(pgl25 ⊓ s5p) := Nat.card_pos
  have := Nat.le_of_dvd hpos h20
  omega

theorem mem_pgl25 {g : Perm (Fin 6)} : g ∈ pgl25 ↔ code g ∈ pglCodes := by
  classical
  have hsub : (Finset.univ.filter fun x : Perm (Fin 6) => x ∈ pgl25) ⊆
      Finset.univ.filter fun x : Perm (Fin 6) => code x ∈ pglCodes := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact code_mem_of_mem_pgl25 hx
  have hcard : (Finset.univ.filter fun x : Perm (Fin 6) => code x ∈ pglCodes).card ≤
      (Finset.univ.filter fun x : Perm (Fin 6) => x ∈ pgl25).card := by
    rw [card_filter_code, ← natCard_eq_filter pgl25 _ fun _ => Iff.rfl]
    exact card_pgl25_ge
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨code_mem_of_mem_pgl25, fun h => ?_⟩
  have : g ∈ Finset.univ.filter fun x : Perm (Fin 6) => code x ∈ pglCodes := by simp [h]
  rw [← heq] at this
  simpa using this

theorem card_pgl25 : Nat.card pgl25 = 120 := by
  rw [natCard_eq_filter pgl25 (fun g => code g ∈ pglCodes) fun g => mem_pgl25]
  exact card_filter_code

theorem mem_psl25 {g : Perm (Fin 6)} : g ∈ psl25 ↔ code g ∈ pglCodes ∧ Perm.sign g = 1 := by
  simp [psl25, mem_pgl25, mem_alternatingGroup]

theorem card_psl25 : Nat.card psl25 = 60 := by
  rw [natCard_eq_filter psl25 (fun g => code g ∈ pglCodes ∧ Perm.sign g = 1) fun g => mem_psl25]
  decide +kernel

def letter (a b : Perm (Fin 6)) : ℕ → Perm (Fin 6)
  | 0 => a
  | 1 => a⁻¹
  | 2 => b
  | _ => b⁻¹

def wordEval (a b : Perm (Fin 6)) (w : List ℕ) : Perm (Fin 6) :=
  (w.map (letter a b)).prod

theorem wordEval_mem {T : Subgroup (Perm (Fin 6))} {a b : Perm (Fin 6)} (ha : a ∈ T)
    (hb : b ∈ T) (w : List ℕ) : wordEval a b w ∈ T := by
  refine T.list_prod_mem fun x hx => ?_
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
  match n with
  | 0 => exact ha
  | 1 => exact T.inv_mem ha
  | 2 => exact hb
  | n + 3 => exact T.inv_mem hb

def threeCycleWords : List (List ℕ) :=
  [[0, 3, 0, 3], [0, 2, 1, 3, 3], [0, 2, 1, 2, 0, 2, 2], [0, 0, 3, 1, 2, 2], [0, 0, 2, 2]]

def stabilizerWords : List (List ℕ) := [[2, 0, 3, 1, 2], [2, 0, 2, 2], [2, 1, 2, 2]]

theorem exists_normalize : ∀ h : Perm (Fin 6), h 5 ≠ 5 → ∃ i j : Fin 5,
    (cycFive ^ (i : ℕ) * h * cycFive ^ (j : ℕ)) 5 = 0 ∧
      (cycFive ^ (i : ℕ) * h * cycFive ^ (j : ℕ)) 0 = 1 := by
  decide +kernel

theorem mem_pgl_or_three_cycle : ∀ g : Perm (Fin 6), g 5 = 0 → g 0 = 1 → code g ∈ pglCodes ∨
    ∃ w ∈ threeCycleWords, (wordEval cycFive g w).support.card = 3 := by
  decide +kernel

theorem exists_stabilizer_word : ∀ u : Perm (Fin 6), code u ∈ pglCodes → Perm.sign u = 1 →
    u 0 = 0 → u 5 ≠ 5 → u ≠ 1 → u ^ 5 = 1 → ∃ w ∈ stabilizerWords,
      (wordEval cycFive u w) 5 = 5 ∧ ∀ i : Fin 5, wordEval cycFive u w ≠ cycFive ^ (i : ℕ) := by
  decide +kernel

theorem eq_or_eq_of_inf_le (Y T : Subgroup (Perm (Fin 6)))
    (h1 : Y ⊓ alternatingGroup (Fin 6) ≤ T) (h2 : T ≤ Y) :
    T = Y ⊓ alternatingGroup (Fin 6) ∨ T = Y := by
  by_cases hodd : ∃ t ∈ T, Perm.sign t = -1
  · right
    obtain ⟨t, ht, hts⟩ := hodd
    refine le_antisymm h2 fun y hy => ?_
    rcases Int.units_eq_one_or (Perm.sign y) with hs | hs
    · exact h1 (Subgroup.mem_inf.mpr ⟨hy, mem_alternatingGroup.mpr hs⟩)
    · have hyt : y * t⁻¹ ∈ Y ⊓ alternatingGroup (Fin 6) :=
        Subgroup.mem_inf.mpr ⟨Y.mul_mem hy (Y.inv_mem (h2 ht)),
          mem_alternatingGroup.mpr (by simp [hs, hts])⟩
      simpa using T.mul_mem (h1 hyt) ht
  · left
    push Not at hodd
    refine le_antisymm (fun t ht => Subgroup.mem_inf.mpr ⟨h2 ht, ?_⟩) h1
    rcases Int.units_eq_one_or (Perm.sign t) with hs | hs
    · exact mem_alternatingGroup.mpr hs
    · exact absurd hs (hodd t ht)

theorem isSolvable_of_card_eq_pow_mul_pow {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rwa [← Nat.card_eq_fintype_card])

theorem isSolvable_of_card_le_twelve {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 12) :
    Group.IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  have h5 : (5 : ℕ).Prime := by norm_num
  have h7 : (7 : ℕ).Prime := by norm_num
  have h11 : (11 : ℕ).Prime := by norm_num
  generalize hn : Nat.card G = n at hpos h
  interval_cases n
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 0) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 0) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 0) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) h2 h5
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) h2 h7
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 0) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 2) h2 h3
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) h2 h5
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) h2 h11
      (by norm_num) (by simp [hn])
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 1) h2 h3
      (by norm_num) (by simp [hn])

theorem isSolvable_of_five_not_dvd_card {S : Subgroup (Perm (Fin 6))} (h : ¬ 5 ∣ Nat.card S) :
    Group.IsSolvable S := by
  have hd : Nat.card S ∣ 720 := by
    have h6 : Nat.card (Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [← h6]
    exact Subgroup.card_subgroup_dvd_card S
  have hcop : Nat.Coprime (Nat.card S) 5 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h))
  have h144 : Nat.card S ∣ 2 ^ 4 * 3 ^ 2 :=
    hcop.dvd_of_dvd_mul_right (by simpa using hd)
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := Nat.dvd_mul.mp h144
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm₁
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hm₂
  exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hm.symm

theorem card_le_factorial_index_of_simple {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]
    (K : Subgroup A) (hK : K ≠ ⊤) : Nat.card A ≤ (K.index).factorial := by
  have h := Subgroup.index_normalCore_le_factorial_index (H := K)
  have hnc : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ K.normalCore_le)) hK
  rwa [hnc, Subgroup.index_bot] at h

@[expose] noncomputable def embedFive : Perm (Fin 5) →* Perm (Fin 6) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 5 ↪ Fin 6)

theorem embedFive_injective : Function.Injective embedFive :=
  Equiv.Perm.viaEmbeddingHom_injective _

theorem embedFive_apply_five (x : Perm (Fin 5)) : embedFive x 5 = 5 := by
  have h : (5 : Fin 6) ∉ Set.range (Fin.castSuccEmb : Fin 5 ↪ Fin 6) := by
    simp only [Set.mem_range]
    decide
  exact Equiv.Perm.viaEmbedding_apply_of_notMem x _ _ h

theorem sign_embedFive (x : Perm (Fin 5)) : Perm.sign (embedFive x) = Perm.sign x := by
  classical
  let ι : Fin 5 ↪ Fin 6 := Fin.castSuccEmb
  simp only [embedFive, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
  convert Equiv.Perm.sign_extendDomain x (Equiv.ofInjective ι.1 ι.2)

theorem range_embedFive : embedFive.range = s5p := by
  have hle : embedFive.range ≤ s5p := by
    rintro _ ⟨x, rfl⟩
    exact mem_s5p.mpr (embedFive_apply_five x)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_s5p, ← Nat.card_congr (MonoidHom.ofInjective embedFive_injective).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem a5p_eq_map : a5p = (alternatingGroup (Fin 5)).map embedFive := by
  ext g
  constructor
  · intro hg
    obtain ⟨hg5, hs⟩ := mem_a5p.mp hg
    have hr : g ∈ embedFive.range := by rw [range_embedFive]; exact mem_s5p.mpr hg5
    obtain ⟨x, rfl⟩ := hr
    exact ⟨x, mem_alternatingGroup.mpr (by rwa [← sign_embedFive]), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_a5p.mpr ⟨embedFive_apply_five x, by rwa [sign_embedFive, ← mem_alternatingGroup]⟩

theorem isSimpleGroup_a5p : IsSimpleGroup a5p := by
  have e : ↥a5p ≃* ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.subgroupCongr a5p_eq_map).trans
      (Subgroup.equivMapOfInjective _ embedFive embedFive_injective).symm
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

theorem a5p_le_of_not_isSolvable {T : Subgroup (Perm (Fin 6))} (hT : T ≤ s5p)
    (hns : ¬ Group.IsSolvable T) : a5p ≤ T := by
  by_contra hA
  have := isSimpleGroup_a5p
  have hUa : T ⊓ a5p ≤ a5p := inf_le_right
  have hUT : T ⊓ a5p ≤ T := inf_le_left
  have hKtop : (T ⊓ a5p).subgroupOf a5p ≠ ⊤ := by
    intro h
    apply hA
    intro x hx
    have : (⟨x, hx⟩ : ↥a5p) ∈ (T ⊓ a5p).subgroupOf a5p := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1
  have hidx := card_le_factorial_index_of_simple _ hKtop
  rw [card_a5p] at hidx
  have hidx5 : 5 ≤ ((T ⊓ a5p).subgroupOf a5p).index := by
    by_contra hlt
    have h4 : ((T ⊓ a5p).subgroupOf a5p).index.factorial ≤ (4 : ℕ).factorial :=
      Nat.factorial_le (by omega)
    have h24 : (4 : ℕ).factorial = 24 := by decide
    omega
  have hmul := ((T ⊓ a5p).subgroupOf a5p).card_mul_index
  rw [card_a5p] at hmul
  have hle : Nat.card ↥((T ⊓ a5p).subgroupOf a5p) ≤ 12 := by
    have := Nat.mul_le_mul_left (Nat.card ↥((T ⊓ a5p).subgroupOf a5p)) hidx5
    omega
  have : Group.IsSolvable ↥((T ⊓ a5p).subgroupOf a5p) := isSolvable_of_card_le_twelve hle
  have : Group.IsSolvable ↥(T ⊓ a5p) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hUa).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hUa).symm.injective
  apply hns
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hUT)
    (Perm.sign.comp T.subtype) (fun x hx => ?_)
  have hx1 : Perm.sign (x : Perm (Fin 6)) = 1 := hx
  have hxa : (x : Perm (Fin 6)) ∈ a5p := mem_a5p.mpr ⟨mem_s5p.mp (hT x.2), hx1⟩
  exact ⟨⟨x, Subgroup.mem_inf.mpr ⟨x.2, hxa⟩⟩, rfl⟩

theorem cycleType_cycFive : cycFive.cycleType = {5} := by
  have hcyc : cycFive.IsCycle :=
    List.isCycle_formPerm (l := [(0 : Fin 6), 1, 2, 3, 4]) (by decide) (by decide)
  rw [hcyc.cycleType]
  have : cycFive.support.card = 5 := by decide +kernel
  rw [this]

theorem sign_cycFive : Perm.sign cycFive = 1 := by
  decide +kernel

theorem isConj_cycFive_of_orderOf_eq_five {σ : Perm (Fin 6)} (h : orderOf σ = 5) :
    IsConj σ cycFive := by
  rw [isConj_iff_cycleType_eq, cycleType_cycFive]
  have hp : (orderOf σ).Prime := by rw [h]; norm_num
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [h] at hn
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, Fintype.card_fin] at hsum
  have hn0 : n = 0 := by simp at hsum; omega
  subst hn0
  simp [hn]

theorem cycFive_apply_five : cycFive 5 = 5 := by
  decide +kernel

theorem eq_five_of_cycFive_apply_eq : ∀ y : Fin 6, cycFive y = y → y = 5 := by
  decide +kernel

theorem mem_zpowers_cycFive {g : Perm (Fin 6)} (hg : g ∈ Subgroup.zpowers cycFive) :
    ∃ i : Fin 5, g = cycFive ^ (i : ℕ) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hk : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
  have hk5 : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨⟨(k % 5).toNat, by omega⟩, ?_⟩
  have := zpow_mod_orderOf cycFive k
  rw [orderOf_cycFive] at this
  rw [← this]
  simp only [Nat.cast_ofNat]
  rw [← zpow_natCast, Int.toNat_of_nonneg hk]

theorem isPretransitive_of_exists_map_five (T : Subgroup (Perm (Fin 6)))
    (htrans : ∀ y : Fin 6, ∃ t ∈ T, t 5 = y) : MulAction.IsPretransitive T (Fin 6) := by
  rw [MulAction.isPretransitive_iff_base 5]
  intro y
  obtain ⟨t, ht, hty⟩ := htrans y
  exact ⟨⟨t, ht⟩, hty⟩

theorem exists_mem_map_five {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T)
    {g : Perm (Fin 6)} (hg : g ∈ T) (hg5 : g 5 ≠ 5) : ∀ y : Fin 6, ∃ t ∈ T, t 5 = y := by
  intro y
  by_cases hy : y = 5
  · exact ⟨1, T.one_mem, by simp [hy]⟩
  · obtain ⟨i, hi⟩ := exists_pow_cycFive (g 5) y hg5 hy
    exact ⟨cycFive ^ (i : ℕ) * g, T.mul_mem (T.pow_mem hc _) hg, by simp [Perm.mul_apply, hi]⟩

theorem isPreprimitive_of_cycFive_mem {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T)
    (htrans : ∀ y : Fin 6, ∃ t ∈ T, t 5 = y) : MulAction.IsPreprimitive T (Fin 6) := by
  have hpt := isPretransitive_of_exists_map_five T htrans
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base (5 : Fin 6) ?_
  intro B h5 hB
  have h5c : (5 : Fin 6) ∈ (⟨cycFive, hc⟩ : T) • B :=
    Set.mem_smul_set.mpr ⟨5, h5, cycFive_apply_five⟩
  have h51 : (5 : Fin 6) ∈ (1 : T) • B := by simpa using h5
  have hcB : (⟨cycFive, hc⟩ : T) • B = B := by
    have := MulAction.isBlock_iff_smul_eq_smul_of_nonempty.mp hB ⟨5, h5c, h51⟩
    simpa using this
  have hstable : ∀ x ∈ B, cycFive x ∈ B := by
    intro x hx
    have : (⟨cycFive, hc⟩ : T) • x ∈ (⟨cycFive, hc⟩ : T) • B := Set.smul_mem_smul_set hx
    rw [hcB] at this
    exact this
  have hpow : ∀ x ∈ B, ∀ i : ℕ, (cycFive ^ i) x ∈ B := by
    intro x hx i
    induction i with
    | zero => simpa using hx
    | succ i ih => rw [pow_succ', Perm.mul_apply]; exact hstable _ ih
  by_cases hx : ∃ x ∈ B, x ≠ 5
  · right
    obtain ⟨x, hxB, hx5⟩ := hx
    ext y
    simp only [Set.mem_univ, iff_true]
    by_cases hy : y = 5
    · rw [hy]; exact h5
    · obtain ⟨i, hi⟩ := exists_pow_cycFive x y hx5 hy
      rw [← hi]; exact hpow x hxB i
  · left
    push Not at hx
    intro a ha b hb
    rw [hx a ha, hx b hb]

theorem le_pgl25_of_no_three_cycle {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T)
    {g : Perm (Fin 6)} (hg : g ∈ T) (hg5 : g 5 ≠ 5) (h3 : ∀ t ∈ T, ¬ t.IsThreeCycle) :
    T ≤ pgl25 := by
  have hmoves : ∀ h ∈ T, h 5 ≠ 5 → h ∈ pgl25 := by
    intro h hh hh5
    obtain ⟨i, j, h1, h2⟩ := exists_normalize h hh5
    have hg₂ : cycFive ^ (i : ℕ) * h * cycFive ^ (j : ℕ) ∈ T :=
      T.mul_mem (T.mul_mem (T.pow_mem hc _) hh) (T.pow_mem hc _)
    rcases mem_pgl_or_three_cycle _ h1 h2 with hm | ⟨w, -, hw⟩
    · have hm' := mem_pgl25.mpr hm
      have hh' : h = (cycFive ^ (i : ℕ))⁻¹ * (cycFive ^ (i : ℕ) * h * cycFive ^ (j : ℕ)) *
          (cycFive ^ (j : ℕ))⁻¹ := by group
      rw [hh']
      exact pgl25.mul_mem (pgl25.mul_mem (pgl25.inv_mem (pgl25.pow_mem cycFive_mem_pgl25 _)) hm')
        (pgl25.inv_mem (pgl25.pow_mem cycFive_mem_pgl25 _))
    · exact absurd (card_support_eq_three_iff.mp hw) (h3 _ (wordEval_mem hc hg₂ w))
  intro h hh
  by_cases hh5 : h 5 = 5
  · have hhg : h * g ∈ pgl25 := by
      refine hmoves _ (T.mul_mem hh hg) fun hc5 => hg5 ?_
      have : h (g 5) = h 5 := by rw [← Perm.mul_apply, hc5, hh5]
      exact h.injective this
    have hg' : g ∈ pgl25 := hmoves g hg hg5
    have : h = h * g * g⁻¹ := by group
    rw [this]
    exact pgl25.mul_mem hhg (pgl25.inv_mem hg')
  · exact hmoves h hh hh5

theorem psl25_le_of_le_pgl25 {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T)
    {g : Perm (Fin 6)} (hg : g ∈ T) (hg5 : g 5 ≠ 5) (hT : T ≤ pgl25) : psl25 ≤ T := by
  obtain ⟨g', hg', hg'5⟩ := exists_mem_map_five hc hg hg5 0
  have hcpsl : cycFive ∈ psl25 :=
    Subgroup.mem_inf.mpr ⟨cycFive_mem_pgl25, mem_alternatingGroup.mpr sign_cycFive⟩
  have hc5 : cycFive 5 = 5 := cycFive_apply_five
  have hfix : ∀ y : Fin 6, cycFive y = y → y = 5 := eq_five_of_cycFive_apply_eq
  set u : Perm (Fin 6) := g' * cycFive * g'⁻¹ with hu
  have huT : u ∈ T := T.mul_mem (T.mul_mem hg' hc) (T.inv_mem hg')
  have hu_pgl : u ∈ pgl25 := hT huT
  have hsign : Perm.sign u = 1 := by simp [hu, sign_cycFive]
  have hupsl : u ∈ psl25 := Subgroup.mem_inf.mpr ⟨hu_pgl, mem_alternatingGroup.mpr hsign⟩
  have hinv : g'⁻¹ 0 = 5 := Perm.inv_eq_iff_eq.mpr hg'5.symm
  have hu0 : u 0 = 0 := by simp [hu, Perm.mul_apply, hinv, hc5, hg'5]
  have hu5 : u 5 ≠ 5 := by
    intro h
    simp only [hu, Perm.mul_apply] at h
    have h1 : cycFive (g'⁻¹ 5) = g'⁻¹ 5 := by
      have := congrArg (fun x => g'⁻¹ x) h
      simpa using this
    have h2 : g'⁻¹ 5 = 5 := hfix _ h1
    have h3 : g' 5 = 5 := by
      calc g' 5 = g' (g'⁻¹ 5) := by rw [h2]
        _ = 5 := by simp
    rw [hg'5] at h3
    exact absurd h3 (by decide)
  have hu1 : u ≠ 1 := fun h => hu5 (by simp [h])
  have hu5pow : u ^ 5 = 1 := by
    have h5 : cycFive ^ 5 = 1 := by decide +kernel
    rw [hu, conj_pow, h5]
    simp
  obtain ⟨w, -, hw5, hwnot⟩ :=
    exists_stabilizer_word u (mem_pgl25.mp hu_pgl) hsign hu0 hu5 hu1 hu5pow
  have hxT : wordEval cycFive u w ∈ T := wordEval_mem hc huT w
  have hxpsl : wordEval cycFive u w ∈ psl25 := wordEval_mem hcpsl hupsl w
  have hHtrans : ∀ y : Fin 6, ∃ t ∈ T ⊓ psl25, t 5 = y := by
    intro y
    by_cases hy : y = 5
    · exact ⟨1, (T ⊓ psl25).one_mem, by simp [hy]⟩
    · obtain ⟨i, hi⟩ := exists_pow_cycFive (u 5) y hu5 hy
      refine ⟨cycFive ^ (i : ℕ) * u, Subgroup.mem_inf.mpr ⟨T.mul_mem (T.pow_mem hc _) huT,
        psl25.mul_mem (psl25.pow_mem hcpsl _) hupsl⟩, ?_⟩
      simp [Perm.mul_apply, hi]
  have h6 := six_mul_card_le (T ⊓ psl25) hHtrans
  have hKcard : 10 ≤ Nat.card ↥((T ⊓ psl25) ⊓ s5p) := by
    have hcK : cycFive ∈ (T ⊓ psl25) ⊓ s5p :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hc, hcpsl⟩, mem_s5p.mpr hc5⟩
    have hxK : wordEval cycFive u w ∈ (T ⊓ psl25) ⊓ s5p :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxT, hxpsl⟩, mem_s5p.mpr hw5⟩
    have hz : Subgroup.zpowers cycFive ≤ (T ⊓ psl25) ⊓ s5p := (Subgroup.zpowers_le).mpr hcK
    have hdvd := Subgroup.card_dvd_of_le hz
    rw [Nat.card_zpowers, orderOf_cycFive] at hdvd
    have hpos : 0 < Nat.card ↥((T ⊓ psl25) ⊓ s5p) := Nat.card_pos
    by_contra hlt
    have h5 : Nat.card ↥((T ⊓ psl25) ⊓ s5p) = 5 := by
      obtain ⟨m, hm⟩ := hdvd
      omega
    have hz' : Subgroup.zpowers cycFive = (T ⊓ psl25) ⊓ s5p :=
      Subgroup.eq_of_le_of_card_ge hz (by rw [Nat.card_zpowers, orderOf_cycFive]; omega)
    obtain ⟨i, hi⟩ := mem_zpowers_cycFive (hz' ▸ hxK)
    exact hwnot i hi
  have hHle : T ⊓ psl25 ≤ psl25 := inf_le_right
  have hHcard : Nat.card ↥(T ⊓ psl25) ≤ 60 := by
    rw [← card_psl25]
    exact Subgroup.card_le_of_le hHle
  have hHeq : T ⊓ psl25 = psl25 := Subgroup.eq_of_le_of_card_ge hHle (by rw [card_psl25]; omega)
  intro y hy
  have : y ∈ T ⊓ psl25 := by rw [hHeq]; exact hy
  exact (Subgroup.mem_inf.mp this).1

theorem classify_of_moves {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T) {g : Perm (Fin 6)}
    (hg : g ∈ T) (hg5 : g 5 ≠ 5) :
    T = alternatingGroup (Fin 6) ∨ T = ⊤ ∨ T = pgl25 ∨ T = psl25 := by
  have htrans := exists_mem_map_five hc hg hg5
  have hprim := isPreprimitive_of_cycFive_mem hc htrans
  by_cases h3 : ∃ t ∈ T, t.IsThreeCycle
  · obtain ⟨t, ht, ht3⟩ := h3
    have halt : alternatingGroup (Fin 6) ≤ T :=
      Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim ht3 ht
    have h1 : (⊤ : Subgroup (Perm (Fin 6))) ⊓ alternatingGroup (Fin 6) ≤ T := by
      rwa [top_inf_eq]
    rcases eq_or_eq_of_inf_le ⊤ T h1 le_top with h | h
    · left
      rwa [top_inf_eq] at h
    · exact Or.inr (Or.inl h)
  · push Not at h3
    have hle := le_pgl25_of_no_three_cycle hc hg hg5 h3
    have hpsl := psl25_le_of_le_pgl25 hc hg hg5 hle
    rcases eq_or_eq_of_inf_le pgl25 T hpsl hle with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

theorem classify_of_cycFive_mem {T : Subgroup (Perm (Fin 6))} (hc : cycFive ∈ T)
    (hns : ¬ Group.IsSolvable T) :
    T = alternatingGroup (Fin 6) ∨ T = ⊤ ∨ T = s5p ∨ T = a5p ∨ T = pgl25 ∨ T = psl25 := by
  by_cases hfix : ∀ t ∈ T, t 5 = 5
  · have hT : T ≤ s5p := fun t ht => mem_s5p.mpr (hfix t ht)
    have hA := a5p_le_of_not_isSolvable hT hns
    rcases eq_or_eq_of_inf_le s5p T hA hT with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
  · push Not at hfix
    obtain ⟨g, hg, hg5⟩ := hfix
    rcases classify_of_moves hc hg hg5 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem exists_conj_mem_of_not_isSolvable (S : Subgroup (Perm (Fin 6)))
    (hS : ¬ Group.IsSolvable S) :
    ∃ σ : Perm (Fin 6), S.map (MulAut.conj σ).toMonoidHom ∈
      ({alternatingGroup (Fin 6), ⊤, s5p, a5p, pgl25, psl25} : Set (Subgroup (Perm (Fin 6)))) := by
  have h5 : 5 ∣ Nat.card S := by
    by_contra h
    exact hS (isSolvable_of_five_not_dvd_card h)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 5 h5
  have hxo : orderOf (x : Perm (Fin 6)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_cycFive_of_orderOf_eq_five hxo)
  refine ⟨τ, ?_⟩
  have hc : cycFive ∈ S.map (MulAut.conj τ).toMonoidHom := ⟨x, x.2, hτ⟩
  have hns : ¬ Group.IsSolvable (S.map (MulAut.conj τ).toMonoidHom) := by
    intro h
    apply hS
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective S (MulAut.conj τ).toMonoidHom
        (MulAut.conj τ).injective).toMonoidHom)
      (Subgroup.equivMapOfInjective S (MulAut.conj τ).toMonoidHom
        (MulAut.conj τ).injective).injective
  rcases classify_of_cycFive_mem hc hns with h | h | h | h | h | h <;> rw [h] <;> simp

theorem exists_mem_psl25_map_five : ∀ y : Fin 6, ∃ t ∈ psl25, t 5 = y := by
  intro y
  by_cases hy : y = 5
  · exact ⟨1, one_mem _, by simp [hy]⟩
  · obtain ⟨i, hi⟩ := exists_pow_cycFive 0 y (by decide) hy
    have hcpsl : cycFive ∈ psl25 :=
      Subgroup.mem_inf.mpr ⟨cycFive_mem_pgl25, mem_alternatingGroup.mpr sign_cycFive⟩
    have hipsl : invZeroInf ∈ psl25 := Subgroup.mem_inf.mpr
      ⟨invZeroInf_mem_pgl25, mem_alternatingGroup.mpr (by decide +kernel)⟩
    refine ⟨cycFive ^ (i : ℕ) * invZeroInf, psl25.mul_mem (psl25.pow_mem hcpsl _) hipsl, ?_⟩
    have h0 : invZeroInf 5 = 0 := by decide +kernel
    simp [Perm.mul_apply, h0, hi]

theorem isPretransitive_psl25 : MulAction.IsPretransitive psl25 (Fin 6) :=
  isPretransitive_of_exists_map_five _ exists_mem_psl25_map_five

theorem exists_conj_range_mem_of_not_isSolvable {K : Type*} [Group K] (φ : K →* Perm (Fin 6))
    (hφ : Function.Injective φ) (hK : ¬ Group.IsSolvable K) :
    ∃ σ : Perm (Fin 6), φ.range.map (MulAut.conj σ).toMonoidHom ∈
      ({alternatingGroup (Fin 6), ⊤, s5p, a5p, pgl25, psl25} : Set (Subgroup (Perm (Fin 6)))) := by
  refine exists_conj_mem_of_not_isSolvable φ.range fun h => hK ?_
  exact Group.isSolvable_of_isSolvable_injective (f := (MonoidHom.ofInjective hφ).toMonoidHom)
    (MonoidHom.ofInjective hφ).injective

end S6Class

end SzPS8

end CFSG.Quasithin
