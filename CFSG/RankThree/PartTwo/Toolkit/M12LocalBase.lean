
module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups

@[expose] public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open CFSG.RankThree.PartTwo.Toolkit (toP3 toP4)
open scoped commutatorElement

structure Enum (H : Subgroup G12) where
  pred : List ℕ → Bool
  mem_iff : ∀ g : G12, g ∈ H ↔ pred (tbl g.1) = true
  L : List Idx
  complete : ∀ k ∈ allIdx, pred (prodT k) = true → k ∈ L
  sound : ∀ k ∈ L, pred (prodT k) = true
  nodup : (L.map prodT).Nodup

namespace Enum

variable {H : Subgroup G12} (E : Enum H)

theorem exists_idx
    {g : G12} (hg : g ∈ H) : ∃ k ∈ E.L, g.1 = prodP k := by
  obtain ⟨k, hk, hgk⟩ := exists_eq_prodP g.2
  refine ⟨k, E.complete k hk ?_, hgk⟩
  rw [← tbl_prodP, ← hgk]
  exact (E.mem_iff g).1 hg

theorem mem_of_idx {k : Idx} (hk : k ∈ E.L) : (⟨prodP k, prodP_mem k⟩ : G12) ∈ H := by
  rw [E.mem_iff]
  change E.pred (tbl (prodP k)) = true
  rw [tbl_prodP]
  exact E.sound k hk

theorem forall_tbl {Q : List ℕ → Prop} (hQ : ∀ k ∈ E.L, Q (prodT k))
    {g : G12} (hg : g ∈ H) :
    Q (tbl g.1) := by
  obtain ⟨k, hk, hgk⟩ := E.exists_idx hg
  rw [hgk, tbl_prodP]
  exact hQ k hk

theorem card : Nat.card H = E.L.length := by
  classical
  have hnd : E.L.Nodup := E.nodup.of_map _
  let φ : {k // k ∈ E.L} → H := fun k => ⟨⟨prodP k.1, prodP_mem k.1⟩, E.mem_of_idx k.2⟩
  have hinj : Function.Injective φ := by
    intro k k' h
    have h1 : prodP k.1 = prodP k'.1 := congrArg (fun g : H => (g : G12).1) h
    have h2 : prodT k.1 = prodT k'.1 := by rw [← tbl_prodP, ← tbl_prodP, h1]
    exact Subtype.ext (List.inj_on_of_nodup_map E.nodup k.2 k'.2 h2)
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨k, hk, hgk⟩ := E.exists_idx g.2
    exact ⟨⟨k, hk⟩, Subtype.ext (Subtype.ext hgk.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩),
    ← Nat.card_congr (List.Nodup.getEquiv _ hnd), Nat.card_eq_fintype_card, Fintype.card_fin]

end Enum

@[expose] def wG0 : List Int :=
  [-2, 1, -2, 1, 2, 1, 2]

@[expose] def wER : List Int :=
  [2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1]

@[expose] def wES : List Int :=
  [-2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2]

@[expose] def wEW : List Int :=
  [1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1]

@[expose] def wFR : List Int :=
  [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1]

@[expose] def wFS : List Int :=
  [-2, 1, -2, 1, 2, 1, 2]

@[expose] def wFW : List Int :=
  [1, -2, 1, 2, 1, -2, 1, 2, 1]

@[expose] def wU : List Int :=
  [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def wS : List Int :=
  [1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def wC1 : List Int :=
  [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def wC2 : List Int :=
  [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2]

@[expose] def a'T : List ℕ := tmul xT (tmul yT yT)

theorem tbl_a' : tbl (x * y ^ 2).1 = a'T := by
  rw [tblG_mul, tblG_pow, tbl_x, tbl_y]
  rfl

theorem card_P0 : Nat.card P0 = 27 := ex27_card x_cube y_cube z_comm_x z_comm_y z_ne_one

theorem basisE_a : basisE.a = ⁅x, y⁆ := rfl

theorem basisE_b : basisE.b = x := rfl

theorem basisF_b : basisF.b = y := rfl

theorem basisA_b : basisA.b = x * y := rfl

theorem basisA'_b : basisA'.b = x * y ^ 2 := rfl

theorem mem_nf3T {u v w t : List ℕ} :
    t ∈ nf3T u v w ↔
      ∃ i < 3, ∃ j < 3, ∃ k < 3, t = tmul (tmul (tpow u i) (tpow v j)) (tpow w k) := by
  simp only [nf3T, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    exact ⟨i, hi, j, hj, k, hk, rfl⟩
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    exact ⟨i, hi, j, hj, k, hk, rfl⟩

theorem mem_nf2T {u v t : List ℕ} :
    t ∈ nf2T u v ↔ ∃ i < 3, ∃ j < 3, t = tmul (tpow u i) (tpow v j) := by
  simp only [nf2T, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩

theorem mem_P0_iff (g : G12) : g ∈ P0 ↔ tbl g.1 ∈ nf3T xT yT zT := by
  rw [mem_nf3T]
  constructor
  · intro hg
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by norm_num) x_cube y_cube z_comm_x
        z_comm_y hg
    exact ⟨i, hi, j, hj, k, hk, by rw [tblG_mul, tblG_mul, tblG_pow, tblG_pow, tblG_pow, tbl_x,
      tbl_y, tbl_z]⟩
  · rintro ⟨i, -, j, -, k, -, h⟩
    have : g = x ^ i * y ^ j * ⁅x, y⁆ ^ k := by
      rw [eq_iff_tbl, h, tblG_mul, tblG_mul, tblG_pow, tblG_pow, tblG_pow, tbl_x, tbl_y, tbl_z]
    rw [this]
    have hxP : x ∈ P0 := subset_closure (by simp)
    have hyP : y ∈ P0 := subset_closure (by simp)
    have hzP : ⁅x, y⁆ ∈ P0 := by
      rw [commutatorElement_def]
      exact P0.mul_mem (P0.mul_mem (P0.mul_mem hxP hyP) (P0.inv_mem hxP)) (P0.inv_mem hyP)
    exact P0.mul_mem (P0.mul_mem (P0.pow_mem hxP _) (P0.pow_mem hyP _)) (P0.pow_mem hzP _)

theorem mem_sub_iff (B : E9Basis G12) {uT vT : List ℕ} (hu : tbl B.a.1 = uT)
    (hv : tbl B.b.1 = vT) (g : G12) : g ∈ B.sub ↔ tbl g.1 ∈ nf2T uT vT := by
  rw [mem_nf2T]
  constructor
  · intro hg
    obtain ⟨i, j, hi, hj, rfl⟩ := B.exists_pow_mul_pow hg
    exact ⟨i, hi, j, hj, by rw [tblG_mul, tblG_pow, tblG_pow, hu, hv]⟩
  · rintro ⟨i, -, j, -, h⟩
    have : g = B.a ^ i * B.b ^ j := by rw [eq_iff_tbl, h, tblG_mul, tblG_pow, tblG_pow, hu, hv]
    rw [this]
    exact B.sub.mul_mem (B.sub.pow_mem (subset_closure (by simp)) _)
      (B.sub.pow_mem (subset_closure (by simp)) _)

theorem mem_A_iff (g : G12) : g ∈ basisA.sub ↔ tbl g.1 ∈ AT := mem_sub_iff basisA tbl_z tbl_a g

theorem mem_normalizer_pair_iff {u v : G12} {uT vT : List ℕ} {ST : List (List ℕ)}
    (hu : tbl u.1 = uT) (hv : tbl v.1 = vT) (hST : ∀ c : G12, c ∈ closure {u, v} ↔ tbl c.1 ∈ ST)
    (g : G12) : g ∈ normalizer ((closure {u, v} : Subgroup G12) : Set G12) ↔
      ([uT, vT].all fun s => ST.contains (tconj (tbl g.1) s)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.contains_iff_mem]
  rw [← hu, ← hv, ← tblG_conj, ← tblG_conj, ← hST, ← hST]
  constructor
  · intro hg
    exact ⟨(mem_normalizer_iff.1 hg u).1 (subset_closure (by simp)),
      (mem_normalizer_iff.1 hg v).1 (subset_closure (by simp))⟩
  · rintro ⟨h1, h2⟩
    refine mem_normalizer_closure_of_conj_mem ?_
    rintro s (rfl | rfl)
    · exact h1
    · exact h2

theorem mem_centralizer_pair_iff {u v : G12} {uT vT : List ℕ} (hu : tbl u.1 = uT)
    (hv : tbl v.1 = vT) (g : G12) : g ∈ centralizer ((closure {u, v} : Subgroup G12) : Set G12) ↔
      ([uT, vT].all fun s => tmul (tbl g.1) s == tmul s (tbl g.1)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  rw [← hu, ← hv, ← tblG_mul, ← tblG_mul, ← tblG_mul, ← tblG_mul, ← eq_iff_tbl, ← eq_iff_tbl]
  constructor
  · intro hg
    rw [mem_centralizer_iff] at hg
    exact ⟨(hg u (subset_closure (by simp))).symm, (hg v (subset_closure (by simp))).symm⟩
  · rintro ⟨h1, h2⟩
    rw [mem_centralizer_iff]
    intro h hh
    have hle : closure ({u, v} : Set G12) ≤ centralizer {g} := by
      rw [closure_le]
      rintro s (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 h1.symm
      · exact mem_centralizer_singleton_iff.2 h2.symm
    exact mem_centralizer_singleton_iff.1 (hle hh)

theorem mem_normalizer_zpowers_iff {u : G12} {uT : List ℕ} (hu : tbl u.1 = uT) (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (g : G12) : g ∈ normalizer ((zpowers u : Subgroup G12) : Set G12) ↔
      (tconj (tbl g.1) uT == uT || tconj (tbl g.1) uT == tpow uT 2) = true := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  simp only [Bool.or_eq_true, beq_iff_eq]
  rw [← hu, ← tblG_conj, ← tblG_pow, ← eq_iff_tbl, ← eq_iff_tbl]
  constructor
  · intro hg
    have hmem := (mem_normalizer_iff.1 hg u).1 (mem_zpowers u)
    have hfin : IsOfFinOrder u := orderOf_pos_iff.1 (by rw [hord]; norm_num)
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 (hfin.mem_zpowers_iff_mem_range_orderOf.1 hmem)
    rw [Finset.mem_range, hord] at hk
    interval_cases k
    · exfalso
      rw [pow_zero] at hk'
      apply hu1
      have : g * u * g⁻¹ = g * 1 * g⁻¹ := by rw [mul_one, mul_inv_cancel]; exact hk'.symm
      exact mul_right_cancel (mul_left_cancel this)
    · left; rw [← hk', pow_one]
    · right; exact hk'.symm
  · intro h
    rw [zpowers_eq_closure]
    refine mem_normalizer_closure_of_conj_mem ?_
    intro s hs
    rw [Set.mem_singleton_iff.1 hs]
    rcases h with h | h
    · rw [h]; exact subset_closure rfl
    · rw [h]; exact (closure {u}).pow_mem (subset_closure rfl) 2

end CFSG.RankThree.PartTwo.Toolkit.M12
