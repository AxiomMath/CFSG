module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualE9
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagResidualGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu

public section

namespace CFSG.RankThree.PartTwo.Sec4.ResidualGen

open CFSG.Blueprint CFSG.Sporadic.Mathieu

section Elements

abbrev la : NativeSporadic.M22 := m22a

abbrev lA : NativeSporadic.M22 := m22a⁻¹

abbrev lb : NativeSporadic.M22 := m22b

abbrev lB : NativeSporadic.M22 := m22b⁻¹

@[expose] def e1W : NativeSporadic.M22 :=
  [lb, lA, lb, lA, lB, lB, lA, lB, lA, lA, lB, lA, lB, lA, lB].prod

@[expose] def e1P : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 13] * List.formPerm [1, 16] * List.formPerm [2, 7] * List.formPerm [4, 20] *
    List.formPerm [5, 15] * List.formPerm [6, 21] * List.formPerm [8, 11] *
    List.formPerm [17, 18]

theorem e1P_eq : e1P = (e1W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def e1M : NativeSporadic.M22 := ⟨e1P, e1P_eq ▸ e1W.2⟩

@[expose] def e2W : NativeSporadic.M22 :=
  [la, lB, la, lB, la, lb, la, lb, lA, lb, lA, lb, lA, lB, lA, lB, lA, lB, lA, lb, la, lb, la,
   lb, la, lB].prod

@[expose] def e2P : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 16] * List.formPerm [1, 13] * List.formPerm [2, 18] * List.formPerm [4, 6] *
    List.formPerm [5, 11] * List.formPerm [7, 17] * List.formPerm [8, 15] *
    List.formPerm [20, 21]

theorem e2P_eq : e2P = (e2W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def e2M : NativeSporadic.M22 := ⟨e2P, e2P_eq ▸ e2W.2⟩

@[expose] def e3W : NativeSporadic.M22 :=
  [lB, lA, lB, lA, lb, lA, lb, lA, lb, la, lB, la, lb, lb, la, lB, la, lb, la, lb, lb, lA, lB,
   lB, lA, lB, lA, lB, lB, lA].prod

@[expose] def e3P : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 7] * List.formPerm [1, 18] * List.formPerm [2, 13] * List.formPerm [4, 15] *
    List.formPerm [5, 20] * List.formPerm [6, 8] * List.formPerm [11, 21] *
    List.formPerm [16, 17]

theorem e3P_eq : e3P = (e3W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def e3M : NativeSporadic.M22 := ⟨e3P, e3P_eq ▸ e3W.2⟩

@[expose] def e4W : NativeSporadic.M22 :=
  [la, lB, la, lb, la, lb, la, lb, la, lB, la, lb, lb, la, lb, la, lB, lA, lb, lA, lB, lB, lA,
   lB, lA, lb, la, lb, lb, la, lb, la, lb, lb, la].prod

@[expose] def e4P : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21] * List.formPerm [1, 4] * List.formPerm [2, 8] * List.formPerm [5, 17] *
    List.formPerm [6, 13] * List.formPerm [7, 11] * List.formPerm [15, 18] *
    List.formPerm [16, 20]

theorem e4P_eq : e4P = (e4W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def e4M : NativeSporadic.M22 := ⟨e4P, e4P_eq ▸ e4W.2⟩

@[expose] def A9W : NativeSporadic.M22 :=
  [lB, lB, lA, lB, lA, lB, la, lb, lb, la, lB, la, lB, lA, lB, lA, lB, lB, lA, lb, lA, lB, lA,
   lB, lA, lB, lA, lb, lA].prod

@[expose] def A9P : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 20, 2] * List.formPerm [3, 11, 9] * List.formPerm [4, 19, 6] *
    List.formPerm [7, 15, 18] * List.formPerm [8, 13, 10] * List.formPerm [14, 21, 17]

theorem A9P_eq : A9P = (A9W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def A9M : NativeSporadic.M22 := ⟨A9P, A9P_eq ▸ A9W.2⟩

@[expose] def F9W : NativeSporadic.M22 :=
  [lb, la, lB, la, lb, la, lb, lb, lA, lb, lA, lB, lB, lA, lB, lA, lB, lA, lB, lB, lB, lA, lb,
   lA].prod

@[expose] def F9P : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 15, 2, 7] * List.formPerm [3, 21, 11, 6] * List.formPerm [4, 17, 14, 19] *
    List.formPerm [5, 13, 16, 10] * List.formPerm [8, 12] * List.formPerm [18, 20]

theorem F9P_eq : F9P = (F9W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def F9M : NativeSporadic.M22 := ⟨F9P, F9P_eq ▸ F9W.2⟩

@[expose] def J9W : NativeSporadic.M22 :=
  [la, lb, lb, lb, la, lb, la, lb, lb, lA, lB, lA, lB, lA, lB, lA, lB, lA, lB, lA, lB, lA, lb,
   lA, lB, lB, lA, lB, lA, lb, lA, lb, lA].prod

@[expose] def J9P : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 8, 20, 10] * List.formPerm [2, 13] * List.formPerm [4, 6, 17, 14] *
    List.formPerm [5, 15, 16, 18] * List.formPerm [7, 12] * List.formPerm [9, 19, 11, 21]

theorem J9P_eq : J9P = (J9W : Equiv.Perm (Fin 22)) := by decide +kernel

@[expose] def J9M : NativeSporadic.M22 := ⟨J9P, J9P_eq ▸ J9W.2⟩

end Elements

section E9

@[expose] def B9M : NativeSporadic.M22 := F9M * A9M * F9M⁻¹

theorem A9M_pow_three : A9M ^ 3 = 1 := by decide +kernel

theorem B9M_pow_three : B9M ^ 3 = 1 := by decide +kernel

theorem A9M_comm_B9M : A9M * B9M = B9M * A9M := by decide +kernel

theorem A9M_ne_one : A9M ≠ 1 := by decide +kernel

theorem B9M_ne : B9M ≠ 1 ∧ B9M ≠ A9M ∧ B9M ≠ A9M ^ 2 := by decide +kernel

theorem B9M_not_mem_zpowers : B9M ∉ Subgroup.zpowers A9M := fun h => by
  rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers A9M_pow_three h with h1 | h1 | h1
  · exact B9M_ne.1 h1
  · exact B9M_ne.2.1 h1
  · exact B9M_ne.2.2 h1

theorem F9M_conj_A9M : F9M * A9M * F9M⁻¹ = B9M := rfl

theorem F9M_conj_B9M : F9M * B9M * F9M⁻¹ = A9M⁻¹ := by decide +kernel

theorem F9M_pow_four : F9M ^ 4 = 1 := by decide +kernel

theorem J9M_conj_A9M : J9M * A9M * J9M⁻¹ = B9M * A9M⁻¹ := by decide +kernel

theorem J9M_conj_B9M : J9M * B9M * J9M⁻¹ = A9M⁻¹ * B9M * A9M⁻¹ := by decide +kernel

theorem exists_e9_M22 :
    ∃ E : Subgroup NativeSporadic.M22, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 ∧
      (∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer (E : Set NativeSporadic.M22), n * x * n⁻¹ = y) ∧
      ∃ s : NativeSporadic.M22, s * s = 1 ∧ ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ :=
  exists_e9_data A9M_pow_three B9M_pow_three A9M_comm_B9M A9M_ne_one B9M_not_mem_zpowers
    F9M_conj_A9M F9M_conj_B9M F9M_pow_four J9M_conj_A9M J9M_conj_B9M

end E9

section E16

theorem mem_finset_of_mem_closure {G : Type*} [Group G] {gens : Set G} {S : Finset G}
    (hgens : ∀ g ∈ gens, g ∈ S) (h1 : (1 : G) ∈ S) (hmul : ∀ s ∈ S, ∀ t ∈ S, s * t ∈ S)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) {x : G} (hx : x ∈ Subgroup.closure gens) : x ∈ S :=
  Subgroup.closure_induction (p := fun x _ => x ∈ S) (fun g hg => hgens g hg) h1
    (fun x y _ _ hx hy => hmul x hx y hy) (fun x _ hx => hinv x hx) hx

@[expose] def e16List : List NativeSporadic.M22 :=
  [1, e1M, e2M, e1M * e2M, e3M, e1M * e3M, e2M * e3M, e1M * e2M * e3M, e4M, e1M * e4M, e2M * e4M,
    e1M * e2M * e4M, e3M * e4M, e1M * e3M * e4M, e2M * e3M * e4M, e1M * e2M * e3M * e4M]

@[expose] def e16Set : Finset NativeSporadic.M22 := e16List.toFinset

theorem e16Set_card : e16Set.card = 16 := by decide +kernel

theorem e16Set_mul : ∀ s ∈ e16Set, ∀ t ∈ e16Set, s * t ∈ e16Set := by decide +kernel

theorem e16Set_inv : ∀ s ∈ e16Set, s⁻¹ ∈ e16Set := by decide +kernel

theorem e16Set_comm : ∀ s ∈ e16Set, ∀ t ∈ e16Set, s * t = t * s := by decide +kernel

theorem e16Set_sq : ∀ s ∈ e16Set, s ^ 2 = 1 := by decide +kernel

theorem exists_e16_M22 :
    ∃ E : Subgroup NativeSporadic.M22, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  set E : Subgroup NativeSporadic.M22 := Subgroup.closure {e1M, e2M, e3M, e4M} with hE
  have h1 : e1M ∈ E := Subgroup.subset_closure (by simp)
  have h2 : e2M ∈ E := Subgroup.subset_closure (by simp)
  have h3 : e3M ∈ E := Subgroup.subset_closure (by simp)
  have h4 : e4M ∈ E := Subgroup.subset_closure (by simp)
  have hgens : ∀ g ∈ ({e1M, e2M, e3M, e4M} : Set NativeSporadic.M22), g ∈ e16Set := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [e16Set, e16List]
  have hin : ∀ x ∈ E, x ∈ e16Set := fun x hx =>
    mem_finset_of_mem_closure hgens (by simp [e16Set, e16List]) e16Set_mul e16Set_inv hx
  have hS : ∀ s ∈ e16Set, s ∈ E := by
    intro s hs
    simp only [e16Set, e16List, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
      at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact E.one_mem
    · exact h1
    · exact h2
    · exact E.mul_mem h1 h2
    · exact h3
    · exact E.mul_mem h1 h3
    · exact E.mul_mem h2 h3
    · exact E.mul_mem (E.mul_mem h1 h2) h3
    · exact h4
    · exact E.mul_mem h1 h4
    · exact E.mul_mem h2 h4
    · exact E.mul_mem (E.mul_mem h1 h2) h4
    · exact E.mul_mem h3 h4
    · exact E.mul_mem (E.mul_mem h1 h3) h4
    · exact E.mul_mem (E.mul_mem h2 h3) h4
    · exact E.mul_mem (E.mul_mem (E.mul_mem h1 h2) h3) h4
  refine ⟨E, fun x hx y hy => e16Set_comm x (hin x hx) y (hin y hy),
    fun x hx => e16Set_sq x (hin x hx), ?_⟩
  have hcard : Nat.card E = e16Set.card := by
    have e : ↥E ≃ ↥e16Set := Equiv.subtypeEquivRight fun x => ⟨hin x, hS x⟩
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard, e16Set_card]

end E16

theorem residualData_M22 : ResidualData NativeSporadic.M22 :=
  ⟨(fam_m22_simplicity).2.2, ⟨m22a, m22b, by decide +kernel⟩, by
    rw [CFSG.RankThree.PartTwo.Sec4.Census.card_m22_eq]; norm_num, exists_e16_M22,
    exists_e9_M22⟩

end CFSG.RankThree.PartTwo.Sec4.ResidualGen
