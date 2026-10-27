module

public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.RankThree.Asc83Table.PermWords
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.RankThree.Asc83Table.M23

open CFSG.Blueprint Subgroup

abbrev gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq : NativeSporadic.M23 = closure {gA, gB} := rfl

theorem card_M23 : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

abbrev gens : List (Equiv.Perm (Fin 23)) := [gA, gB]

theorem gens_mem : ∀ g ∈ gens, g ∈ NativeSporadic.M23 := by
  intro g hg
  rw [m23_eq]
  simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

abbrev x : Equiv.Perm (Fin 23) :=
  List.formPerm [3, 4, 16] * List.formPerm [5, 14, 17] * List.formPerm [6, 7, 13] *
    List.formPerm [8, 11, 20] * List.formPerm [9, 21, 22] * List.formPerm [12, 18, 19]

abbrev y : Equiv.Perm (Fin 23) :=
  List.formPerm [2, 15, 10] * List.formPerm [3, 9, 5] * List.formPerm [4, 21, 14] *
    List.formPerm [6, 13, 7] * List.formPerm [8, 11, 20] * List.formPerm [16, 22, 17]

abbrev gR : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 12, 8, 13, 10, 19, 20, 6] *
    List.formPerm [4, 9, 14, 17, 16, 5, 22, 21] * List.formPerm [7, 15, 18, 11]

abbrev gS : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 20] * List.formPerm [4, 14] * List.formPerm [5, 9] *
    List.formPerm [6, 13] * List.formPerm [8, 10] * List.formPerm [11, 15] * List.formPerm [16, 22]

theorem x_eq : x = permWord gens [(0, -1), (1, 2), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, -1), (1, -2), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -2), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -3), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1)] := by
  decide +kernel

theorem x_mem : x ∈ NativeSporadic.M23 := x_eq ▸ permWord_mem gens_mem _

abbrev y_c0 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 16, 4, 10, 2, 20, 6, 21, 5, 13, 3, 9, 12, 1, 17, 11, 8, 7, 22, 19, 18, 14]

theorem y_c0_eq : y_c0 = permWord gens [(1, 1), (0, 1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, 1), (0, -1), (1, -1), (0, -2), (1, -2), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -2),
    (1, -2), (0, -1), (1, -2), (0, -1), (1, -1), (0, -1), (1, -2), (0, -1), (1, -2),
    (0, -1), (1, 1)] := by
  decide +kernel

theorem y_c0_mem : y_c0 ∈ NativeSporadic.M23 := y_c0_eq ▸ permWord_mem gens_mem _

abbrev y_c1 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 14, 16, 7, 20, 11, 2] * List.formPerm [1, 12, 9, 21, 18, 19, 22] *
    List.formPerm [4, 6, 5, 13, 8, 17, 15]

theorem y_c1_eq : y_c1 = permWord gens [(0, -2), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -2), (0, -1), (1, 1), (0, -1),
    (1, 1)] := by
  decide +kernel

theorem y_c1_mem : y_c1 ∈ NativeSporadic.M23 := y_c1_eq ▸ permWord_mem gens_mem _

theorem y_eq : y = y_c0 * y_c1 := by
  decide +kernel

theorem y_mem : y ∈ NativeSporadic.M23 := by
  rw [y_eq]
  refine mul_mem ?_ ?_
  · exact y_c0_mem
  · exact y_c1_mem

abbrev gR_c0 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 2, 19, 6, 3, 20, 4, 5, 12, 11, 21, 7, 13, 18] * List.formPerm [1, 10] *
    List.formPerm [8, 15, 14, 9, 16, 22, 17]

theorem gR_c0_eq : gR_c0 = permWord gens [(1, -1), (0, 1), (1, 2), (0, 1), (1, -1), (0, 1),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 2),
    (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1),
    (1, 1), (0, 1), (1, -1), (0, 1), (1, 2)] := by
  decide +kernel

theorem gR_c0_mem : gR_c0 ∈ NativeSporadic.M23 := gR_c0_eq ▸ permWord_mem gens_mem _

abbrev gR_c1 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 10, 2, 5, 16, 4, 14, 22, 11, 21, 20, 19, 3, 6] *
    List.formPerm [1, 18, 12, 17, 9, 15, 13] * List.formPerm [7, 8]

theorem gR_c1_eq : gR_c1 = permWord gens [(0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1),
    (0, -1), (1, 1), (0, -1), (1, -2), (0, -1), (1, -1)] := by
  decide +kernel

theorem gR_c1_mem : gR_c1 ∈ NativeSporadic.M23 := gR_c1_eq ▸ permWord_mem gens_mem _

theorem gR_eq : gR = gR_c0 * gR_c1 := by
  decide +kernel

theorem gR_mem : gR ∈ NativeSporadic.M23 := by
  rw [gR_eq]
  refine mul_mem ?_ ?_
  · exact gR_c0_mem
  · exact gR_c1_mem

abbrev gS_c0 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 16, 1, 2, 11, 9] * List.formPerm [3, 7] * List.formPerm [4, 8, 20, 5, 6, 14] *
    List.formPerm [10, 22, 13] * List.formPerm [12, 18] * List.formPerm [17, 19, 21]

theorem gS_c0_eq : gS_c0 = permWord gens [(1, 1), (0, 1), (1, 2), (0, 1), (1, -1), (0, -1),
    (1, -2), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1), (1, -2), (0, -1), (1, 1), (0, -1),
    (1, -1), (0, -1), (1, -2), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -1), (0, -1),
    (1, -1), (0, -1), (1, -1), (0, -1), (1, 1), (0, -1), (1, -1), (0, -1), (1, -2), (0, -1),
    (1, -2), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1),
    (1, 1), (0, 1)] := by
  decide +kernel

theorem gS_c0_mem : gS_c0 ∈ NativeSporadic.M23 := gS_c0_eq ▸ permWord_mem gens_mem _

abbrev gS_c1 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 16, 10, 4, 6, 22] * List.formPerm [1, 9, 20] *
    List.formPerm [2, 8, 13, 5, 11, 15] * List.formPerm [3, 7] * List.formPerm [12, 18] *
    List.formPerm [17, 21, 19]

theorem gS_c1_eq : gS_c1 = permWord gens [(1, 1), (0, 1), (1, 1)] := by
  decide +kernel

theorem gS_c1_mem : gS_c1 ∈ NativeSporadic.M23 := gS_c1_eq ▸ permWord_mem gens_mem _

theorem gS_eq : gS = gS_c0 * gS_c1 := by
  decide +kernel

theorem gS_mem : gS ∈ NativeSporadic.M23 := by
  rw [gS_eq]
  refine mul_mem ?_ ?_
  · exact gS_c0_mem
  · exact gS_c1_mem
abbrev X : NativeSporadic.M23 := ⟨x, x_mem⟩

abbrev Y : NativeSporadic.M23 := ⟨y, y_mem⟩

abbrev GR : NativeSporadic.M23 := ⟨gR, gR_mem⟩

abbrev GS : NativeSporadic.M23 := ⟨gS, gS_mem⟩

theorem X_cube : X ^ 3 = 1 := Subtype.ext (show x ^ 3 = 1 by decide +kernel)

theorem Y_cube : Y ^ 3 = 1 := Subtype.ext (show y ^ 3 = 1 by decide +kernel)

theorem XY_comm : Commute X Y := Subtype.ext (show x * y = y * x by decide +kernel)

theorem X_ne : X ≠ 1 := fun h => absurd (congrArg Subtype.val h) (show x ≠ 1 by decide +kernel)

theorem Y_ne : Y ≠ 1 := fun h => absurd (congrArg Subtype.val h) (show y ≠ 1 by decide +kernel)

theorem Y_ne_X : Y ≠ X := fun h => absurd (congrArg Subtype.val h) (show y ≠ x by decide +kernel)

theorem Y_ne_X2 : Y ≠ X ^ 2 := fun h =>
  absurd (congrArg Subtype.val h) (show y ≠ x ^ 2 by decide +kernel)

@[expose] noncomputable def E : E9Basis NativeSporadic.M23 :=
  E9Basis.ofNe X_cube Y_cube XY_comm X_ne Y_ne Y_ne_X Y_ne_X2

theorem GR_X : GR * X * GR⁻¹ = X ^ 0 * Y ^ 1 :=
  Subtype.ext (show gR * x * gR⁻¹ = x ^ 0 * y ^ 1 by decide +kernel)

theorem GR_Y : GR * Y * GR⁻¹ = X ^ 1 * Y ^ 2 :=
  Subtype.ext (show gR * y * gR⁻¹ = x ^ 1 * y ^ 2 by decide +kernel)

theorem GS_X : GS * X * GS⁻¹ = X ^ 1 * Y ^ 2 :=
  Subtype.ext (show gS * x * gS⁻¹ = x ^ 1 * y ^ 2 by decide +kernel)

theorem GS_Y : GS * Y * GS⁻¹ = X ^ 0 * Y ^ 2 :=
  Subtype.ext (show gS * y * gS⁻¹ = x ^ 0 * y ^ 2 by decide +kernel)

@[expose] def sdR : GL23 := gl23 !![0, 1; 1, 2] !![1, 1; 1, 0] (by decide) (by decide)

@[expose] def sdS : GL23 := gl23 !![1, 0; 2, 2] !![1, 0; 2, 2] (by decide) (by decide)

theorem sdR_mem : sdR ∈ E.rhoE.range := E.mem_range_of_conj 0 1 1 2 GR_X GR_Y (by decide)

theorem sdS_mem : sdS ∈ E.rhoE.range := E.mem_range_of_conj 1 0 2 2 GS_X GS_Y (by decide)

theorem sdR_pow : sdR ^ 8 = 1 := by decide +kernel

theorem sdS_pow : sdS ^ 2 = 1 := by decide +kernel

theorem sd_conj : sdS * sdR * sdS⁻¹ = sdR ^ 3 := by decide +kernel

theorem sd_ne : ∀ i : Fin 8, ∀ e : Fin 2, sdR ^ (i : ℕ) * sdS ^ (e : ℕ) = 1 → i = 0 ∧ e = 0 := by
  decide +kernel

theorem not_dvd_card : ¬ 27 ∣ Nat.card NativeSporadic.M23 := by
  rw [card_M23]
  decide

theorem automizer_P0 : Nonempty (Automizer E.sub ≃* CFSG.Open.SemidihedralGroup 4) :=
  E.nonempty_semidihedral (E.three_not_dvd not_dvd_card) sdR_mem sdS_mem sdR_pow sdS_pow sd_conj
    sd_ne

theorem factorization_card : (Nat.card NativeSporadic.M23).factorization 3 = 2 := by
  rw [card_M23]
  exact factorization_eq_of_eq Nat.prime_three (show 10200960 = 3 ^ 2 * 1133440 by norm_num)
    (by norm_num)

theorem table {L : Type} [Group L] (hL : NativeSporadic.IsSporadic L .M23) :
    (∀ P : Sylow 3 L, IsElementaryAbelian 3 (P : Subgroup L) ∧ Nat.card P = 9) ∧
      CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, IsElementaryAbelian 3 B → Nat.card B = 9 →
        ActsNontriviallyOnTwoSubgroup B →
          Nonempty (Automizer B ≃* CFSG.Open.SemidihedralGroup 4) := by
  obtain ⟨e⟩ := hL
  obtain ⟨h₁, h₂, h₃⟩ := e9_transport E factorization_card (e : L ≃* NativeSporadic.M23)
  obtain ⟨q⟩ := automizer_P0
  exact ⟨h₁, h₂, fun B _ hB _ => (h₃ B hB).map fun f => f.trans q⟩

end CFSG.RankThree.Asc83Table.M23
