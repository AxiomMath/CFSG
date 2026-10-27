module

public import CFSG.Sporadic.Recognition.ThMultiplierV
public import CFSG.Sporadic.Recognition.ThMultiplierConfig3
public import CFSG.Sporadic.Th.Max3.AllConjFinal

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.LocalAnalysis.DempwolffFive
open scoped commutatorElement

@[expose] def matA1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 1; 0, 1, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1]

@[expose] def matA1inv : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 1, 0; 0, 1, 1, 1, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 1, 0]

@[expose] def matA2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 1, 0; 0, 1, 1, 0, 1]

@[expose] def matA2inv : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 1, 0; 0, 1, 1, 0, 1]

@[expose] def matA3 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 1, 1, 0; 1, 1, 1, 1, 1; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 1, 0, 1]

@[expose] def matA3inv : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 1, 1; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 1, 0, 1, 1, 0; 0, 0, 1, 1, 1]

theorem colA1_lt : ∀ j i, colA1 j i < 2 := by decide

theorem colA2_lt : ∀ j i, colA2 j i < 2 := by decide

theorem colA3_lt : ∀ j i, colA3 j i < 2 := by decide

theorem matA1_apply : ∀ i j, matA1 i j = (colA1 j i : ZMod 2) := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matA2_apply : ∀ i j, matA2 i j = (colA2 j i : ZMod 2) := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matA3_apply : ∀ i j, matA3 i j = (colA3 j i : ZMod 2) := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def gA1 : G := ⟨matA1, matA1inv, by decide, by decide⟩

@[expose] def gA2 : G := ⟨matA2, matA2inv, by decide, by decide⟩

@[expose] def gA3 : G := ⟨matA3, matA3inv, by decide, by decide⟩

@[expose] def atomG : Fin 3 → G := ![gA1, gA2, gA3]

@[expose] def wordTable : Fin 5 → Fin 5 → List (Fin 3 × Bool) :=
  ![![[], [(2, true), (0, false), (0, false), (0, false), (2, false)],
    [(1, false), (2, true), (0, false), (0, false), (0, false), (2, false), (1, false)],
    [(2, true), (2, true), (0, false), (1, false), (0, true), (2, false), (2, false)],
    [(0, true), (2, true), (2, true), (0, false), (1, false), (0, true), (2, false), (2, false),
      (0, false)]],
  ![[(0, false), (0, false), (2, true), (0, false), (1, false), (0, true), (2, false),
      (0, false)], [], [(0, false), (0, false), (0, false)],
    [(2, false), (2, false), (0, false), (2, true), (1, false), (2, false), (0, true),
      (2, true), (2, true)],
    [(2, true), (1, false), (0, false), (1, false), (0, true), (1, false), (2, false)]],
  ![[(2, false), (0, false), (0, false), (2, true), (2, true), (1, false), (2, false),
      (2, false), (0, true), (0, true), (2, true)],
    [(0, false), (1, false), (2, false), (1, false), (2, true), (1, false), (0, true)], [],
    [(2, false), (2, false), (0, true), (2, true), (1, false), (2, false), (0, false),
      (2, true), (2, true)], [(0, true), (2, false), (1, false), (2, true), (0, false)]],
  ![[(0, false), (2, false), (0, false), (2, false), (1, false), (2, true), (0, true),
      (2, true), (0, true)],
    [(1, false), (2, false), (1, false), (0, false), (0, false), (0, false), (1, false),
      (2, true), (1, false)],
    [(2, false), (1, false), (0, false), (0, false), (0, false), (1, false), (2, true)], [],
    [(0, false), (1, false), (0, false), (2, false), (1, false), (2, true), (0, true),
      (1, false), (0, true)]],
  ![[(2, false), (2, false), (0, false), (2, true), (1, false), (2, false), (1, false),
      (0, false), (2, false), (1, false), (0, true), (1, false)],
    [(2, true), (2, true), (0, true), (2, true), (2, true), (1, false), (2, false), (2, false),
      (0, false), (2, false), (2, false)],
    [(0, false), (2, false), (1, false), (0, false), (0, false), (0, false), (1, false),
      (2, true), (0, false), (0, false)],
    [(2, false), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false),
      (0, true), (2, true)], []]]

theorem xg_eq_word : ∀ i j : Fin 5, i ≠ j →
    xg (i, j, 1) =
      ((wordTable i j).map fun l => if l.2 then (atomG l.1)⁻¹ else atomG l.1).prod := by
  decide

theorem iotaN_col (col : Fin 5 → Fin 5 → ℕ)
    (hcol : ∀ j i, col j i < 2) (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hM : ∀ i j, M i j = (col j i : ZMod 2)) (j : Fin 5) :
    iotaN (col j) = iotaG vGen (fun i => M i j) := by
  have h2 : ∀ i, (M i j).val = col j i := fun i => by
    rw [hM, ZMod.val_natCast, Nat.mod_eq_of_lt (hcol j i)]
  show (List.ofFn fun i => vGen i ^ col j i).prod =
    (List.ofFn fun i => vGen i ^ (M i j).val).prod
  simp only [h2]

theorem vGen_mem_Q (j : Fin 5) : vGen j ∈ Q :=
  Q.mul_mem (Subgroup.pow_mem _ z_mem_Q _) (Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact Subgroup.pow_mem _ (q_mem_Q i) _)

theorem A1_conj'
    (j : Fin 5) :
    A1 * vGen j * A1⁻¹ = iotaG vGen (fun i => matA1 i j) := by
  rw [mul_inv_eq_iff_eq_mul, A1_vGen, iotaN_col colA1 colA1_lt matA1 matA1_apply j]

theorem A2_conj'
    (j : Fin 5) :
    A2 * vGen j * A2⁻¹ = iotaG vGen (fun i => matA2 i j) := by
  rw [mul_inv_eq_iff_eq_mul, A2_vGen, iotaN_col colA2 colA2_lt matA2 matA2_apply j]

theorem A3_conj'
    (j : Fin 5) :
    A3 * vGen j * A3⁻¹ = iotaG vGen (fun i => matA3 i j) := by
  rw [mul_inv_eq_iff_eq_mul, A3_vGen, iotaN_col colA3 colA3_lt matA3 matA3_apply j]

section Instance


noncomputable def thConfig : Config J where
  v := vGen
  v_sq := fun j => vGen_mul_self j
  v_comm := fun i j => vGen_comm i j
  v_indep := fun c hc => iotaN_ne_one hc
  a := ![A1, A2, A3]
  atom := atomG
  a_conj := fun k j => by
    fin_cases k
    · exact A1_conj' j
    · exact A2_conj' j
    · exact A3_conj' j
  word := wordTable
  word_spec := xg_eq_word
  Q := Q
  M := M
  Q_le_M := Q_le_M
  v_mem_Q := fun j => vGen_mem_Q j
  M_conj_Q := fun m hm q hq => (Subgroup.mem_normalizer_iff.1 (M_le_normalizer_Q hm) q).1 hq
  Q_comm := fun q hq g hg => by
    rw [vGen_zero]
    exact (mem_Q_iff_comm_mem_zpowers (Q_le_M hq)).1 hq g hg
  card_Q := card_Q
  cent_M := fun g hg => by
    have h : g ∈ Subgroup.centralizer ({a} : Set J) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      rw [vGen_zero, z_eq_a] at hg
      exact hg.symm
    rwa [Kernel.centralizer_a_eq_M th_kernel_facts] at h
  cent_Q := fun g hgM hg => by
    rw [vGen_zero, ← centralizer_Q_inf_M]
    exact ⟨Subgroup.mem_centralizer_iff.2 fun q hq => hg q hq, hgM⟩

theorem exists_odd_perfect_noCover :
    ∃ H : Subgroup J, Odd H.index ∧ Group.IsPerfect H ∧
      CFSG.Monster.Schur.NoPerfectDoubleCover H :=
  thConfig.exists_subgroup natCard_J

end Instance

end CFSG.Sporadic.Recognition.ThMultiplier
