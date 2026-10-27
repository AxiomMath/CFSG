module

public import CFSG.Quasithin.Vol2.Ch10SecKRSa
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.Quasithin.Vol2.Ch10SecQ9H4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag C10P4F

theorem mem_stab_flag_iff {i : ℕ} {g : SL5} :
    g ∈ stabilizer (flagSpace 5 (ZMod 2) i) ↔
      ∀ a b : Fin 5, (b : ℕ) < i → i ≤ (a : ℕ) →
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = 0 := by
  constructor
  · intro hg a b hb ha
    have hmem : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single b 1 ∈
        flagSpace 5 (ZMod 2) i := by
      rw [← mem_stabilizer.mp hg]
      exact ⟨_, BinaryParabolic.single_mem_flagSpace hb, rfl⟩
    have := (mem_flagSpace.mp hmem) a ha
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  · intro h
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro a ha
    simp only [mulVecLin_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : (b : ℕ) < i
    · rw [h a b hb ha, zero_mul]
    · rw [hv b (not_lt.mp hb), mul_zero]

abbrev M (j : ℕ) : Subgroup SL5 := flagStabilizer 5 (ZMod 2) (Set.Icc 1 4 \ {j})

theorem mem_M_iff {j : ℕ} {g : SL5} :
    g ∈ M j ↔ ∀ a b : Fin 5, b < a → ¬ ((a : ℕ) = j ∧ (b : ℕ) + 1 = j) →
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = 0 := by
  rw [mem_flagStabilizer]
  constructor
  · intro h a b hab hn
    have hab' : (b : ℕ) < a := hab
    by_cases hb : (b : ℕ) + 1 = j
    · have ha : (a : ℕ) ≠ j := fun h' => hn ⟨h', hb⟩
      exact mem_stab_flag_iff.mp (h a ⟨⟨by omega, by omega⟩, ha⟩) a b hab' le_rfl
    · exact mem_stab_flag_iff.mp (h (b + 1) ⟨⟨by omega, by omega⟩, hb⟩) a b (by omega)
        (by omega)
  · rintro h i ⟨⟨hi1, hi4⟩, hij⟩
    rw [mem_stab_flag_iff]
    intro a b hb ha
    have hij' : i ≠ j := hij
    exact h a b (show (b : ℕ) < a by omega) (fun ⟨h1, h2⟩ => hij' (by omega))

theorem P0_eq : P0 = M 1 := by
  ext g
  rw [mem_M_iff, mem_btSL]
  constructor
  · intro h a b hab hn
    apply h
    fin_cases a <;> fin_cases b <;> simp_all
  · intro h a b hab
    apply h
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a <;> fin_cases b <;> simp_all

theorem P2_eq : P2 = M 3 := by
  ext g
  rw [mem_M_iff, mem_btSL]
  constructor
  · intro h a b hab hn
    apply h
    fin_cases a <;> fin_cases b <;> simp_all
  · intro h a b hab
    apply h
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a <;> fin_cases b <;> simp_all

abbrev Q1 : Subgroup SL5 := flagStabilizer 5 (ZMod 2) {1}

theorem mem_Q1_iff {g : SL5} :
    g ∈ Q1 ↔ ∀ a : Fin 5, 1 ≤ (a : ℕ) → (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a 0 = 0 := by
  rw [mem_flagStabilizer]
  constructor
  · intro h a ha
    exact mem_stab_flag_iff.mp (h 1 rfl) a 0 (by simp) ha
  · intro h i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rw [mem_stab_flag_iff]
    intro a b hb ha
    have hb0 : b = 0 := Fin.ext (by omega)
    rw [hb0]
    exact h a ha

theorem M_le_Q1 {j : ℕ} (hj : 2 ≤ j) : M j ≤ Q1 := fun g hg =>
  mem_Q1_iff.mpr fun a ha =>
    mem_M_iff.mp hg a 0 (Fin.lt_def.mpr (by simp only [Fin.val_zero]; omega))
      (fun ⟨_, h2⟩ => by simp at h2; omega)

theorem uniSL_eq : uniSL 5 = unitriangular 5 (ZMod 2) := by
  ext g
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun _ _ hij => h1 hij, h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun _ _ hij => h1 _ _ hij, h2⟩⟩

theorem uniSL_le_M (j : ℕ) : uniSL 5 ≤ M j := fun _ hg =>
  mem_M_iff.mpr fun _ _ hab _ => hg.1 hab

theorem M_inf_M {j k : ℕ} (hjk : j ≠ k) : M j ⊓ M k ≤ uniSL 5 := by
  rintro g ⟨hj, hk⟩
  have hup : g ∈ upperTriangular 5 (ZMod 2) := by
    intro a b hab
    by_cases h : (a : ℕ) = j ∧ (b : ℕ) + 1 = j
    · exact mem_M_iff.mp hk a b hab fun h' => hjk (h.1.symm.trans h'.1)
    · exact mem_M_iff.mp hj a b hab h
  rw [BinaryParabolic.upperTriangular_eq_unitriangular, ← uniSL_eq] at hup
  exact hup

theorem relIndex_M {j : ℕ} (hj1 : 1 ≤ j) (hj4 : j ≤ 4) : (uniSL 5).relIndex (M j) = 3 := by
  have h := ((binary_linear_index_three_sylow_overgroups_are_single_root_parabolics
    (n := 5) (by norm_num)).2.2.2.1 j hj1 (by omega)).2
  rw [uniSL_eq]
  exact h

theorem eq_M_of_le {A : Subgroup SL5} (hA : uniSL 5 ≤ A) (h3 : (uniSL 5).relIndex A = 3) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ A = M j := by
  rw [uniSL_eq] at hA h3
  rcases (binary_linear_index_three_sylow_overgroups_are_single_root_parabolics (n := 5)
    (by norm_num)).2.2.1 A hA h3.le with h | ⟨j, ⟨hj1, hj5, hjA⟩, -⟩
  · rw [h, Subgroup.relIndex_self] at h3
    norm_num at h3
  · exact ⟨j, hj1, by omega, hjA⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
