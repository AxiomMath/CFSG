module

public import CFSG.Quasithin.EmptyFaithful.S151ZQ

public section

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def g3M : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def g1M : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0]

theorem g3M_det : g3M.det = 1 := by decide

theorem g1M_det : g1M.det = 1 := by decide

@[expose] def g3 : SLt 4 := ⟨g3M, g3M_det⟩

@[expose] def g1 : SLt 4 := ⟨g1M, g1M_det⟩

theorem g3_pow : g3 ^ 7 = 1 := by
  apply Subtype.ext
  show g3M ^ 7 = 1
  decide

theorem g1_pow : g1 ^ 7 = 1 := by
  apply Subtype.ext
  show g1M ^ 7 = 1
  decide

theorem g3_ne : g3 ≠ 1 := by
  intro h
  have := congrArg (fun x : SLt 4 => (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2) h
  revert this
  decide

theorem g1_ne : g1 ≠ 1 := by
  intro h
  have := congrArg (fun x : SLt 4 => (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3) h
  revert this
  decide

theorem orderOf_g3 : orderOf g3 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime g3_pow g3_ne

theorem orderOf_g1 : orderOf g1 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime g1_pow g1_ne

theorem mem_QI_single_of {n k : ℕ} {g : SLt n}
    (h : ∀ v : Fin n → ZMod 2, (∀ j : Fin n, k ≤ j.val → v j = 0) →
      ∀ j : Fin n, k ≤ j.val → ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) j = 0) :
    g ∈ QI n {k} := by
  rw [QI, mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff.1 hi]
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  exact mem_flagSpace.2 (h v (mem_flagSpace.1 hv))

theorem g3_mem : g3 ∈ QI 4 {3} :=
  mem_QI_single_of (by decide +revert)

theorem g1_mem : g1 ∈ QI 4 {1} :=
  mem_QI_single_of (by decide +revert)

theorem card_QI_end (k : ℕ) (hk : k = 1 ∨ k = 3) : Nat.card ↥(QI 4 {k}) = 1344 := by
  have hUt : Nat.card ↥(Ut 4) = 64 := by
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular (K := ZMod 2) 4
    rw [Nat.card_zmod] at this
    simpa using this
  have hUQ : Ut 4 ≤ QI 4 {k} := Ut_le_QI 4 {k}
  have h1 := Subgroup.relIndex_mul_card (Ut 4) (QI 4 {k})
  rw [inf_of_le_left hUQ, hUt] at h1
  rcases hk with rfl | rfl
  · have hset : ({1} : Set ℕ) = nodeSet 4 \ {2, 3} := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_sdiff, mem_nodeSet, Set.mem_insert_iff]
      omega
    have hidx := index_double (n := 4) (i := 2) (j := 3) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num)
    rw [← hset] at hidx
    have h7 : 7 ∣ Nat.card ↥(QI 4 {1}) := by
      have := orderOf_dvd_natCard (⟨g1, g1_mem⟩ : ↥(QI 4 {1}))
      have e : orderOf (⟨g1, g1_mem⟩ : ↥(QI 4 {1})) = 7 := by
        rw [← orderOf_g1]
        exact Subgroup.orderOf_mk g1 g1_mem
      rwa [e] at this
    rcases hidx with h | h
    · rw [h] at h1
      omega
    · rw [h] at h1
      omega
  · have hset : ({3} : Set ℕ) = nodeSet 4 \ {1, 2} := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_sdiff, mem_nodeSet, Set.mem_insert_iff]
      omega
    have hidx := index_double (n := 4) (i := 1) (j := 2) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      (by norm_num)
    rw [← hset] at hidx
    have h7 : 7 ∣ Nat.card ↥(QI 4 {3}) := by
      have := orderOf_dvd_natCard (⟨g3, g3_mem⟩ : ↥(QI 4 {3}))
      have e : orderOf (⟨g3, g3_mem⟩ : ↥(QI 4 {3})) = 7 := by
        rw [← orderOf_g3]
        exact Subgroup.orderOf_mk g3 g3_mem
      rwa [e] at this
    rcases hidx with h | h
    · rw [h] at h1
      omega
    · rw [h] at h1
      omega

end CFSG.Quasithin.A38c10
