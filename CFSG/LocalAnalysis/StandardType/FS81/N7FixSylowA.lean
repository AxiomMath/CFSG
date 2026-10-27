module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixInv

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem q2nN7_E6set_subset_F1set : E6set ⊆ F1set := by
  rintro _ ⟨S, h0, hS, rfl⟩
  exact ⟨S, h0, by rw [hS]; decide, rfl⟩

theorem q2nN7_one_mem_F1set : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ F1set :=
  ⟨∅, Finset.notMem_empty _, by simp, q2nN7_sgn_empty.symm⟩

private theorem q2nN7_even_card_symmDiff {A B : Finset (Fin 8)} (hA : Even A.card)
    (hB : Even B.card) : Even (symmDiff A B).card := by
  have h1 : Even (A \ B).card ↔ Even (A ∩ B).card := by
    have h : Even ((A \ B).card + (A ∩ B).card) := by
      rw [Finset.card_sdiff_add_card_inter]; exact hA
    exact Nat.even_add.mp h
  have h2 : Even (B \ A).card ↔ Even (A ∩ B).card := by
    have h : Even ((B \ A).card + (A ∩ B).card) := by
      rw [Finset.inter_comm A B, Finset.card_sdiff_add_card_inter]; exact hB
    exact Nat.even_add.mp h
  have hdisj : Disjoint (A \ B) (B \ A) :=
    Finset.disjoint_left.2 fun _ ha hb => (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 hb).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  exact Nat.even_add.mpr (h1.trans h2.symm)

theorem q2nN7_F1set_mul {M N : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ F1set)
    (hN : N ∈ F1set) : M * N ∈ F1set := by
  obtain ⟨A, h0A, heA, rfl⟩ := hM
  obtain ⟨B, h0B, heB, rfl⟩ := hN
  refine ⟨symmDiff A B, ?_, q2nN7_even_card_symmDiff heA heB, q2nN7_sgn_mul A B⟩
  intro h
  rw [Finset.mem_symmDiff] at h
  rcases h with ⟨ha, _⟩ | ⟨hb, _⟩
  · exact h0A ha
  · exact h0B hb

theorem q2nN7_sgn_pair_eq_mul {i j : Fin 8} (hij : i ≠ j) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ A B : Finset (Fin 8), 0 ∉ A ∧ 0 ∉ B ∧ A.card = 6 ∧ B.card = 6 ∧
      sgn ({i, j} : Finset (Fin 8)) = sgn A * sgn B := by
  refine ⟨Finset.univ \ {0, i}, Finset.univ \ {0, j}, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Finset.mem_sdiff]
  · simp [Finset.mem_sdiff]
  · rw [Finset.card_univ_sdiff, Finset.card_pair hi.symm, Fintype.card_fin]
  · rw [Finset.card_univ_sdiff, Finset.card_pair hj.symm, Fintype.card_fin]
  · rw [q2nN7_sgn_mul]
    refine congrArg sgn ?_
    ext k
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hk0 : k = 0
    · rw [hk0]; simp [Ne.symm hi, Ne.symm hj]
    · by_cases hki : k = i
      · rw [hki]; simp [hi, hij]
      · by_cases hkj : k = j
        · rw [hkj]; simp [hj, Ne.symm hij]
        · simp [hk0, hki, hkj]

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

@[expose] def F1 : Subgroup X := Subgroup.closure {x | S.ρ x ∈ E6set}

theorem exists_of_mem_E6set {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ E6set) :
    ∃ x : X, S.ρ x = M :=
  S.surj_H M (E6set_subset_evenFix0 hM)

theorem q2nN7_exists_mem_F1 (A : Finset (Fin 8)) (h0 : (0 : Fin 8) ∉ A) (he : Even A.card) :
    ∃ x ∈ S.F1, S.ρ x = sgn A := by
  classical
  suffices key : ∀ n : ℕ, ∀ A : Finset (Fin 8), A.card = n → (0 : Fin 8) ∉ A →
      Even A.card → ∃ x ∈ S.F1, S.ρ x = sgn A by
    exact key A.card A rfl h0 he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hAn h0 he
    rcases Finset.eq_empty_or_nonempty A with hA | ⟨i, hiA⟩
    · subst hA
      exact ⟨1, S.F1.one_mem, by rw [map_one, q2nN7_sgn_empty]⟩
    · have hcardpos : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
      have hcard2 : 2 ≤ A.card :=
        Nat.one_lt_of_ne_zero_of_even (Nat.pos_iff_ne_zero.mp hcardpos) he
      have hne : (A.erase i).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hiA]
        omega
      obtain ⟨j, hj⟩ := hne
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjA : j ∈ A := Finset.mem_of_mem_erase hj
      set A' : Finset (Fin 8) := (A.erase i).erase j with hA'def
      have h0' : (0 : Fin 8) ∉ A' := by
        intro h
        exact h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hA'def ▸ h)))
      have hcard' : A'.card = A.card - 2 := by
        rw [hA'def, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hiA]
        omega
      have hEven' : Even A'.card := by
        rw [hcard']
        exact (Nat.even_sub hcard2).2 (iff_of_true he even_two)
      obtain ⟨x', hx', hx'ρ⟩ := ih A'.card (by rw [← hAn]; omega) A' rfl h0' hEven'
      have hi0 : i ≠ 0 := fun h => h0 (h ▸ hiA)
      have hj0 : j ≠ 0 := fun h => h0 (h ▸ hjA)
      obtain ⟨A₁, A₂, h0₁, h0₂, hc₁, hc₂, hpair⟩ :=
        q2nN7_sgn_pair_eq_mul (Ne.symm hji) hi0 hj0
      obtain ⟨y₁, hy₁⟩ := S.exists_of_mem_E6set ⟨A₁, h0₁, hc₁, rfl⟩
      obtain ⟨y₂, hy₂⟩ := S.exists_of_mem_E6set ⟨A₂, h0₂, hc₂, rfl⟩
      have hm₁ : y₁ ∈ S.F1 :=
        Subgroup.subset_closure (show S.ρ y₁ ∈ E6set from ⟨A₁, h0₁, hc₁, hy₁⟩)
      have hm₂ : y₂ ∈ S.F1 :=
        Subgroup.subset_closure (show S.ρ y₂ ∈ E6set from ⟨A₂, h0₂, hc₂, hy₂⟩)
      have hiA' : i ∉ A' := by simp [hA'def, Finset.mem_erase]
      have hjA' : j ∉ A' := by simp [hA'def, Finset.mem_erase]
      have hAunion : A = ({i, j} : Finset (Fin 8)) ∪ A' := by
        ext k
        constructor
        · intro hk
          by_cases hki : k = i
          · exact Finset.mem_union_left _ (by simp [hki])
          · by_cases hkj : k = j
            · exact Finset.mem_union_left _ (by simp [hkj])
            · refine Finset.mem_union_right _ ?_
              rw [hA'def, Finset.mem_erase, Finset.mem_erase]
              exact ⟨hkj, hki, hk⟩
        · intro hk
          rcases Finset.mem_union.mp hk with hk | hk
          · rcases Finset.mem_insert.mp hk with hki | hkj
            · rw [hki]; exact hiA
            · rw [Finset.mem_singleton.mp hkj]; exact hjA
          · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hA'def ▸ hk))
      have hdisj : Disjoint ({i, j} : Finset (Fin 8)) A' := by
        rw [Finset.disjoint_left]
        intro k hk hk'
        rcases Finset.mem_insert.mp hk with hki | hkj
        · rw [hki] at hk'; exact hiA' hk'
        · rw [Finset.mem_singleton.mp hkj] at hk'; exact hjA' hk'
      refine ⟨y₁ * y₂ * x', S.F1.mul_mem (S.F1.mul_mem hm₁ hm₂) hx', ?_⟩
      rw [map_mul, map_mul, hy₁, hy₂, hx'ρ, ← hpair, q2nN7_sgn_mul,
        Finset.symmDiff_eq_union hdisj, ← hAunion]

theorem mem_F1_iff (x : X) : x ∈ S.F1 ↔ S.ρ x ∈ F1set := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun y _ => S.ρ y ∈ F1set) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact q2nN7_E6set_subset_F1set hy
    · rw [map_one]
      exact q2nN7_one_mem_F1set
    · intro y z _ _ hy hz
      rw [map_mul]
      exact q2nN7_F1set_mul hy hz
    · intro y _ hy
      obtain ⟨A, h0, he, hA⟩ := hy
      have hmul : S.ρ y⁻¹ * S.ρ y = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have h1 : S.ρ y⁻¹ = sgn A := by
        calc S.ρ y⁻¹ = S.ρ y⁻¹ * (sgn A * sgn A) := by rw [q2nN7_sgn_mul_self, mul_one]
          _ = (S.ρ y⁻¹ * S.ρ y) * sgn A := by rw [hA, mul_assoc]
          _ = sgn A := by rw [hmul, one_mul]
      exact ⟨A, h0, he, h1⟩
  · rintro ⟨A, h0, he, hA⟩
    obtain ⟨x', hx', hρ⟩ := S.q2nN7_exists_mem_F1 A h0 he
    have hx : x = x' := S.ρ_inj (hA.trans hρ.symm)
    exact hx ▸ hx'

theorem F1_le_H : S.F1 ≤ S.H := by
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  exact (S.mem_H_iff x).2 (E6set_subset_evenFix0 hx)

theorem F1_comm {a b : X} (ha : a ∈ S.F1) (hb : b ∈ S.F1) : a * b = b * a := by
  obtain ⟨A, -, -, hA⟩ := (S.mem_F1_iff a).1 ha
  obtain ⟨B, -, -, hB⟩ := (S.mem_F1_iff b).1 hb
  apply S.ρ_inj
  rw [map_mul, map_mul, hA, hB, q2nN7_sgn_comm]

theorem F1_sq {a : X} (ha : a ∈ S.F1) : a * a = 1 := by
  obtain ⟨A, -, -, hA⟩ := (S.mem_F1_iff a).1 ha
  apply S.ρ_inj
  rw [map_mul, map_one, hA, q2nN7_sgn_mul_self]

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
