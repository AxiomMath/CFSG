module

public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

section Family

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {M : CoxeterMatrix (Fin n)}
  {G : Type} [Group G]

theorem PhanFamilyE.torus_inf_of_le (S : PhanFamilyE K 2 f M G)
    (h1 : ∀ i, (S.ι i).range ⊓ S.torus ≤ (S.nodeTor i).range)
    (h2 : ∀ i j, i ≠ j → ((S.ι i).range ⊔ (S.ι j).range) ⊓ S.torus ≤
      (S.nodeTor i).range ⊔ (S.nodeTor j).range)
    (J : Set (Fin n)) (hJ : J.encard ≤ 2) :
    (⨆ j ∈ J, (S.ι j).range) ⊓ S.torus = ⨆ j ∈ J, (S.nodeTor j).range := by
  refine le_antisymm ?_ ?_
  · rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · have hle1 : (J \ {i}).encard ≤ 1 := by
        have h := Set.encard_sdiff_singleton_add_one hi
        have h2 : (J \ {i}).encard + 1 ≤ 1 + 1 := by
          rw [h]
          simpa only [one_add_one_eq_two] using hJ
        exact (ENat.add_le_add_iff_right (by norm_num : (1 : ENat) ≠ ⊤)).mp h2
      rcases Set.encard_le_one_iff_eq.1 hle1 with h0 | ⟨j, hj⟩
      · have hJeq : J = {i} := by
          apply Set.Subset.antisymm
          · intro x hx
            by_contra hxi
            have hmem : x ∈ J \ {i} := ⟨hx, hxi⟩
            rw [h0] at hmem
            exact hmem
          · intro x hx
            rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact hi
        subst hJeq
        simp only [iSup_singleton]
        exact h1 i
      · have hjmem : j ∈ J \ {i} := by rw [hj]; exact Set.mem_singleton j
        have hji : j ≠ i := hjmem.2
        have hJeq : J = {i, j} := by
          apply Set.Subset.antisymm
          · intro x hx
            rcases eq_or_ne x i with hxi | hxi
            · rw [hxi]
              exact Set.mem_insert i {j}
            · have hx' : x ∈ J \ {i} := ⟨hx, hxi⟩
              rw [hj] at hx'
              rw [Set.mem_singleton_iff] at hx'
              rw [hx']
              exact Set.mem_insert_of_mem i rfl
          · intro x hx
            rcases hx with rfl | rfl
            · exact hi
            · exact hjmem.1
        subst hJeq
        simp only [iSup_insert, iSup_singleton]
        exact h2 i j (Ne.symm hji)
  · refine iSup₂_le fun j hj => ?_
    have hle : (S.nodeTor j).range ≤ (S.ι j).range := by
      rw [PhanFamilyE.nodeTor, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    refine le_inf ?_ ?_
    · exact hle.trans (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    · rw [PhanFamilyE.torus]
      exact le_iSup (fun i => (S.nodeTor i).range) j


theorem PhanFamilyE.eq_of_ι_eq_of_θ_eq {S T : PhanFamilyE K 2 f M G}
    (hι : ∀ i, S.ι i = T.ι i) (hθ : ∀ i j, S.θ i j = T.θ i j) : S = T := by
  cases S with
  | mk i1 t1 l1 r1 c1 =>
    cases T with
    | mk i2 t2 l2 r2 c2 =>
      have e1 : i1 = i2 := funext hι
      have e2 : t1 = t2 := funext fun i => funext (hθ i)
      subst e1
      subst e2
      rfl

end Family

end CFSG.ClassicalInvolution.Phan.PhanE
