module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] {C : Subgroup G} {c l : G}

theorem comm_mem_perfectCore_right (hc : c ∈ C) (hl : l ∈ perfectCore C) :
    ⁅c, l⁆ ∈ perfectCore C := by
  have h := (perfectCore_normal C).conj_mem ⟨l, perfectCore_le C hl⟩
    (Subgroup.mem_subgroupOf.2 hl) ⟨c, hc⟩
  rw [commutatorElement_def]
  exact mul_mem (Subgroup.mem_subgroupOf.1 h) (inv_mem hl)

theorem comm_mem_perfectCore_left (hc : c ∈ C) (hl : l ∈ perfectCore C) :
    ⁅l, c⁆ ∈ perfectCore C := by
  rw [← commutatorElement_inv]
  exact inv_mem (comm_mem_perfectCore_right hc hl)

end Generic

section L3

variable {K : Type} [Field K]

theorem rootElt_mem_Q3 {a b : Fin 3} (h : a < b) (c : K) (j : Fin 2) : rootElt a b c ∈ Q3 K j :=
  upperTriangular_le_Q3 j (unitriangular_le_upperTriangular 3 K (rootElt_mem_unitriangular h c))

theorem embSL_zero_up (c : K) :
    embSL 0 (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) c) =
      rootElt (1 : Fin 3) 2 c := by
  apply Subtype.ext
  rw [coe_embSL, coe_rootElt_of_ne (by decide)]
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, Matrix.transvection, Matrix.SpecialLinearGroup.transvection]

theorem embSL_zero_low (c : K) :
    embSL 0 (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) c) =
      rootElt (2 : Fin 3) 1 c := by
  apply Subtype.ext
  rw [coe_embSL, coe_rootElt_of_ne (by decide)]
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, Matrix.transvection, Matrix.SpecialLinearGroup.transvection]

theorem embSL_one_up (c : K) :
    embSL 1 (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) c) =
      rootElt (0 : Fin 3) 1 c := by
  apply Subtype.ext
  rw [coe_embSL, coe_rootElt_of_ne (by decide)]
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, Matrix.transvection, Matrix.SpecialLinearGroup.transvection]

theorem embSL_one_low (c : K) :
    embSL 1 (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) c) =
      rootElt (1 : Fin 3) 0 c := by
  apply Subtype.ext
  rw [coe_embSL, coe_rootElt_of_ne (by decide)]
  ext r l
  fin_cases r <;> fin_cases l <;>
    simp [embMat, Matrix.transvection, Matrix.SpecialLinearGroup.transvection]

theorem unitriangular_le_perfectCore_Q3 [Finite K] (hK : ∃ s : Finset K, s.card = 4)
    (j : Fin 2) : unitriangular 3 K ≤ perfectCore (Q3 K j) := by
  refine unitriangular_le_closure_rootElt.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨a, b, c, hab, rfl⟩
  fin_cases j
  · have h12 : ∀ d : K, rootElt (1 : Fin 3) 2 d ∈ perfectCore (Q3 K 0) := fun d => by
      rw [← embSL_zero_up]
      exact embSL_mem_perfectCore hK 0 _
    have h21 : ∀ d : K, rootElt (2 : Fin 3) 1 d ∈ perfectCore (Q3 K 0) := fun d => by
      rw [← embSL_zero_low]
      exact embSL_mem_perfectCore hK 0 _
    have h02 : ∀ d : K, rootElt (0 : Fin 3) 2 d ∈ perfectCore (Q3 K 0) := fun d => by
      have := comm_mem_perfectCore_right (rootElt_mem_Q3 (by decide : (0 : Fin 3) < 1) d 0)
        (h12 1)
      rwa [commutatorElement_rootElt (by decide) (by decide) (by decide), mul_one] at this
    have h01 : ∀ d : K, rootElt (0 : Fin 3) 1 d ∈ perfectCore (Q3 K 0) := fun d => by
      have := comm_mem_perfectCore_right (rootElt_mem_Q3 (by decide : (0 : Fin 3) < 2) d 0)
        (h21 1)
      rwa [commutatorElement_rootElt (by decide) (by decide) (by decide), mul_one] at this
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact h01 c
    · exact h02 c
    · exact h12 c
  · have h01 : ∀ d : K, rootElt (0 : Fin 3) 1 d ∈ perfectCore (Q3 K 1) := fun d => by
      rw [← embSL_one_up]
      exact embSL_mem_perfectCore hK 1 _
    have h10 : ∀ d : K, rootElt (1 : Fin 3) 0 d ∈ perfectCore (Q3 K 1) := fun d => by
      rw [← embSL_one_low]
      exact embSL_mem_perfectCore hK 1 _
    have h02 : ∀ d : K, rootElt (0 : Fin 3) 2 d ∈ perfectCore (Q3 K 1) := fun d => by
      have := comm_mem_perfectCore_left (rootElt_mem_Q3 (by decide : (1 : Fin 3) < 2) 1 1)
        (h01 d)
      rwa [commutatorElement_rootElt (by decide) (by decide) (by decide), mul_one] at this
    have h12 : ∀ d : K, rootElt (1 : Fin 3) 2 d ∈ perfectCore (Q3 K 1) := fun d => by
      have := comm_mem_perfectCore_left (rootElt_mem_Q3 (by decide : (0 : Fin 3) < 2) d 1)
        (h10 1)
      rwa [commutatorElement_rootElt (by decide) (by decide) (by decide), one_mul] at this
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact h01 c
    · exact h02 c
    · exact h12 c

end L3

end CFSG.Quasithin.F146Field.Case2b
