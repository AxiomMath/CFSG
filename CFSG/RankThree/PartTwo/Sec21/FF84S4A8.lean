module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

theorem mem_CenS_Pm_iff (g : P8) : g ∈ CenS Pm ↔ g * cc = cc * g ∧ g * dd = dd * g := by
  constructor
  · intro h
    have hc : cc ∈ (Pm : Set P8) := Subgroup.subset_closure (Set.mem_insert _ _)
    have hd : dd ∈ (Pm : Set P8) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact ⟨(mem_centralizer_iff.1 h cc hc).symm, (mem_centralizer_iff.1 h dd hd).symm⟩
  · rintro ⟨h1, h2⟩
    have hle : Subgroup.closure ({cc, dd} : Set P8) ≤ centralizer {g} := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rcases hx with rfl | hx
      · exact mem_centralizer_singleton_iff.2 h1.symm
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact mem_centralizer_singleton_iff.2 h2.symm
    refine mem_centralizer_iff.2 fun x hx => ?_
    exact mem_centralizer_singleton_iff.1 (hle hx)

@[expose] def centVals (a b c d : Fin 8) : Fin 8 → Fin 8 :=
  ![a, cc a, cc (cc a), b, dd b, dd (dd b), c, d]

theorem centVals_key : ∀ c : Fin 8, cc c = c → dd c = c → ∀ d : Fin 8, cc d = d → dd d = d →
    ∀ a b : Fin 8, (∀ i, centVals a b c d (centVals a b c d i) = i) →
      (∃ i, centVals a b c d i ≠ i) → ∀ i, centVals a b c d i = swap 6 7 i := by
  decide +kernel

theorem involution_cent_P_key : ∀ g : P8, g * cc = cc * g → g * dd = dd * g → g * g = 1 →
    g ≠ 1 → g = swap 6 7 := by
  intro g h1 h2 h3 h4
  have e1 : ∀ i, g (cc i) = cc (g i) := fun i => by
    simpa only [Perm.mul_apply] using congrArg (fun p : P8 => p i) h1
  have e2 : ∀ i, g (dd i) = dd (g i) := fun i => by
    simpa only [Perm.mul_apply] using congrArg (fun p : P8 => p i) h2
  have hc0 : cc 0 = 1 := by decide
  have hc1 : cc 1 = 2 := by decide
  have hc6 : cc 6 = 6 := by decide
  have hc7 : cc 7 = 7 := by decide
  have hd3 : dd 3 = 4 := by decide
  have hd4 : dd 4 = 5 := by decide
  have hd6 : dd 6 = 6 := by decide
  have hd7 : dd 7 = 7 := by decide
  have g1 : g 1 = cc (g 0) := by have := e1 0; rwa [hc0] at this
  have g2 : g 2 = cc (cc (g 0)) := by have := e1 1; rwa [hc1, g1] at this
  have g4 : g 4 = dd (g 3) := by have := e2 3; rwa [hd3] at this
  have g5 : g 5 = dd (dd (g 3)) := by have := e2 4; rwa [hd4, g4] at this
  have c6 : cc (g 6) = g 6 := by have := e1 6; rw [hc6] at this; exact this.symm
  have c7 : cc (g 7) = g 7 := by have := e1 7; rw [hc7] at this; exact this.symm
  have d6 : dd (g 6) = g 6 := by have := e2 6; rw [hd6] at this; exact this.symm
  have d7 : dd (g 7) = g 7 := by have := e2 7; rw [hd7] at this; exact this.symm
  have hg : ∀ i, g i = centVals (g 0) (g 3) (g 6) (g 7) i := by
    intro i
    fin_cases i <;> simp [centVals, g1, g2, g4, g5]
  have hinv : ∀ i, centVals (g 0) (g 3) (g 6) (g 7) (centVals (g 0) (g 3) (g 6) (g 7) i) = i := by
    intro i
    have := congrArg (fun p : P8 => p i) h3
    simp only [Perm.mul_apply, Perm.one_apply] at this
    rwa [hg i, hg (centVals (g 0) (g 3) (g 6) (g 7) i)] at this
  have hne : ∃ i, centVals (g 0) (g 3) (g 6) (g 7) i ≠ i := by
    by_contra hall
    push_neg at hall
    exact h4 (Equiv.ext fun i => by rw [hg i, hall i, Perm.one_apply])
  exact Equiv.ext fun i => by
    rw [hg i]
    exact centVals_key (g 6) c6 d6 (g 7) c7 d7 (g 0) (g 3) hinv hne i

theorem involution_cent_P_eq (g : P8) (h1 : g * cc = cc * g) (h2 : g * dd = dd * g)
    (h3 : g * g = 1) (h4 : g ≠ 1) : g = swap 6 7 :=
  involution_cent_P_key g h1 h2 h3 h4

theorem A_cent_P_inv_involution : ∀ g ∈ CenS Pm, orderOf g = 2 → g = Equiv.swap 6 7 := by
  intro g hg ho
  rw [mem_CenS_Pm_iff] at hg
  have hsq : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [ho] at this
    simpa [pow_two] using this
  have hne : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    exact absurd ho (by norm_num)
  exact involution_cent_P_eq g hg.1 hg.2 hsq hne

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
