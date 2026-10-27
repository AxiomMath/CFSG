module

public import CFSG.Quasithin.AppendixH.H9.H92.CentSwap.DiagonalCommutator

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem exists_nonsingular_vec_swap :
    ∃ v ∈ fixV (Subgroup.zpowers (swapN 5)), pairQn 5 v = 1 ∧
      (∀ g ∈ Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5))), g v = v) ∧
      fixV (Subgroup.zpowers (swapN 5)) =
        Subgroup.zpowers v ⊔ commOn (fixV (Subgroup.zpowers (swapN 5)))
          (Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5)))) ∧
      Subgroup.zpowers v ⊓ commOn (fixV (Subgroup.zpowers (swapN 5)))
          (Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5)))) = ⊥ := by
  have hone : (∑ i : Fin 5, (1 : ZMod 2)) = 1 := by decide
  have hvF : pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) ∈
      fixV (Subgroup.zpowers (swapN 5)) := mem_fixV_swap_iff.mpr ⟨_, rfl⟩
  have hvv : pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) *
      pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) = 1 := by
    rw [← pairVec_inv (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1)]
    exact mul_inv_cancel _
  have hvD : pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) ∉ evenDiag 5 := by
    rintro ⟨c, hc, hvc⟩
    obtain ⟨h1, -⟩ := pairVec_inj.mp hvc
    rw [← h1] at hc
    rw [hone] at hc
    exact one_ne_zero hc
  refine ⟨pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1), hvF, ?_, ?_, ?_, ?_⟩
  · rw [pairQn_pairVec]
    simpa [dotProduct] using hone
  · intro g hg
    obtain ⟨B, hB, rfl⟩ := mem_inf_centralizer_swap_iff.mp hg
    have h := pairActN_pairVec_of_orth hB (fun _ => (1 : ZMod 2)) (fun _ => (1 : ZMod 2))
    rw [orth_mulVec_ones hB] at h
    exact h
  · rw [commOn_fixV_swap_eq]
    apply le_antisymm
    · intro x hx
      obtain ⟨a, rfl⟩ := mem_fixV_swap_iff.mp hx
      by_cases hε : ∑ i, a i = 0
      · exact Subgroup.mem_sup_right ⟨a, hε, rfl⟩
      · have hε1 : ∑ i, a i = 1 := by
          have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          exact this _ hε
        have hy : pairVec (a + fun _ => (1 : ZMod 2)) (a + fun _ => (1 : ZMod 2)) ∈ evenDiag 5 := by
          refine ⟨a + fun _ => 1, ?_, rfl⟩
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, hε1, hone]
          decide
        have hx : pairVec a a = pairVec (fun _ : Fin 5 => (1 : ZMod 2)) (fun _ => 1) *
            pairVec (a + fun _ => (1 : ZMod 2)) (a + fun _ => (1 : ZMod 2)) := by
          rw [pairVec_mul]
          have : ((fun _ : Fin 5 => (1 : ZMod 2)) + (a + fun _ => (1 : ZMod 2))) = a := by
            funext i
            simp only [Pi.add_apply]
            exact (by decide : ∀ z : ZMod 2, 1 + (z + 1) = z) (a i)
          rw [this]
        rw [hx]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) hy
    · exact sup_le ((Subgroup.zpowers_le).mpr hvF) evenDiag_le_fixV_swap
  · rw [commOn_fixV_swap_eq]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rcases mem_zpowers_involution hvv hx1 with h | h
    · exact h
    · exact absurd (h ▸ hx2) hvD

end CFSG.ASVolI.ChH
