module

public import CFSG.Quasithin.AppendixH.H9.H92.CentSwap.OrthogonalCentralizer
public import CFSG.Quasithin.AppendixH.H9.H93.Theta.OuterInvolution

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

@[expose] def evenDiag (n : ℕ) : Subgroup (PairN n) where
  carrier := {x | ∃ c : Fin n → ZMod 2, ∑ i, c i = 0 ∧ x = pairVec c c}
  one_mem' := ⟨0, by simp, pairVec_one⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c + d, ?_, pairVec_mul c c d d⟩
    simp [Finset.sum_add_distrib, hc, hd]
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, pairVec_inv c c⟩

theorem mem_evenDiag {x : PairN n} :
    x ∈ evenDiag n ↔ ∃ c : Fin n → ZMod 2, ∑ i, c i = 0 ∧ x = pairVec c c := Iff.rfl

theorem mem_fixV_swap_iff {x : PairN n} :
    x ∈ fixV (Subgroup.zpowers (swapN n)) ↔ ∃ a : Fin n → ZMod 2, x = pairVec a a := by
  rw [mem_fixV_zpowers_iff_of_involution swapN_mul_self]
  constructor
  · intro h
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    have h' : pairVec b a = pairVec a b := (swapN_pairVec a b).symm.trans h
    obtain ⟨h1, -⟩ := pairVec_inj.mp h'
    subst h1
    exact ⟨b, rfl⟩
  · rintro ⟨a, rfl⟩
    exact swapN_pairVec a a

theorem evenDiag_le_fixV_swap : evenDiag n ≤ fixV (Subgroup.zpowers (swapN n)) := by
  rintro x ⟨c, -, rfl⟩
  exact mem_fixV_swap_iff.mpr ⟨c, rfl⟩

theorem commOn_fixV_swap_eq :
    commOn (fixV (Subgroup.zpowers (swapN n)))
      (Lg n ⊓ Subgroup.centralizer ({swapN n} : Set (MulAut (PairN n)))) = evenDiag n := by
  apply le_antisymm
  · unfold commOn
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨a, ha, w, hw, rfl⟩
    obtain ⟨B, hB, rfl⟩ := mem_inf_centralizer_swap_iff.mp ha
    obtain ⟨c, rfl⟩ := mem_fixV_swap_iff.mp hw
    have key : pairActN n B (pairVec c c) * (pairVec c c)⁻¹ =
        pairVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c + c)
          ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c + c) := by
      rw [pairActN_pairVec_of_orth hB, pairVec_inv, pairVec_mul]
    have hev : ∑ i, ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c + c) i = 0 := by
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, orth_sum_mulVec hB c]
      exact CharTwo.add_self_eq_zero _
    exact mem_evenDiag.mpr ⟨_, hev, key⟩
  · rintro x ⟨c, hc, rfl⟩
    by_cases h0 : c = 0
    · subst h0
      rw [← pairVec_one]
      exact one_mem _
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
      have hi1 : c i = 1 := by
        have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
        exact this _ hi
      obtain ⟨B, hB, hBc⟩ := exists_orth_mulVec_single_add c hc i hi1
      have key : pairActN n B (pairVec (Pi.single i 1) (Pi.single i 1)) *
          (pairVec (Pi.single i 1) (Pi.single i 1))⁻¹ = pairVec c c := by
        rw [pairActN_pairVec_of_orth hB, pairVec_inv, pairVec_mul, hBc]
      exact Subgroup.subset_closure ⟨pairActN n B,
        mem_inf_centralizer_swap_iff.mpr ⟨B, hB, rfl⟩,
        pairVec (Pi.single i 1) (Pi.single i 1), mem_fixV_swap_iff.mpr ⟨_, rfl⟩, key.symm⟩

end CFSG.ASVolI.ChH
