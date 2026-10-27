module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelFork
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelFar
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyDisj

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section Main

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)

private theorem pmm_A3_cases_of_three_le {m : ℕ} (hm : 3 ≤ m) (i j k : Fin (m + 1))
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 2) :
    (∃ a : ℕ, a + 3 ≤ m ∧ ((i.val = a ∧ j.val = a + 1 ∧ k.val = a + 2) ∨
      (i.val = a + 2 ∧ j.val = a + 1 ∧ k.val = a))) ∨
    ((i.val = m - 3 ∧ j.val = m - 2 ∧ k.val = m) ∨ (i.val = m ∧ j.val = m - 2 ∧ k.val = m - 3)) ∨
    ((i.val = m - 1 ∧ j.val = m - 2 ∧ k.val = m) ∨
      (i.val = m ∧ j.val = m - 2 ∧ k.val = m - 1)) := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hik : i ≠ k := by
    rintro rfl
    rw [qtwoLabel_self] at h3
    omega
  have h1' := (qtwoLabel_three_iff hm i j).mp h1
  have h2' := (qtwoLabel_three_iff hm j k).mp h2
  rcases h1' with ⟨hij, hij'⟩ | ⟨hij, hij'⟩ | ⟨hij, hij'⟩ | ⟨hij, hij'⟩
  · rcases h2' with ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩
    · exact Or.inl ⟨i.val, by omega, Or.inl ⟨rfl, by omega, by omega⟩⟩
    · exfalso
      exact hik (Fin.ext (by omega))
    · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
    · exfalso
      omega
  · rcases h2' with ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩
    · exfalso
      exact hik (Fin.ext (by omega))
    · exact Or.inl ⟨k.val, by omega, Or.inr ⟨by omega, by omega, rfl⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    · exfalso
      omega
  · rcases h2' with ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      omega
    · exfalso
      exact hik (Fin.ext (by omega))
  · rcases h2' with ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩ | ⟨hjk, hjk'⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨by omega, by omega, by omega⟩))
    · exfalso
      exact hik (Fin.ext (by omega))
    · exfalso
      omega

theorem qtwo_A3_cases (i j k : Fin (m + 1))
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 2) :
    (∃ a : ℕ, a + 3 ≤ m ∧ ((i.val = a ∧ j.val = a + 1 ∧ k.val = a + 2) ∨
      (i.val = a + 2 ∧ j.val = a + 1 ∧ k.val = a))) ∨
    ((i.val = m - 3 ∧ j.val = m - 2 ∧ k.val = m) ∨ (i.val = m ∧ j.val = m - 2 ∧ k.val = m - 3)) ∨
    ((i.val = m - 1 ∧ j.val = m - 2 ∧ k.val = m) ∨
      (i.val = m ∧ j.val = m - 2 ∧ k.val = m - 1)) := by
  by_cases hm : 3 ≤ m
  · exact pmm_A3_cases_of_three_le hm i j k h1 h2 h3
  · have hm2 : m ≤ 2 := by omega
    interval_cases m
    · exfalso
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [CFSG.StandardType.ggCoxeterMatrixD_apply] at h1
    · exfalso
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [CFSG.StandardType.ggCoxeterMatrixD_apply, CartanMatrix.D] at h1 h2 h3
    · fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [CFSG.StandardType.ggCoxeterMatrixD_apply, CartanMatrix.D] at h1 h2 h3 ⊢

theorem qtwoStd_pair (i j : Fin (m + 1))
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    UnitaryBlockStandardPair K 2 1 (qtwoStdW E m hm i j) (qtwoStdU E m hm i)
      (qtwoStdU E m hm j) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [qtwoLabel_self] at h
    omega
  have hconj : (MulAut.conj (1 : Su K 2 1 3)⁻¹).toMonoidHom =
      MonoidHom.id (Su K 2 1 3) := by
    ext x
    simp
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨(stdFamilyV E m hm).θ i j, 1, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
    · unfold qtwoStdW
      rw [if_pos h, if_pos hlt]
    · have hinj := stdFamilyV_θ_inj E hm i j hlt h
      rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
      exact bot_le
    · rw [hconj, Subgroup.map_id]
      unfold B12 qtwoStdU
      rw [← MonoidHom.range_comp, (stdFamilyV E m hm).left i j hlt h]
    · rw [hconj, Subgroup.map_id]
      unfold B23 qtwoStdU
      rw [← MonoidHom.range_comp, (stdFamilyV E m hm).right i j hlt h]
  · have hMji : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := by
      rw [((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j)]
      exact h
    refine ⟨(stdFamilyV E m hm).θ j i, 1, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
    · unfold qtwoStdW
      rw [if_pos h, if_neg (not_lt_of_gt hgt)]
    · have hinj := stdFamilyV_θ_inj E hm j i hgt hMji
      rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
      exact bot_le
    · rw [hconj, Subgroup.map_id]
      unfold B12 qtwoStdU
      rw [← MonoidHom.range_comp, (stdFamilyV E m hm).left j i hgt hMji]
    · rw [hconj, Subgroup.map_id]
      unfold B23 qtwoStdU
      rw [← MonoidHom.range_comp, (stdFamilyV E m hm).right j i hgt hMji]

end Main

end CFSG.StandardType.QTwo

end
