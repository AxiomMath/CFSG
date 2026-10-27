module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallCaseA
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallCaseB
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallCaseC

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_tableSmall_holds : C2TableSmallLeaf := by
  unfold C2TableSmallLeaf
  intro hT hSp p hp hp3 n hn V instACG instMod b A hPA hStab r u φ hnf c hcoef hcne hex hk hnot
  subst hp3
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => i ≠ 0 ∧ b.coord i u ≠ 0) with hSdef
  set k : ℕ := S.card with hkdef
  have hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0 := by
    intro i; rw [hSdef]; simp
  have h0S : (0 : Fin (n + 1)) ∉ S := by
    rw [hS_mem]; simp
  have hk1 : 1 ≤ k := by
    obtain ⟨i, hi0, hic⟩ := hex
    rw [hkdef]
    exact Finset.card_pos.mpr ⟨i, (hS_mem i).mpr ⟨hi0, hic⟩⟩
  have hk' : b.coord 0 u = 2 - c * (k : ZMod 3) := (eq_sub_iff_add_eq).mpr hk
  rcases hdRo7CSmallAux_zmod3_ne_zero hcne with hc1 | hcm1
  · subst hc1
    have hk4 : k ≤ 4 := by
      by_contra h
      exact hnot (Or.inl ⟨rfl, not_le.mp h⟩)
    interval_cases k
    · have hScard : S.card = 1 := by omega
      have hu0val : b.coord 0 u = 1 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_c1_k1 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
    · exfalso
      have hScard : S.card = 2 := by omega
      have hu0val : b.coord 0 u = 0 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_c1_k2 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
    · exfalso
      have hScard : S.card = 3 := by omega
      have hu0val : b.coord 0 u = -1 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_c1_k3 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
    · exfalso
      have hScard : S.card = 4 := by omega
      have hu0val : b.coord 0 u = 1 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_c1_k4 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
  · subst hcm1
    have hk3 : k ≤ 3 := by
      by_contra h
      exact hnot (Or.inr ⟨rfl, not_le.mp h⟩)
    interval_cases k
    · exfalso
      have hu0val : b.coord 0 u = 0 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_cm1_k1 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hu0val
    · exfalso
      have hScard : S.card = 2 := by omega
      have hu0val : b.coord 0 u = 1 := by norm_num at hk' ⊢; exact hk'
      exact hdRo7CSmallAux_case_cm1_k2 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
    · exfalso
      have hScard : S.card = 3 := by omega
      have hu0val : b.coord 0 u = -1 := by rw [hk']; exact hdRo7CSmallAux_zmod3_m13
      exact hdRo7CSmallAux_case_cm1_k3 hT hSp hn b A hPA hStab r u φ hnf hcoef S hS_mem hScard hu0val
end CFSG.StandardType.HdRo7C
