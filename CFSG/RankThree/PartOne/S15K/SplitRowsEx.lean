module

public import CFSG.RankThree.PartOne.S15K.SplitRows
public import CFSG.RankThree.PartOne.KF.F132AtEx
public import CFSG.RankThree.PartOne.S15K.KF158A
public import CFSG.RankThree.PartOne.S15K.LayerData

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem split_of_rowDeg {r f g p : ℕ} (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7)
    (hpf : p ∣ 2 ^ f - 1) (hdeg : S13K.KRowDeg r f g) : p ∣ 2 ^ g - 1 := by
  have h2 : p ∣ 2 ^ (2 * f) - 1 := hpf.trans (S13K.two_pow_sub_one_dvd_mul f 2)
  have h3 : p ∣ 2 ^ (3 * f) - 1 := hpf.trans (S13K.two_pow_sub_one_dvd_mul f 3)
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [S13K.KRowDeg] at hdeg
    subst hdeg
    exact hpf
  · simp only [S13K.KRowDeg] at hdeg
    subst hdeg
    exact hpf
  · simp only [S13K.KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h3
  · simp only [S13K.KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h2
  · simp only [S13K.KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h2
  · simp only [S13K.KRowDeg] at hdeg
    subst hdeg
    exact hpf

variable {G : Type} [Group G] [Finite G]

theorem kf158ASplit_of_kf132ex (h123 : Node123) (hS13 : Sec13Avail)
    (hAt : ∀ r : ℕ, (r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7) → S13K.KF132AtEx r)
    (hShort : S13K.KF132Short8) : KF158ASplit := by
  intro G _ _ p A c L E h15 hF hout
  have h := h15.h12
  have hEA : E = A := by
    rcases hout with h | h | h | h
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne hEA
  have hF13 := hS13 G p A c L E h hnot5
  obtain ⟨hclos, r, hr1, hr12, hrow, hweyl, hrA, hr9⟩ := h123 G p A c L E h
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    rw [hEA, h.A_card] at h4
    have hp := h.prime
    have h5 : 5 ≤ p := Sec12Three.five_le h
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hexp : ∀ x ∈ reflectionGroup p E, x ^ 12 = 1 := by
    apply reflectionGroup_pow_twelve
    rcases hout with ⟨-, -, -, -, ⟨σ⟩, -⟩ | ⟨-, -, -, -, ⟨σ⟩, -⟩ | ⟨-, -, -, -, ⟨σ⟩, -⟩ |
        ⟨-, -, -, -, ⟨σ⟩, -⟩
    · exact Or.inl ⟨σ⟩
    · exact Or.inr ⟨σ⟩
    · exact Or.inr ⟨σ⟩
    · exact Or.inr ⟨σ⟩
  have hstar : torusImage E L ≤ reflectionGroup p E := by
    calc torusImage E L = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) :=
          hclos
      _ ≤ reflectionGroup p E := Subgroup.closure_mono Set.inter_subset_left
  by_cases h8 : r = 8
  · subst h8
    obtain ⟨t, ht, -, g, hg, hKF⟩ := S13K.kf132Short8_split hShort h hF hF13 hnot5 hrow hEA
    exact ⟨t, ht, g, hg, hKF⟩
  · have h4 : r ≠ 4 := by
      rintro rfl
      obtain ⟨e⟩ : Nonempty (↥(torusImage E L) ≃* DihedralGroup 8) := hweyl
      exact false_of_dihedral_eight hstar hexp e
    have hrr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
    obtain ⟨t, ht, -, f, g, hRM, hdeg, hKF⟩ := hAt r hrr G p A c L E h hF hF13 hnot5 h4 hrow
      (fun _ => hEA) (fun h9 => by omega)
    have hpf : p ∣ 2 ^ f - 1 := by
      rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hRM.2.1
    exact ⟨t, ht, g, split_of_rowDeg hrr hpf hdeg, hKF⟩

end CFSG.RankThree.PartOne.S15K
