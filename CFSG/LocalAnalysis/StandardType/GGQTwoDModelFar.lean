module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelCommute

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)

private lemma pmfar_label_three_symm (m : ℕ) {i j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 :=
  ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j).trans h

private lemma pmfar_label_two (m : ℕ) (hm : 3 ≤ m) {i j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2) :
    i ≠ j ∧
      ¬ (j.val = i.val + 1 ∧ j.val ≤ m - 1) ∧
      ¬ (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∧
      ¬ (i.val + 2 = m ∧ j.val = m) ∧
      ¬ (j.val + 2 = m ∧ i.val = m) := by
  have hij : i ≠ j := ((ggCoxeterMatrixD_eq_two_iff (by omega : 4 ≤ m + 1) i j).mp h).1
  have h' := (qtwoLabel_two_iff hm i j hij).mp h
  simp only [not_or] at h'
  exact ⟨hij, h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩

private theorem pmfar_nodeEdge_lt
    (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)
    (i j k : Fin (m + 1)) (hjk : j < k)
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 2) :
    ∀ x ∈ qtwoStdU E m hm i, ∀ y ∈ qtwoStdW E m hm j k, x * y = y * x := by
  intro x hx y hy
  have hltv : j.val < k.val := by
    rw [Fin.lt_def] at hjk
    exact hjk
  rcases (qtwoLabel_three_iff hm j k).mp h1 with
    ⟨hk1, hk2⟩ | ⟨hj1, hj2⟩ | ⟨hf1, hf2⟩ | ⟨hj3, hj4⟩
  ·
    have ha : j.val + 2 ≤ m := by omega
    rw [qtwoStdW_chain E m hm j.val ha j k rfl hk1] at hy
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    ·
      rw [qtwoStdU_castSucc] at hx
      obtain ⟨-, h2A, h2B, -, -⟩ := pmfar_label_two m hm h2
      obtain ⟨-, h3A, h3B, -, -⟩ := pmfar_label_two m hm h3
      rw [Fin.val_castSucc] at h2A h2B h3A h3B
      have e1 : j.val ≠ i'.val + 1 := fun h => h2A ⟨h, by omega⟩
      have e2 : i'.val ≠ j.val + 1 := fun h => h2B ⟨h, by omega⟩
      have e3 : k.val ≠ i'.val + 1 := fun h => h3A ⟨h, by omega⟩
      have e4 : i'.val ≠ k.val + 1 := fun h => h3B ⟨h, by omega⟩
      exact qtwoStd_comm_win_win (m := m) (a := i'.val) (k := 2) (b := j.val) (l := 3)
        (by omega) (by omega) (by omega) x y hx hy
    ·
      rw [qtwoStdU_last] at hx
      obtain ⟨-, -, -, h2C, h2D⟩ := pmfar_label_two m hm h2
      obtain ⟨-, -, -, h3C, h3D⟩ := pmfar_label_two m hm h3
      rw [Fin.val_last] at h2C h2D h3C h3D
      have e1 : j.val + 2 ≠ m := fun h => h2D ⟨h, rfl⟩
      have e2 : k.val + 2 ≠ m := fun h => h3D ⟨h, rfl⟩
      exact qtwoStd_comm_twist_win E (m := m) (a := m - 1) (k := 2) (b := j.val) (l := 3)
        (by omega) (by omega) (by omega) x y hx hy
  · omega
  ·
    rw [qtwoStdW_fork E m hm j k (by omega) hf2] at hy
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    ·
      rw [qtwoStdU_castSucc] at hx
      obtain ⟨-, h2A, h2B, -, -⟩ := pmfar_label_two m hm h2
      obtain ⟨-, -, -, h3C, -⟩ := pmfar_label_two m hm h3
      rw [Fin.val_castSucc] at h2A h2B h3C
      have e1 : i'.val ≠ m - 3 := fun h => h2A ⟨by omega, by omega⟩
      have e2 : i'.val ≠ m - 1 := fun h => h2B ⟨by omega, by omega⟩
      have e3 : i'.val ≠ m - 2 := fun h => h3C ⟨by omega, hf2⟩
      exact (qtwoStd_comm_twist_win E (m := m) (a := m - 2) (k := 3) (b := i'.val) (l := 2)
        (by omega) (by omega) (by omega) y x hy hx).symm
    ·
      exfalso
      have hk_eq : k = Fin.last m := Fin.ext hf2
      rw [hk_eq, qtwoLabel_self] at h3
      omega
  · omega

private theorem pmfar_edgeEdge_lt
    (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)
    (i k j l : Fin (m + 1)) (hik : i < k) (hjl : j < l)
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j l = 3)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    (h4 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i l = 2)
    (h5 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k j = 2)
    (h6 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k l = 2) :
    ∀ x ∈ qtwoStdW E m hm i k, ∀ y ∈ qtwoStdW E m hm j l, x * y = y * x := by
  intro x hx y hy
  have hikv : i.val < k.val := by
    rw [Fin.lt_def] at hik
    exact hik
  have hjlv : j.val < l.val := by
    rw [Fin.lt_def] at hjl
    exact hjl
  rcases (qtwoLabel_three_iff hm i k).mp h1 with
    ⟨hi1, hi2⟩ | ⟨hi3, hi4⟩ | ⟨hi5, hi6⟩ | ⟨hi7, hi8⟩
  ·
    have hia : i.val + 2 ≤ m := by omega
    rw [qtwoStdW_chain E m hm i.val hia i k rfl hi1] at hx
    rcases (qtwoLabel_three_iff hm j l).mp h2 with
      ⟨hj1, hj2⟩ | ⟨hj3, hj4⟩ | ⟨hf1, hf2⟩ | ⟨hj7, hj8⟩
    ·
      have hja : j.val + 2 ≤ m := by omega
      rw [qtwoStdW_chain E m hm j.val hja j l rfl hj1] at hy
      obtain ⟨-, h3A, h3B, -, -⟩ := pmfar_label_two m hm h3
      obtain ⟨-, h4A, h4B, -, -⟩ := pmfar_label_two m hm h4
      obtain ⟨-, h5A, h5B, -, -⟩ := pmfar_label_two m hm h5
      have e1 : j.val ≠ i.val + 1 := fun h => h3A ⟨h, by omega⟩
      have e2 : i.val ≠ j.val + 1 := fun h => h3B ⟨h, by omega⟩
      have e3 : i.val ≠ j.val := fun h => h4A ⟨by omega, by omega⟩
      have e4 : i.val ≠ j.val + 2 := fun h => h4B ⟨by omega, by omega⟩
      have e5 : j.val ≠ i.val + 2 := fun h => h5A ⟨by omega, by omega⟩
      exact qtwoStd_comm_win_win (m := m) (a := i.val) (k := 3) (b := j.val) (l := 3)
        (by omega) (by omega) (by omega) x y hx hy
    · omega
    ·
      rw [qtwoStdW_fork E m hm j l (by omega) hf2] at hy
      obtain ⟨-, h3A, h3B, -, h3D⟩ := pmfar_label_two m hm h3
      obtain ⟨-, -, h4B, h4C, -⟩ := pmfar_label_two m hm h4
      obtain ⟨-, h5A, h5B, -, -⟩ := pmfar_label_two m hm h5
      obtain ⟨-, -, -, h6C, -⟩ := pmfar_label_two m hm h6
      have f1 : i.val ≠ m - 3 := fun h => h3A ⟨by omega, by omega⟩
      have f2 : i.val ≠ m - 1 := fun h => h3B ⟨by omega, by omega⟩
      have f3 : i.val ≠ m - 2 := fun h => h4C ⟨by omega, hf2⟩
      have f4 : i.val ≠ m - 4 := fun h => h5A ⟨by omega, by omega⟩
      have f5 : i.val ≠ m - 2 := fun h => h5B ⟨by omega, by omega⟩
      have f6 : i.val ≠ m - 3 := fun h => h6C ⟨by omega, hf2⟩
      exact (qtwoStd_comm_twist_win E (m := m) (a := m - 2) (k := 3) (b := i.val) (l := 3)
        (by omega) (by omega) (by omega) y x hy hx).symm
    · omega
  · omega
  ·
    rw [qtwoStdW_fork E m hm i k (by omega) hi6] at hx
    rcases (qtwoLabel_three_iff hm j l).mp h2 with
      ⟨hj1, hj2⟩ | ⟨hj3, hj4⟩ | ⟨hf1, hf2⟩ | ⟨hj7, hj8⟩
    ·
      have hja : j.val + 2 ≤ m := by omega
      rw [qtwoStdW_chain E m hm j.val hja j l rfl hj1] at hy
      obtain ⟨-, h3A, h3B, h3C, -⟩ := pmfar_label_two m hm h3
      obtain ⟨-, h4A, h4B, h4C, -⟩ := pmfar_label_two m hm h4
      obtain ⟨-, -, -, -, h5D⟩ := pmfar_label_two m hm h5
      obtain ⟨-, -, -, -, h6D⟩ := pmfar_label_two m hm h6
      have g1 : j.val ≠ m - 1 := fun h => h3A ⟨by omega, by omega⟩
      have g2 : j.val ≠ m - 3 := fun h => h3B ⟨by omega, by omega⟩
      have g3 : j.val ≠ m := fun h => h3C ⟨by omega, h⟩
      have g4 : j.val ≠ m - 2 := fun h => h4A ⟨by omega, by omega⟩
      have g5 : j.val ≠ m - 4 := fun h => h4B ⟨by omega, by omega⟩
      have g6 : j.val ≠ m - 1 := fun h => h4C ⟨by omega, by omega⟩
      have g7 : j.val ≠ m - 2 := fun h => h5D ⟨by omega, hi6⟩
      have g8 : j.val ≠ m - 3 := fun h => h6D ⟨by omega, hi6⟩
      exact qtwoStd_comm_twist_win E (m := m) (a := m - 2) (k := 3) (b := j.val) (l := 3)
        (by omega) (by omega) (by omega) x y hx hy
    · omega
    ·
      exfalso
      have hjeq : j = i := by
        apply Fin.ext
        omega
      rw [hjeq, qtwoLabel_self] at h3
      omega
    · omega
  · omega

theorem qtwoStd_farNodeEdge (i j k : Fin (m + 1))
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 2) :
    ∀ x ∈ qtwoStdU E m hm i, ∀ y ∈ qtwoStdW E m hm j k, x * y = y * x := by
  have hjk_ne : j ≠ k := by
    intro h
    rw [h, qtwoLabel_self] at h1
    omega
  intro x hx y hy
  by_cases hlt : j < k
  · exact pmfar_nodeEdge_lt E m hm i j k hlt h1 h2 h3 x hx y hy
  · have hkj : k < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hjk_ne)
    have hy' : y ∈ qtwoStdW E m hm k j := by
      rw [← qtwoStdW_symm E m hm j k]
      exact hy
    exact pmfar_nodeEdge_lt E m hm i k j hkj (pmfar_label_three_symm m h1) h3 h2 x hx y hy'

theorem qtwoStd_farEdgeEdge (i k j l : Fin (m + 1))
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 3)
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j l = 3)
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    (h4 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i l = 2)
    (h5 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k j = 2)
    (h6 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k l = 2) :
    ∀ x ∈ qtwoStdW E m hm i k, ∀ y ∈ qtwoStdW E m hm j l, x * y = y * x := by
  have hik_ne : i ≠ k := by
    intro h
    rw [h, qtwoLabel_self] at h1
    omega
  have hjl_ne : j ≠ l := by
    intro h
    rw [h, qtwoLabel_self] at h2
    omega
  intro x hx y hy
  by_cases hik : i < k
  · by_cases hjl : j < l
    · exact pmfar_edgeEdge_lt E m hm i k j l hik hjl h1 h2 h3 h4 h5 h6 x hx y hy
    · have hlj : l < j := lt_of_le_of_ne (le_of_not_gt hjl) (Ne.symm hjl_ne)
      have hy' : y ∈ qtwoStdW E m hm l j := by
        rw [← qtwoStdW_symm E m hm j l]
        exact hy
      exact pmfar_edgeEdge_lt E m hm i k l j hik hlj h1 (pmfar_label_three_symm m h2)
        h4 h3 h6 h5 x hx y hy'
  · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hik) (Ne.symm hik_ne)
    have hx' : x ∈ qtwoStdW E m hm k i := by
      rw [← qtwoStdW_symm E m hm i k]
      exact hx
    have h1' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k i = 3 :=
      pmfar_label_three_symm m h1
    by_cases hjl : j < l
    · exact pmfar_edgeEdge_lt E m hm k i j l hki hjl h1' h2 h5 h6 h3 h4 x hx' y hy
    · have hlj : l < j := lt_of_le_of_ne (le_of_not_gt hjl) (Ne.symm hjl_ne)
      have hy' : y ∈ qtwoStdW E m hm l j := by
        rw [← qtwoStdW_symm E m hm j l]
        exact hy
      exact pmfar_edgeEdge_lt E m hm k i l j hki hlj h1' (pmfar_label_three_symm m h2)
        h6 h5 h4 h3 x hx' y hy'

end CFSG.StandardType.QTwo

end
