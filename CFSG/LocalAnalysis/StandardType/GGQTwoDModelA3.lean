module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelCommute
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem pma3_window_union {n a : ℕ} (ha : a + 4 ≤ n) :
    ((Finset.univ.map (SixPoint.qTwoSixWinEmb (m := n) (k := 3) (i := a)
        (show a + 3 ≤ n by omega))) : Finset (Fin n)) ∪
      (Finset.univ.map (SixPoint.qTwoSixWinEmb (m := n) (k := 3) (i := a + 1)
        (show a + 1 + 3 ≤ n by omega))) =
    Finset.univ.map (SixPoint.qTwoSixWinEmb (m := n) (k := 4) (i := a) ha) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · refine ⟨⟨y.val, by omega⟩, ?_⟩
      ext
      rw [SixPoint.qTwoSixWinEmb_val, Fin.val_mk]
      have := congrArg Fin.val hy
      simp only [SixPoint.qTwoSixWinEmb_val] at this
      omega
    · refine ⟨⟨y.val + 1, by omega⟩, ?_⟩
      ext
      rw [SixPoint.qTwoSixWinEmb_val, Fin.val_mk]
      have := congrArg Fin.val hy
      simp only [SixPoint.qTwoSixWinEmb_val] at this
      omega
  · rintro ⟨y, hy⟩
    rcases lt_or_ge y.val 3 with h | h
    · left
      refine ⟨⟨y.val, h⟩, ?_⟩
      ext
      rw [SixPoint.qTwoSixWinEmb_val, Fin.val_mk]
      have := congrArg Fin.val hy
      simp only [SixPoint.qTwoSixWinEmb_val] at this
      omega
    · right
      have hy3 : y.val = 3 := by have := y.isLt; omega
      refine ⟨⟨2, by norm_num⟩, ?_⟩
      ext
      rw [SixPoint.qTwoSixWinEmb_val, Fin.val_mk]
      have := congrArg Fin.val hy
      simp only [SixPoint.qTwoSixWinEmb_val] at this
      omega

theorem blockEmb_range_four (hK : Nat.card K = 4) {n a : ℕ} (ha : a + 4 ≤ n) :
    (blockEmb K 2 1 n 4 a ha).range =
      (blockEmb K 2 1 n 3 a (by omega)).range ⊔
        (blockEmb K 2 1 n 3 (a + 1) (by omega)).range := by
  rw [SixPoint.qTwoSixWin_range (K := K) (m := n) (k := 4) (i := a) ha,
    SixPoint.qTwoSixWin_range (K := K) (m := n) (k := 3) (i := a) (by omega),
    SixPoint.qTwoSixWin_range (K := K) (m := n) (k := 3) (i := a + 1) (by omega),
    ← pma3_window_union (n := n) (a := a) ha]
  exact (coordBlockSU_sup_three (K := K) hK
    (A := Finset.univ.map (SixPoint.qTwoSixWinEmb (m := n) (k := 3) (i := a) (by omega)))
    (B := Finset.univ.map (SixPoint.qTwoSixWinEmb (m := n) (k := 3) (i := a + 1) (by omega)))
    (by simp) (by simp)
    (by rw [pma3_window_union (n := n) (a := a) ha]; simp)).symm

theorem blockEmb_three_sup_eq_top (hK : Nat.card K = 4) :
    (blockEmb K 2 1 4 3 0 (by norm_num)).range ⊔ (blockEmb K 2 1 4 3 1 (by norm_num)).range =
      ⊤ := by
  have hmap : (Finset.univ.map (SixPoint.qTwoSixWinEmb (m := 4) (k := 4) (i := 0)
      (by norm_num)) : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rw [Finset.mem_map]
    exact ⟨x, Finset.mem_univ x, by ext; rw [SixPoint.qTwoSixWinEmb_val]; simp⟩
  have h := blockEmb_range_four (K := K) hK (n := 4) (a := 0) (by norm_num)
  rw [← h, SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 4) (i := 0) (by norm_num),
    hmap, SixPoint.qTwoSixWin_coordBlockSU_univ (K := K) 4]

end Gen

section Chain

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

private theorem pma3_map_eq_of_fixed {G : Type} [Group G] (c : G →* G) (R : Subgroup G)
    (h : ∀ x ∈ R, c x = x) : R.map c = R := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [h x hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, h y hy⟩

theorem qtwoStdWin_range_four (hK : Nat.card K = 4) (m a : ℕ) (ha : a + 4 ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a 4 ha).range =
      (qtwoStdWin (F := F) (K := K) m a 3 (by omega)).range ⊔
        (qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega)).range := by
  simp only [qtwoStdWin]
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    blockEmb_range_four (K := K) hK (n := m + 1) (a := a) (by omega), Subgroup.map_sup]

variable (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)

private theorem pma3_qtwoStdWin_three_congr {m a a' : ℕ} (ha : a = a')
    (h : a + 3 ≤ m + 1) (h' : a' + 3 ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a 3 h).range =
      (qtwoStdWin (F := F) (K := K) m a' 3 h').range := by
  subst ha
  rfl

theorem qtwoStd_A3_chain (hK : Nat.card K = 4) (a : ℕ) (ha : a + 3 ≤ m) (i j k : Fin (m + 1))
    (hi : i.val = a) (hj : j.val = a + 1) (hk : k.val = a + 2) :
    ∃ θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)),
      θ.range = qtwoStdW E m hm i j ⊔ qtwoStdW E m hm j k := by
  refine ⟨qtwoStdWin (F := F) (K := K) m a 4 (by omega), ?_⟩
  rw [qtwoStdWin_range_four (K := K) hK (m := m) (a := a) (by omega),
    qtwoStdW_chain (F := F) (K := K) E m hm a (by omega) i j hi hj,
    qtwoStdW_chain (F := F) (K := K) E m hm (a + 1) (by omega) j k hj hk]

theorem qtwoStd_A3_twisted (hK : Nat.card K = 4) (i j k : Fin (m + 1)) (hi : i.val = m - 3)
    (hj : j.val = m - 2) (hk : k.val = m) :
    ∃ θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)),
      θ.range = qtwoStdW E m hm i j ⊔ qtwoStdW E m hm j k := by
  have hR1 : (qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega)).range.map
      (stdConj E m).toMonoidHom =
      (qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega)).range := by
    apply pma3_map_eq_of_fixed
    rintro x ⟨A, rfl⟩
    exact qtwoStdConj_win (F := F) (K := K) E (a := m - 3) (k := 3) (by omega) A
  have hB_eq : (qtwoStdWin (F := F) (K := K) m ((m - 3) + 1) 3 (by omega)).range =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range :=
    pma3_qtwoStdWin_three_congr (F := F) (K := K) (m := m)
      (show (m - 3) + 1 = m - 2 by omega) (by omega) (by omega)
  refine ⟨(stdConj E m).toMonoidHom.comp
    (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega)), ?_⟩
  rw [MonoidHom.range_comp,
    qtwoStdWin_range_four (K := K) hK (m := m) (a := m - 3) (by omega),
    Subgroup.map_sup, hB_eq, hR1,
    qtwoStdW_chain (F := F) (K := K) E m hm (m - 3) (by omega) i j hi
      (show j.val = (m - 3) + 1 by omega),
    qtwoStdW_fork (F := F) (K := K) E m hm j k hj hk]

end Chain

end CFSG.StandardType.QTwo

end
