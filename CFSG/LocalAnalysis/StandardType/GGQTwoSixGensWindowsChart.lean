module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G]

@[expose] def qTwoSixWin_adj (φ : Fin 3 → Su K 2 1 4 →* G) : Prop :=
  ∀ (s : Fin 2) (x : Su K 2 1 3),
    φ s.castSucc (qTwoSixWin_left (K := K) x) =
      φ s.succ (qTwoSixWin_right (K := K) x)

theorem qTwoSixWin_adj_of_overlap {φ : Fin 3 → Su K 2 1 4 →* G}
    (a01 : ∀ x : Su K 2 1 3,
      φ 0 (qTwoSixWin_left (K := K) x) = φ 1 (qTwoSixWin_right (K := K) x))
    (a12 : ∀ x : Su K 2 1 3,
      φ 1 (qTwoSixWin_left (K := K) x) = φ 2 (qTwoSixWin_right (K := K) x)) :
    qTwoSixWin_adj φ := by
  intro s x
  fin_cases s
  · simpa using a01 x
  · simpa using a12 x

theorem qTwoSixWin_adj_lifts (hK : Nat.card K = 4) (s : Fin 2) (i : Fin 18)
    (h0 : qTwoSixData_inWindow s.castSucc i)
    (h1 : qTwoSixData_inWindow s.succ i) :
    ∃ y : Su K 2 1 3,
      qTwoSixWin_lift hK s.castSucc i = qTwoSixWin_left (K := K) y ∧
      qTwoSixWin_lift hK s.succ i = qTwoSixWin_right (K := K) y := by
  have h3 : (s.val + 1) + 3 ≤ 6 := by
    have := s.isLt
    omega
  have hsub : qTwoSixData_support i ⊆ Finset.univ.map (qTwoSixWinEmb h3) := by
    intro a ha
    have h0a := h0 a ha
    have h1a := h1 a ha
    have hlt : a.val < s.val + 4 := by
      simpa only [Fin.val_castSucc] using h0a.2
    have hge : s.val + 1 ≤ a.val := by
      simpa only [Fin.val_succ] using h1a.1
    rw [Finset.mem_map]
    refine ⟨⟨a.val - (s.val + 1), by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    rw [qTwoSixWinEmb_val]
    dsimp only
    omega
  have hmem : nativeSu hK i ∈
      coordBlockSU K 2 1 (Finset.univ.map (qTwoSixWinEmb h3)) :=
    qTwoS34_coordBlockSU_mono hsub (qTwoSixData_native_mem hK i)
  rw [← qTwoSixWin_range h3] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hleft : qTwoSixWin_lift hK s.castSucc i = qTwoSixWin_left (K := K) y := by
    apply qTwoSixWin_emb_injective s.castSucc
    calc blockEmb K 2 1 6 4 (s.castSucc).val (qTwoSixWin_hs s.castSucc)
          (qTwoSixWin_lift hK s.castSucc i)
        = nativeSu hK i :=
          qTwoSixWin_lift_eq hK s.castSucc i (qTwoSixWin_hs s.castSucc) h0
      _ = blockEmb K 2 1 6 3 (s.val + 1) h3 y := hy.symm
      _ = blockEmb K 2 1 6 4 (s.castSucc).val (qTwoSixWin_hs s.castSucc)
            (qTwoSixWin_left (K := K) y) := by
          rw [qTwoSixWin_left]
          exact (blockEmb_comp_apply (K := K) (p := 2) (f := 1)
            (m := 6) (k := 4) (l := 3) (i := s.val) (j := 1)
            (qTwoSixWin_hs s.castSucc) (by omega) y).symm
  have hright : qTwoSixWin_lift hK s.succ i = qTwoSixWin_right (K := K) y := by
    apply qTwoSixWin_emb_injective s.succ
    calc blockEmb K 2 1 6 4 (s.succ).val (qTwoSixWin_hs s.succ)
          (qTwoSixWin_lift hK s.succ i)
        = nativeSu hK i :=
          qTwoSixWin_lift_eq hK s.succ i (qTwoSixWin_hs s.succ) h1
      _ = blockEmb K 2 1 6 3 (s.val + 1) h3 y := hy.symm
      _ = blockEmb K 2 1 6 4 (s.succ).val (qTwoSixWin_hs s.succ)
            (qTwoSixWin_right (K := K) y) := by
          rw [qTwoSixWin_right]
          exact (blockEmb_comp_apply (K := K) (p := 2) (f := 1)
            (m := 6) (k := 4) (l := 3) (i := s.val + 1) (j := 0)
            (qTwoSixWin_hs s.succ) (by omega) y).symm
  exact ⟨y, hleft, hright⟩

theorem qTwoSixWin_adj_agree (hK : Nat.card K = 4)
    {φ : Fin 3 → Su K 2 1 4 →* G} (hadj : qTwoSixWin_adj φ)
    (s : Fin 2) (i : Fin 18)
    (h0 : qTwoSixData_inWindow s.castSucc i)
    (h1 : qTwoSixData_inWindow s.succ i) :
    φ s.castSucc (qTwoSixWin_lift hK s.castSucc i) =
      φ s.succ (qTwoSixWin_lift hK s.succ i) := by
  obtain ⟨y, hleft, hright⟩ := qTwoSixWin_adj_lifts hK s i h0 h1
  calc φ s.castSucc (qTwoSixWin_lift hK s.castSucc i)
      = φ s.castSucc (qTwoSixWin_left (K := K) y) := by rw [hleft]
    _ = φ s.succ (qTwoSixWin_right (K := K) y) := hadj s y
    _ = φ s.succ (qTwoSixWin_lift hK s.succ i) := by rw [hright]

theorem qTwoSixWin_mid_window {i : Fin 18}
    (h0 : qTwoSixData_inWindow 0 i) (h2 : qTwoSixData_inWindow 2 i) :
    qTwoSixData_inWindow 1 i := by
  intro j hj
  have h0j := h0 j hj
  have h2j := h2 j hj
  omega

@[expose] noncomputable def qTwoSixWin_chart (i : Fin 18) : Fin 3 :=
  Classical.choose (qTwoSixData_window_exists i)

theorem qTwoSixWin_chart_spec (i : Fin 18) :
    qTwoSixData_inWindow (qTwoSixWin_chart i) i :=
  Classical.choose_spec (qTwoSixData_window_exists i)

theorem qTwoSixWin_chart_agree (hK : Nat.card K = 4)
    {φ : Fin 3 → Su K 2 1 4 →* G} (hadj : qTwoSixWin_adj φ)
    (s t : Fin 3) (i : Fin 18)
    (hs : qTwoSixData_inWindow s i) (ht : qTwoSixData_inWindow t i) :
    φ s (qTwoSixWin_lift hK s i) = φ t (qTwoSixWin_lift hK t i) := by
  fin_cases s <;> fin_cases t
  · rfl
  · simpa using qTwoSixWin_adj_agree hK hadj 0 i hs ht
  · have hmid : qTwoSixData_inWindow 1 i := qTwoSixWin_mid_window hs ht
    simpa using (qTwoSixWin_adj_agree hK hadj 0 i hs hmid).trans
      (qTwoSixWin_adj_agree hK hadj 1 i hmid ht)
  · simpa using (qTwoSixWin_adj_agree hK hadj 0 i ht hs).symm
  · rfl
  · simpa using qTwoSixWin_adj_agree hK hadj 1 i hs ht
  · have hmid : qTwoSixData_inWindow 1 i := qTwoSixWin_mid_window ht hs
    simpa using ((qTwoSixWin_adj_agree hK hadj 0 i ht hmid).trans
      (qTwoSixWin_adj_agree hK hadj 1 i hmid hs)).symm
  · simpa using (qTwoSixWin_adj_agree hK hadj 1 i ht hs).symm
  · rfl

@[expose] noncomputable def qTwoSixWin_g (hK : Nat.card K = 4)
    (φ : Fin 3 → Su K 2 1 4 →* G) : Fin 18 → G := fun i =>
  φ (qTwoSixWin_chart i) (qTwoSixWin_lift hK (qTwoSixWin_chart i) i)

theorem qTwoSixWin_g_eq (hK : Nat.card K = 4)
    {φ : Fin 3 → Su K 2 1 4 →* G}
    (a01 : ∀ x : Su K 2 1 3,
      φ 0 (qTwoSixWin_left (K := K) x) = φ 1 (qTwoSixWin_right (K := K) x))
    (a12 : ∀ x : Su K 2 1 3,
      φ 1 (qTwoSixWin_left (K := K) x) = φ 2 (qTwoSixWin_right (K := K) x))
    (s : Fin 3) (i : Fin 18) (hin : qTwoSixData_inWindow s i) :
    qTwoSixWin_g hK φ i = φ s (qTwoSixWin_lift hK s i) := by
  change φ (qTwoSixWin_chart i)
      (qTwoSixWin_lift hK (qTwoSixWin_chart i) i) =
    φ s (qTwoSixWin_lift hK s i)
  exact qTwoSixWin_chart_agree hK (qTwoSixWin_adj_of_overlap a01 a12)
    (qTwoSixWin_chart i) s i (qTwoSixWin_chart_spec i) hin

theorem qTwoSixWin_g_mem_blk (hK : Nat.card K = 4)
    {H : Subgroup G}
    {φ : Fin 3 → Su K 2 1 4 →* G}
    (a01 : ∀ x : Su K 2 1 3,
      φ 0 (qTwoSixWin_left (K := K) x) = φ 1 (qTwoSixWin_right (K := K) x))
    (a12 : ∀ x : Su K 2 1 3,
      φ 1 (qTwoSixWin_left (K := K) x) = φ 2 (qTwoSixWin_right (K := K) x))
    {B : QTwoCanonBlocks K 5 6 H}
    (hchart : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s))
    (i : Fin 18) :
    qTwoSixWin_g hK φ i ∈ B.blk (qTwoSixData_support i) := by
  have hin : qTwoSixData_inWindow (qTwoSixWin_chart i) i := qTwoSixWin_chart_spec i
  rw [qTwoSixWin_g_eq hK a01 a12 (qTwoSixWin_chart i) i hin]
  have hcard := qTwoSixWin_supp_card (s := qTwoSixWin_chart i) (i := i) hin
  have hsupp := qTwoSixData_support_card i
  have hJ2 : 2 ≤ (qTwoSixWin_supp (qTwoSixWin_chart i) i).card := by
    rw [hcard]
    exact hsupp.1
  have hblk := (hchart (qTwoSixWin_chart i)).2
    (qTwoSixWin_supp (qTwoSixWin_chart i) i) hJ2
  rw [← qTwoSixWin_supp_map hin, hblk]
  exact Subgroup.mem_map.mpr
    ⟨_, qTwoSixWin_lift_mem hK (qTwoSixWin_chart i) i hin, rfl⟩

end CFSG.StandardType.QTwo.SixPoint

end
