module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1614_row4_rk (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h4 : Case168_4With D ⊥ V hV L 3) : 8 ≤ rk (Vtil ⊥ V hV) := by
  classical
  obtain ⟨p, hp, h4At⟩ := h4
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, -, -⟩ := s16n9b_case4_data h4At.2.1
  letI := hι
  have hrkT : rk (Vtil ⊥ V hV) = Fintype.card ι * dParam p := by
    have h1 := rk_iSup_biSup_eq_sum Y hind Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset ι), Y i : Subgroup (Vtil ⊥ V hV)) = ⊤ := by
      rw [← hsup]
      simp
    rw [h2, rk_top] at h1
    rw [h1]
    simp [hrk]
  have hd2 : 2 ≤ dParam p := by
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three]
    · rw [s16c1610_dParam_seven]
      norm_num
  rw [hrkT, hcard]
  omega

theorem s1614_row4_hrow (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    (h4 : Case168_4With D ⊥ V hV L 3)
    (hge : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p (Mbar D.M ⊥ V hV)) :
    ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        ∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B := by
  classical
  intro t htM ht2 hkt W hWC hW
  obtain ⟨p, hp, h4At⟩ := h4
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hT2 : ∀ x : Vtil ⊥ V hV, x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hpσ : p ∈ D.sig := h4At.2.2
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data h4At.2.1
  letI := hι
  obtain ⟨F, hFX, hFel, hFcard, hFY, -⟩ := s16n9b_case4_kernel hT2 hp (by norm_num : 1 < 3)
    h4At.1 (s16n9b_case4_pcore D hV hc hpp (by norm_num) h4At.1) (hge p hpσ) hind hinj hsup
    hcard hrk hperm hsurj
  have hB : ∀ i, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)), B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧
      ¬ IsCyclic ↥B ∧ ∀ y ∈ Y i, y ∈ fixV B := by
    intro i
    have hidx := s16n9b_case4_aut_index_le hp hT2 (hrk i) hFel (fun f hf => hFY f hf i)
    have hBel : IsElemAbelian p (F ⊓ centSub (Y i)) := hFel.mono inf_le_left
    refine ⟨F ⊓ centSub (Y i), inf_le_left.trans hFX, hBel.isPGroup, ?_, ?_⟩
    · intro hcyc
      haveI : Fintype ↥(F ⊓ centSub (Y i)) := Fintype.ofFinite _
      have hle : Fintype.card ↥(F ⊓ centSub (Y i)) ≤ p := by
        have h := IsCyclic.card_pow_eq_one_le (α := ↥(F ⊓ centSub (Y i))) hpp.pos
        have hall : (Finset.univ.filter fun a : ↥(F ⊓ centSub (Y i)) => a ^ p = 1) =
            Finset.univ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact Subtype.ext (hBel.2 a a.2)
        rwa [hall, Finset.card_univ] at h
      rw [← Nat.card_eq_fintype_card] at hle
      have h1 : p ^ 3 ≤ p * p := hFcard.trans (hidx.trans (Nat.mul_le_mul_left p hle))
      have h2 := hpp.two_le
      nlinarith [Nat.mul_pos hpp.pos hpp.pos]
    · intro y hy
      exact mem_fixV.2 fun b hb => mem_centSub.1 hb.2 y hy
  have hd2 : 2 ≤ dParam p := by
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three]
    · rw [s16c1610_dParam_seven]
      norm_num
  have hke : D.k + 2 ≤ dParam p + 1 := by
    rcases hp with rfl | rfl
    · have := s16c1610_k_lt_dParam_three D hSg h1219 hpσ
      omega
    · rw [s16c1610_dParam_seven]
      have := s16c167_k_le_two D
      omega
  have hn : 3 ≤ Fintype.card ι := by
    rw [hcard]
    omega
  obtain ⟨z, hzW, hz1, B, hBM, hBp, hBc, hzB⟩ := s1614_frame_hrow (T := Vtil ⊥ V hV) hT2 hind
    hinj hsup (d := dParam p) (e := D.k + 2) hrk hd2 hke hn (hperm t htM) (by omega) hB hWC hW
  exact ⟨z, hzW, hz1, p, hpσ, B, hBM, hBp, hBc, hzB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
