module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3TenGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1614e3_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s1614e3_pow_eq_one_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

private theorem s1614e3_isElemAbelian_of_rank {X : Type*} [Group X] {p n : ℕ}
    {E : Subgroup X} (h : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (congrArg Subtype.val (s1614e3_comm_of_elem h a b))⟩⟩,
    fun x hx => by
      simpa using congrArg Subtype.val (s1614e3_pow_eq_one_of_elem h ⟨x, hx⟩)⟩

theorem s1614e3_row10_rk (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (h10 : Case168_10At D ⊥ V hV L p) : 8 ≤ rk (Vtil ⊥ V hV) := by
  classical
  obtain ⟨Y, hY⟩ := s16t_ten_blocks_of_case168_10 D h1217 hc hp h10
  have hrkT : rk (Vtil ⊥ V hV) = Fintype.card (Fin 4) * dParam p := by
    have h1 := rk_iSup_biSup_eq_sum Y hY.blocks.indep Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset (Fin 4)), Y i : Subgroup (Vtil ⊥ V hV)) = ⊤ := by
      rw [← hY.blocks.sup]
      simp
    rw [h2, rk_top] at h1
    rw [h1]
    simp [hY.blocks.rank]
  have hd2 : 2 ≤ dParam p := by
    rcases hp with rfl | rfl
    · rw [s16c1610_dParam_three]
    · rw [s16c1610_dParam_seven]
      norm_num
  rw [hrkT, Fintype.card_fin 4]
  omega

theorem s1614e3_row10_hrow (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) {p : ℕ} (hp : p = 3 ∨ p = 7)
    (h10 : Case168_10At D ⊥ V hV L p) :
    ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        ∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B := by
  classical
  intro t htM ht2 hkt W hWC hW
  obtain ⟨Y, hY⟩ := s16t_ten_blocks_of_case168_10 D h1217 hc hp h10
  obtain ⟨hcyc, hrk, hs, hσ, hF⟩ := h10
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hpσ : p ∈ D.sig := by rw [hσ]; exact Set.mem_singleton p
  have hT2 : ∀ x : Vtil ⊥ V hV, x ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hFel : IsElemAbelian p (fstarBar D.M ⊥ V hV) := s1614e3_isElemAbelian_of_rank hF
  have hB : ∀ i, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)), B ≤ Mbar D.M ⊥ V hV ∧
      IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ ∀ y ∈ Y i, y ∈ fixV B := by
    intro i
    have hBel : IsElemAbelian p (fstarBar D.M ⊥ V hV ⊓ centSub (Y i)) := hFel.mono inf_le_left
    have hBM : fstarBar D.M ⊥ V hV ⊓ centSub (Y i) ≤ Mbar D.M ⊥ V hV :=
      inf_le_left.trans (Subgroup.map_subtype_le _)
    refine ⟨fstarBar D.M ⊥ V hV ⊓ centSub (Y i), hBM, hBel.isPGroup, ?_, ?_⟩
    · intro hcyc'
      haveI : Fintype ↥(fstarBar D.M ⊥ V hV ⊓ centSub (Y i)) := Fintype.ofFinite _
      haveI : IsCyclic ↥(fstarBar D.M ⊥ V hV ⊓ centSub (Y i)) := hcyc'
      have hle : Fintype.card ↥(fstarBar D.M ⊥ V hV ⊓ centSub (Y i)) ≤ p := by
        have h := IsCyclic.card_pow_eq_one_le
          (α := ↥(fstarBar D.M ⊥ V hV ⊓ centSub (Y i))) hpp.pos
        have hall : (Finset.univ.filter fun a : ↥(fstarBar D.M ⊥ V hV ⊓ centSub (Y i)) =>
            a ^ p = 1) = Finset.univ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact Subtype.ext (hBel.2 a a.2)
        rwa [hall, Finset.card_univ] at h
      rw [← Nat.card_eq_fintype_card, hY.card_ker i] at hle
      have h2 := hpp.two_le
      nlinarith
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
  have hn : 3 ≤ Fintype.card (Fin 4) := by norm_num
  obtain ⟨z, hzW, hz1, B, hBM, hBp, hBc, hzB⟩ := s1614_frame_hrow (T := Vtil ⊥ V hV) hT2
    hY.blocks.indep hY.blocks.inj hY.blocks.sup (d := dParam p) (e := D.k + 2) hY.blocks.rank hd2
    hke hn (hY.blocks.perm t htM) (by omega) hB hWC hW
  exact ⟨z, hzW, hz1, p, hpσ, B, hBM, hBp, hBc, hzB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
