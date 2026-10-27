module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrCaseThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614_row3_hrow (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L) (hk1 : D.k = 1)
    (hpr : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV)) :
    ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        ∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B := by
  classical
  intro t htM ht2 hkt W hWC hW
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V hV x
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hWcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  have hMN := s16c167_mbar_le_normalizer_lbar D hV hc h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAM, hAab, hA27⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3) hpr
  have hA27' : Nat.card ↥A = 27 := by
    rw [hA27]
    norm_num
  have ht2' : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨Y, hind, hinj, hsup, hrk, hperm, hB⟩ :=
    s1614_torus_frame hWsq hWcard h3.1 hMN ⟨A, hAM, hAab, hA27'⟩ htM ht2'
  have hD3 : (3 : ℕ) ∈ D.sig := by
    rw [h3.2.2]
    exact Set.mem_singleton 3
  obtain ⟨z, hzW, hz1, B, hBM, hB3, hBnc, hzB⟩ := s1614_frame_hrow (T := Vtil ⊥ V hV)
    (fun x => by rw [pow_two]; exact hWsq x) hind hinj hsup (d := 2) (e := D.k + 2) hrk le_rfl
    (by omega) (by simp) hperm (by omega) hB hWC hW
  exact ⟨z, hzW, hz1, 3, hD3, B, hBM, hB3, hBnc, hzB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
