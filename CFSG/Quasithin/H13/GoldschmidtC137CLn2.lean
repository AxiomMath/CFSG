module

public import CFSG.Quasithin.H13.GoldschmidtC137CLn1
public import CFSG.Quasithin.H13.GoldschmidtC137Ln2Aux
public import CFSG.Quasithin.H13.GoldschmidtC137CPt2
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin6

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem line_conj (hP : autI h.hVe P = H2.map F.ρ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 P) A) {h' : Gp 6} (hh' : h' ∈ H2)
    {K : Subgroup (Gp 6)} (hAK : autI h.hVe A = K.map F.ρ) :
    ∃ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 P) A' ∧
      autI h.hVe A' = (cj h' K).map F.ρ := by
  have hρ : F.ρ h' ∈ autI h.hVe P := by
    rw [hP]
    exact ⟨h', hh', rfl⟩
  obtain ⟨g, hgP, hg⟩ := (mem_autI h.hVe).1 hρ
  refine ⟨cjSub g A, isMaxElemAbelian_cjSub
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hgP) hA, ?_⟩
  rw [← autI_cjSub h.hVe g.2, hg, hAK, ← F.conjAut_map_ρ, conjAut_eq_map_gc]

theorem line_Z_all (hP : autI h.hVe P = H2.map F.ρ)
    (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    (∃ A, IsMaxElemAbelian (pCoreOf 2 P) A ∧ autI h.hVe A = Z0.map F.ρ) ∧
    (∃ A, IsMaxElemAbelian (pCoreOf 2 P) A ∧ autI h.hVe A = Z2.map F.ρ) ∧
    (∃ A, IsMaxElemAbelian (pCoreOf 2 P) A ∧ autI h.hVe A = Z1.map F.ρ) := by
  obtain ⟨A, hA⟩ := h.exists_offender hJ
  have hmax := hA.1
  rcases F.line_offender_cases hR h5 hA with hi | hi | hi
  · obtain ⟨⟨k2, hk2, hc2⟩, ⟨k1, hk1, hc1⟩⟩ := exists_H2_conj_Z0
    refine ⟨⟨A, hmax, hi⟩, ?_, ?_⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk2 hi
      exact ⟨A', hA', by rw [e, hc2]⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk1 hi
      exact ⟨A', hA', by rw [e, hc1]⟩
  · obtain ⟨⟨k0, hk0, hc0⟩, ⟨k1, hk1, hc1⟩⟩ := exists_H2_conj_Z2
    refine ⟨?_, ⟨A, hmax, hi⟩, ?_⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk0 hi
      exact ⟨A', hA', by rw [e, hc0]⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk1 hi
      exact ⟨A', hA', by rw [e, hc1]⟩
  · obtain ⟨⟨k2, hk2, hc2⟩, ⟨k0, hk0, hc0⟩⟩ := exists_H2_conj_Z1
    refine ⟨?_, ?_, ⟨A, hmax, hi⟩⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk0 hi
      exact ⟨A', hA', by rw [e, hc0]⟩
    · obtain ⟨A', hA', e⟩ := F.line_conj hP hmax hk2 hi
      exact ⟨A', hA', by rw [e, hc2]⟩

theorem line_J_eq (hP : autI h.hVe P = H2.map F.ρ) (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    autI h.hVe (thompsonJ (pCoreOf 2 P)) = R2.map F.ρ := by
  obtain ⟨⟨A0, hA0, e0⟩, ⟨A2, hA2, e2⟩, ⟨A1, hA1, e1⟩⟩ := F.line_Z_all hP hR h5 hJ
  have hle : ∀ {A' : Subgroup G}, IsMaxElemAbelian (pCoreOf 2 P) A' →
      autI h.hVe A' ≤ autI h.hVe (thompsonJ (pCoreOf 2 P)) := fun hA' =>
    autI_mono h.hVe (le_iSup₂_of_le _ hA' le_rfl)
  apply le_antisymm
  · rw [← hR]
    exact autI_mono h.hVe (thompsonJ_le_self _)
  · calc R2.map F.ρ ≤ (Z0 ⊔ Z2 ⊔ Z1).map F.ρ := Subgroup.map_mono R2_le_sup
      _ = Z0.map F.ρ ⊔ Z2.map F.ρ ⊔ Z1.map F.ρ := by rw [Subgroup.map_sup, Subgroup.map_sup]
      _ ≤ _ := sup_le (sup_le (e0 ▸ hle hA0) (e2 ▸ hle hA2)) (e1 ▸ hle hA1)

theorem line_no_strong (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2) :
    ∀ A : Subgroup G, ¬ IsStrongFFOffender h.hVe (pCoreOf 2 P) A := by
  intro A hA
  have hr : rAV (autI h.hVe A) = 1 := by
    rcases F.line_offender_cases hR h5 hA.1 with e | e | e
    · rw [e, F.rAV_ρ]
      exact rAV_of_rank rank_Z0
    · rw [e, F.rAV_ρ]
      exact rAV_of_rank rank_Z2
    · rw [e, F.rAV_ρ]
      exact rAV_of_rank rank_Z1
  have := hA.2.2
  rw [hr] at this
  exact lt_irrefl _ this

theorem line_hDE (hP : autI h.hVe P = H2.map F.ρ) (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V h.hVe))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hVe L, B1.conjAut g (Y i) ≤ autI h.hVe (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hVe (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hVe (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hVe L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hVe L)) ∧
      ∀ A, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V h.hVe))),
          A = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hVe L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hVe (pCoreOf 2 P) := by
  have hJR : autI h.hVe (thompsonJ (pCoreOf 2 P)) = autI h.hVe (pCoreOf 2 P) :=
    (F.line_J_eq hP hR h5 hJ).trans hR.symm
  obtain ⟨⟨A0, hA0, e0⟩, -, -⟩ := F.line_Z_all hP hR h5 hJ
  have hc : ∀ i : Fin 2, ![F.ρ c2L, F.ρ c3L] i ∈ autI h.hVe L := by
    intro i
    rw [← F.hA]
    fin_cases i
    · exact ⟨c2L, c2L_even, rfl⟩
    · exact ⟨c3L, c3L_even, rfl⟩
  refine hDE_of_pieces h.hVe h.hXN h.hLX h.R_le_X
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) h.toBaum.hA2 hJR (m := 2) (fun _ => A0)
    (fun _ => hA0) ![F.ρ c2L, F.ρ c3L] hc ?_ ?_
  · simp only [e0]
    rw [hR, ← F.hA]
    have h2 : B1.conjAut (F.ρ c2L) (Z0.map F.ρ) ≤ ⨆ i : Fin 2,
        B1.conjAut (![F.ρ c2L, F.ρ c3L] i) (Z0.map F.ρ) :=
      le_iSup (fun i : Fin 2 => B1.conjAut (![F.ρ c2L, F.ρ c3L] i) (Z0.map F.ρ)) 0
    have h3 : B1.conjAut (F.ρ c3L) (Z0.map F.ρ) ≤ ⨆ i : Fin 2,
        B1.conjAut (![F.ρ c2L, F.ρ c3L] i) (Z0.map F.ρ) :=
      le_iSup (fun i : Fin 2 => B1.conjAut (![F.ρ c2L, F.ρ c3L] i) (Z0.map F.ρ)) 1
    rw [F.conjAut_map_ρ] at h2 h3
    calc (alternatingGroup (Fin 6)).map F.ρ ≤ (R2 ⊔ cj c2L Z0 ⊔ cj c3L Z0).map F.ρ := by
          rw [R2_sup_eq_top]
          exact Subgroup.map_mono le_top
      _ = R2.map F.ρ ⊔ (cj c2L Z0).map F.ρ ⊔ (cj c3L Z0).map F.ρ := by
          rw [Subgroup.map_sup, Subgroup.map_sup]
      _ ≤ _ := sup_le (sup_le le_sup_left (h2.trans le_sup_right)) (h3.trans le_sup_right)
  · simp only [Fin.sum_univ_two, e0]
    rw [hR, ← F.hA, F.rkIdx_fixV_ρ, F.rkIdx_fixV_ρ, F.rkIdx_fixV_ρ, rank_R2.2, rank_Z0.2,
      rkIdx_A6]
    norm_num


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
