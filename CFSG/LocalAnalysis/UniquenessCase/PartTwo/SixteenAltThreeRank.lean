module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s168e3_named_three_mQuot_sum
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (tau : MulAut W)
    (S : Fin 3 → Subgroup W) (Q : Subgroup W)
    (hJoin : (⨆ i : Fin 3, S i) = Q)
    (hInd : ∀ i : Fin 3, S i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S j) = ⊥)
    (hStable : ∀ i : Fin 3, (S i).map tau.toMonoidHom = S i) :
    E3.mQuot Q (Q ⊓ fixV (Subgroup.zpowers tau)) =
      E3.mQuot (S 0) (S 0 ⊓ fixV (Subgroup.zpowers tau)) +
      E3.mQuot (S 1) (S 1 ⊓ fixV (Subgroup.zpowers tau)) +
      E3.mQuot (S 2) (S 2 ⊓ fixV (Subgroup.zpowers tau)) := by
  have h01 : S 0 ⊓ S 1 = ⊥ := by
    have hle : S 1 ≤ ⨆ (j : Fin 3) (_ : j ≠ 0), S j :=
      le_iSup₂ (f := fun j : Fin 3 => fun _ : j ≠ 0 => S j) 1 (by decide)
    have h := inf_le_inf (le_refl (S 0)) hle
    rw [hInd 0] at h
    exact le_bot_iff.mp h
  have hle0 : S 0 ≤ ⨆ (j : Fin 3) (_ : j ≠ 2), S j :=
    le_iSup₂ (f := fun j : Fin 3 => fun _ : j ≠ 2 => S j) 0 (by decide)
  have hle1 : S 1 ≤ ⨆ (j : Fin 3) (_ : j ≠ 2), S j :=
    le_iSup₂ (f := fun j : Fin 3 => fun _ : j ≠ 2 => S j) 1 (by decide)
  have h012 : (S 0 ⊔ S 1) ⊓ S 2 = ⊥ := by
    have hle : S 0 ⊔ S 1 ≤ ⨆ (j : Fin 3) (_ : j ≠ 2), S j := sup_le hle0 hle1
    have h := inf_le_inf (le_refl (S 2)) hle
    rw [hInd 2] at h
    rw [inf_comm]
    exact le_bot_iff.mp h
  have hsupStable : (S 0 ⊔ S 1).map tau.toMonoidHom = S 0 ⊔ S 1 := by
    rw [Subgroup.map_sup, hStable 0, hStable 1]
  have hsplit1 := s16c167_mQuot_sup_split hW tau (A := S 0) (B := S 1) h01
    (hStable 0) (hStable 1)
  have hsplit2 := s16c167_mQuot_sup_split hW tau (A := S 0 ⊔ S 1) (B := S 2) h012
    hsupStable (hStable 2)
  have hjoin : (S 0 ⊔ S 1) ⊔ S 2 = Q := by
    rw [← hJoin]
    apply le_antisymm
    · exact sup_le (sup_le (le_iSup S 0) (le_iSup S 1)) (le_iSup S 2)
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_trans le_sup_left le_sup_left
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right
  rw [← hjoin, hsplit2, hsplit1]

theorem s168e3_two_block_three_rank_allocation
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (tau : MulAut W) (htau : tau ≠ 1)
    {Q1 Q2 : Subgroup W} (S1 S2 : Fin 3 → Subgroup W)
    (hQinf : Q1 ⊓ Q2 = ⊥) (hQsup : Q1 ⊔ Q2 = ⊤)
    (hQ1 : Q1.map tau.toMonoidHom = Q1) (hQ2 : Q2.map tau.toMonoidHom = Q2)
    (hJoin1 : (⨆ i : Fin 3, S1 i) = Q1) (hJoin2 : (⨆ i : Fin 3, S2 i) = Q2)
    (hInd1 : ∀ i : Fin 3, S1 i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S1 j) = ⊥)
    (hInd2 : ∀ i : Fin 3, S2 i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S2 j) = ⊥)
    (hS1 : ∀ i : Fin 3, (S1 i).map tau.toMonoidHom = S1 i)
    (hS2 : ∀ i : Fin 3, (S2 i).map tau.toMonoidHom = S2 i)
    (hUniform1 : ∀ i : Fin 3, S1 i ≤ fixV (Subgroup.zpowers tau) →
      Q1 ≤ fixV (Subgroup.zpowers tau))
    (hUniform2 : ∀ i : Fin 3, S2 i ≤ fixV (Subgroup.zpowers tau) →
      Q2 ≤ fixV (Subgroup.zpowers tau))
    (hRank : rkIdx (fixV (Subgroup.zpowers tau)) ≤ 3) :
    let F := fixV (Subgroup.zpowers tau)
    rkIdx F = 3 ∧
      (((¬ Q1 ≤ F) ∧ E3.mQuot Q1 (Q1 ⊓ F) = 3 ∧
        (∀ i : Fin 3, (¬ S1 i ≤ F) ∧ E3.mQuot (S1 i) (S1 i ⊓ F) = 1) ∧
        Q2 ≤ F ∧ E3.mQuot Q2 (Q2 ⊓ F) = 0) ∨
       ((¬ Q2 ≤ F) ∧ E3.mQuot Q2 (Q2 ⊓ F) = 3 ∧
        (∀ i : Fin 3, (¬ S2 i ≤ F) ∧ E3.mQuot (S2 i) (S2 i ⊓ F) = 1) ∧
        Q1 ≤ F ∧ E3.mQuot Q1 (Q1 ⊓ F) = 0)) := by
  let F := fixV (Subgroup.zpowers tau)
  have hD1 : E3.mQuot Q1 (Q1 ⊓ F) =
      E3.mQuot (S1 0) (S1 0 ⊓ F) + E3.mQuot (S1 1) (S1 1 ⊓ F) +
        E3.mQuot (S1 2) (S1 2 ⊓ F) := by
    simpa only [F] using s168e3_named_three_mQuot_sum hW tau S1 Q1 hJoin1 hInd1 hS1
  have hD2 : E3.mQuot Q2 (Q2 ⊓ F) =
      E3.mQuot (S2 0) (S2 0 ⊓ F) + E3.mQuot (S2 1) (S2 1 ⊓ F) +
        E3.mQuot (S2 2) (S2 2 ⊓ F) := by
    simpa only [F] using s168e3_named_three_mQuot_sum hW tau S2 Q2 hJoin2 hInd2 hS2
  have hsplit : rkIdx F = E3.mQuot Q1 (Q1 ⊓ F) + E3.mQuot Q2 (Q2 ⊓ F) := by
    simpa only [F] using s16c167_rkIdx_fixV_split hW tau hQinf hQsup hQ1 hQ2
  have hRankF : rkIdx F ≤ 3 := by simpa only [F] using hRank
  have hnon1 : ¬ Q1 ≤ F → ∀ i : Fin 3, ¬ S1 i ≤ F := by
    intro hQ i hS
    apply hQ
    have hfix : S1 i ≤ fixV (Subgroup.zpowers tau) := by simpa only [F] using hS
    have := hUniform1 i hfix
    simpa only [F] using this
  have hnon2 : ¬ Q2 ≤ F → ∀ i : Fin 3, ¬ S2 i ≤ F := by
    intro hQ i hS
    apply hQ
    have hfix : S2 i ≤ fixV (Subgroup.zpowers tau) := by simpa only [F] using hS
    have := hUniform2 i hfix
    simpa only [F] using this
  have hD1ge : ¬ Q1 ≤ F → 3 ≤ E3.mQuot Q1 (Q1 ⊓ F) := by
    intro hQ
    have h0 : 1 ≤ E3.mQuot (S1 0) (S1 0 ⊓ F) := by
      have h : ¬ S1 0 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon1 hQ 0
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S1 0) h
    have h1 : 1 ≤ E3.mQuot (S1 1) (S1 1 ⊓ F) := by
      have h : ¬ S1 1 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon1 hQ 1
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S1 1) h
    have h2 : 1 ≤ E3.mQuot (S1 2) (S1 2 ⊓ F) := by
      have h : ¬ S1 2 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon1 hQ 2
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S1 2) h
    omega
  have hD2ge : ¬ Q2 ≤ F → 3 ≤ E3.mQuot Q2 (Q2 ⊓ F) := by
    intro hQ
    have h0 : 1 ≤ E3.mQuot (S2 0) (S2 0 ⊓ F) := by
      have h : ¬ S2 0 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon2 hQ 0
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S2 0) h
    have h1 : 1 ≤ E3.mQuot (S2 1) (S2 1 ⊓ F) := by
      have h : ¬ S2 1 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon2 hQ 1
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S2 1) h
    have h2 : 1 ≤ E3.mQuot (S2 2) (S2 2 ⊓ F) := by
      have h : ¬ S2 2 ≤ fixV (Subgroup.zpowers tau) := by
        simpa only [F] using hnon2 hQ 2
      simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S2 2) h
    omega
  have hsome : ¬ Q1 ≤ F ∨ ¬ Q2 ≤ F := by
    by_contra h
    simp only [not_or, not_not] at h
    obtain ⟨h1, h2⟩ := h
    have htop : F = ⊤ := by
      have hle : (⊤ : Subgroup W) ≤ F := by
        rw [← hQsup]
        exact sup_le h1 h2
      exact top_le_iff.mp hle
    apply htau
    ext w
    have hw : w ∈ F := by rw [htop]; exact Subgroup.mem_top w
    have hw' : w ∈ fixV (Subgroup.zpowers tau) := by simpa only [F] using hw
    exact (mem_fixV_zpowers tau w).mp hw'
  have hnotboth : ¬ (¬ Q1 ≤ F ∧ ¬ Q2 ≤ F) := by
    rintro ⟨h1, h2⟩
    have h1ge := hD1ge h1
    have h2ge := hD2ge h2
    omega
  have hD2zero : Q2 ≤ F → E3.mQuot Q2 (Q2 ⊓ F) = 0 := by
    intro hQ
    rw [inf_eq_left.mpr hQ]
    exact E3.mQuot_self Q2
  have hD1zero : Q1 ≤ F → E3.mQuot Q1 (Q1 ⊓ F) = 0 := by
    intro hQ
    rw [inf_eq_left.mpr hQ]
    exact E3.mQuot_self Q1
  have hFthree : rkIdx F = 3 := by
    rcases hsome with h1 | h2
    · have h2le : Q2 ≤ F := by
        by_contra h
        exact hnotboth ⟨h1, h⟩
      have hz := hD2zero h2le
      have hge := hD1ge h1
      omega
    · have h1le : Q1 ≤ F := by
        by_contra h
        exact hnotboth ⟨h, h2⟩
      have hz := hD1zero h1le
      have hge := hD2ge h2
      omega
  refine ⟨hFthree, ?_⟩
  by_cases hQ1a : Q1 ≤ F
  · right
    have hQ2a : ¬ Q2 ≤ F := by
      rcases hsome with h | h
      · exact absurd hQ1a h
      · exact h
    have hD2three : E3.mQuot Q2 (Q2 ⊓ F) = 3 := by
      have := hD2ge hQ2a
      omega
    have hd2 : ∀ i : Fin 3, E3.mQuot (S2 i) (S2 i ⊓ F) = 1 := by
      have hge : ∀ i : Fin 3, 1 ≤ E3.mQuot (S2 i) (S2 i ⊓ F) := by
        intro i
        have h : ¬ S2 i ≤ fixV (Subgroup.zpowers tau) := by
          simpa only [F] using hnon2 hQ2a i
        simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S2 i) h
      have hg0 := hge 0
      have hg1 := hge 1
      have hg2 := hge 2
      have h0 : E3.mQuot (S2 0) (S2 0 ⊓ F) = 1 := by omega
      have h1 : E3.mQuot (S2 1) (S2 1 ⊓ F) = 1 := by omega
      have h2 : E3.mQuot (S2 2) (S2 2 ⊓ F) = 1 := by omega
      intro i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    have hD1z := hD1zero hQ1a
    exact ⟨hQ2a, hD2three, fun i => ⟨hnon2 hQ2a i, hd2 i⟩, hQ1a, hD1z⟩
  · left
    have hQ1a' : ¬ Q1 ≤ F := hQ1a
    have hQ2le : Q2 ≤ F := by
      by_contra hQ2a
      exact hnotboth ⟨hQ1a', hQ2a⟩
    have hD1three : E3.mQuot Q1 (Q1 ⊓ F) = 3 := by
      have := hD1ge hQ1a'
      omega
    have hd1 : ∀ i : Fin 3, E3.mQuot (S1 i) (S1 i ⊓ F) = 1 := by
      have hge : ∀ i : Fin 3, 1 ≤ E3.mQuot (S1 i) (S1 i ⊓ F) := by
        intro i
        have h : ¬ S1 i ≤ fixV (Subgroup.zpowers tau) := by
          simpa only [F] using hnon1 hQ1a' i
        simpa only [F] using s16c167_one_le_mQuot_of_not_le hW tau (A := S1 i) h
      have hg0 := hge 0
      have hg1 := hge 1
      have hg2 := hge 2
      have h0 : E3.mQuot (S1 0) (S1 0 ⊓ F) = 1 := by omega
      have h1 : E3.mQuot (S1 1) (S1 1 ⊓ F) = 1 := by omega
      have h2 : E3.mQuot (S1 2) (S1 2 ⊓ F) = 1 := by omega
      intro i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    have hD2z := hD2zero hQ2le
    exact ⟨hQ1a', hD1three, fun i => ⟨hnon1 hQ1a' i, hd1 i⟩, hQ2le, hD2z⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
