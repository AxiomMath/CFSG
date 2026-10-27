module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagMoveAux
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPos

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.ClassicalInvolution.Phan.PhanE

open Classical

variable {K : Type} [Field K] {m : ℕ}

theorem hasPos_adj {E F F' : FlagK K (m + 1)} {i : Fin m} {σ : Equiv.Perm (Fin (m + 1))}
    (hadj : (flagSys K m).adj i F F') (h : HasPos E F σ) :
    HasPos E F' σ ∨ HasPos E F' (adjSwap i * σ) := by
  classical
  have hPQ : F.E i.val ≤ F.E (i.val + 2) := F.mono (by omega)
  have hPM' : F.E i.val ≤ F'.E (i.val + 1) :=
    (hadj i.val (by omega)).trans_le (F'.mono (by omega))
  have hM'Q : F'.E (i.val + 1) ≤ F.E (i.val + 2) := by
    rw [hadj (i.val + 2) (by omega)]
    exact F'.mono (by omega)
  have hM'dim : finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1 :=
    q2cFM_dim_replace F F' i
  have hQdim : finrank K ↥(F.E (i.val + 2)) = finrank K ↥(F.E i.val) + 2 := by
    rw [F.dim (i.val + 2) (by omega), F.dim i.val (by omega)]
  have hs := q2cFM_s_formula (E := E) (F := F) (i := i) (σ := σ) h
  have ha₂ : max (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val + 1 ≤ m + 1 := by
    have h1 := (σ⁻¹ i.castSucc).isLt
    have h2 := (σ⁻¹ i.succ).isLt
    omega
  have hmem := q2cFM_jump_mem (E := E) (P := F.E i.val) (Q := F.E (i.val + 2))
      (M := F'.E (i.val + 1)) hPM' hM'Q hPQ hQdim hM'dim q2cFM_huv hs ha₂
  rcases lt_or_gt_of_ne q2cFM_huv with huvlt | huvgt
  · rcases hmem with hj | hj
    · exact Or.inl (q2cFM_hasPos_left hadj h hPM' hM'Q hPQ hM'dim
        (by rwa [min_eq_left (le_of_lt huvlt)] at hj))
    · exact Or.inr (q2cFM_hasPos_right hadj h hPM' hM'Q hPQ hM'dim
        (by rwa [max_eq_right (le_of_lt huvlt)] at hj))
  · rcases hmem with hj | hj
    · exact Or.inr (q2cFM_hasPos_right hadj h hPM' hM'Q hPQ hM'dim
        (by rwa [min_eq_right (le_of_lt huvgt)] at hj))
    · exact Or.inl (q2cFM_hasPos_left hadj h hPM' hM'Q hPQ hM'dim
        (by rwa [max_eq_left (le_of_lt huvgt)] at hj))

theorem hasPos_adj_of_lt {E F F' : FlagK K (m + 1)} {i : Fin m}
    {σ : Equiv.Perm (Fin (m + 1))} (hadj : (flagSys K m).adj i F F') (hne : F ≠ F')
    (h : HasPos E F σ) (hlt : σ⁻¹ i.castSucc < σ⁻¹ i.succ) :
    HasPos E F' (adjSwap i * σ) := by
  classical
  have hlt' : (σ⁻¹ i.castSucc).val < (σ⁻¹ i.succ).val := hlt
  have hPQ : F.E i.val ≤ F.E (i.val + 2) := F.mono (by omega)
  have hPM' : F.E i.val ≤ F'.E (i.val + 1) :=
    (hadj i.val (by omega)).trans_le (F'.mono (by omega))
  have hM'Q : F'.E (i.val + 1) ≤ F.E (i.val + 2) := by
    rw [hadj (i.val + 2) (by omega)]
    exact F'.mono (by omega)
  have hM'dim : finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1 :=
    q2cFM_dim_replace F F' i
  have hQdim : finrank K ↥(F.E (i.val + 2)) = finrank K ↥(F.E i.val) + 2 := by
    rw [F.dim (i.val + 2) (by omega), F.dim i.val (by omega)]
  have hs := q2cFM_s_formula (E := E) (F := F) (i := i) (σ := σ) h
  have ha₂ : max (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val + 1 ≤ m + 1 := by
    have h1 := (σ⁻¹ i.castSucc).isLt
    have h2 := (σ⁻¹ i.succ).isLt
    omega
  have hj0 := q2cFM_jump_self (E := E) (F := F) (i := i) (σ := σ) h
  have hmem := q2cFM_jump_mem (E := E) (P := F.E i.val) (Q := F.E (i.val + 2))
    (M := F'.E (i.val + 1)) hPM' hM'Q hPQ hQdim hM'dim q2cFM_huv hs ha₂
  rw [min_eq_left (le_of_lt hlt'), max_eq_right (le_of_lt hlt')] at hmem
  rcases hmem with hj | hj
  · exfalso
    apply hne
    have hSdim : finrank K
        ↥((E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val) =
        finrank K ↥(F.E i.val) + 1 := by
      rw [hs ((σ⁻¹ i.castSucc).val + 1) (by omega),
        q2cFM_ind_sum_one (u := (σ⁻¹ i.castSucc).val) (v := (σ⁻¹ i.succ).val)
          (a := (σ⁻¹ i.castSucc).val + 1) (by omega) (by omega)]
    have hM'le : F'.E (i.val + 1) ≤
        (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val := by
      have := q2cFM_jump_spec E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) hM'Q hPQ
      rwa [hj] at this
    have hM0le : F.E (i.val + 1) ≤
        (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val := by
      have := q2cFM_jump_spec E (F.E i.val) (F.E (i.val + 2)) (F.E (i.val + 1))
        (F.mono (by omega)) hPQ
      rwa [hj0] at this
    have hM'eq : F'.E (i.val + 1) =
        (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val :=
      Submodule.eq_of_le_of_finrank_eq hM'le (by rw [hSdim, hM'dim])
    have hM0eq : F.E (i.val + 1) =
        (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val :=
      Submodule.eq_of_le_of_finrank_eq hM0le (by rw [hSdim, q2cFM_dim_replace F F i])
    have hFF' : F' = F := by
      apply FlagK.ext
      intro j
      by_cases hji : j = i.val + 1
      · rw [hji]; exact hM'eq.trans hM0eq.symm
      · exact (hadj j hji).symm
    exact hFF'.symm
  · exact q2cFM_hasPos_right hadj h hPM' hM'Q hPQ hM'dim hj

theorem exists_adj_hasPos (E F : FlagK K (m + 1)) (i : Fin m) {σ : Equiv.Perm (Fin (m + 1))}
    (h : HasPos E F σ) : ∃ F', (flagSys K m).adj i F F' ∧ HasPos E F' (adjSwap i * σ) := by
  classical
  have hPQ : F.E i.val ≤ F.E (i.val + 2) := F.mono (by omega)
  have hQdim : finrank K ↥(F.E (i.val + 2)) = finrank K ↥(F.E i.val) + 2 := by
    rw [F.dim (i.val + 2) (by omega), F.dim i.val (by omega)]
  have hs := q2cFM_s_formula (E := E) (F := F) (i := i) (σ := σ) h
  have ha₂ : max (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val + 1 ≤ m + 1 := by
    have h1 := (σ⁻¹ i.castSucc).isLt
    have h2 := (σ⁻¹ i.succ).isLt
    omega
  have hN : ∃ N : Submodule K (Fin (m + 1) → K),
      F.E i.val ≤ N ∧ N ≤ F.E (i.val + 2) ∧ finrank K N = i.val + 1 ∧
        q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) N = (σ⁻¹ i.succ).val + 1 := by
    rcases lt_or_gt_of_ne q2cFM_huv with huvlt | huvgt
    ·
      have hSdim₁ : finrank K
          ↥((E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val) =
          finrank K ↥(F.E i.val) + 1 := by
        have h1 : min (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val < (σ⁻¹ i.castSucc).val + 1 := by
          rw [min_eq_left (le_of_lt huvlt)]; omega
        have h2 : (σ⁻¹ i.castSucc).val + 1 ≤
            max (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val := by
          rw [max_eq_right (le_of_lt huvlt)]; omega
        rw [hs ((σ⁻¹ i.castSucc).val + 1) (by omega),
          q2cFM_ind_sum_one (u := (σ⁻¹ i.castSucc).val) (v := (σ⁻¹ i.succ).val)
            (a := (σ⁻¹ i.castSucc).val + 1) h1 h2]
      have hproper : ¬ F.E (i.val + 2) ≤
          (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val := by
        intro hle
        have := Submodule.finrank_mono hle
        rw [hSdim₁, hQdim] at this
        omega
      have hnotall : ¬ ∀ q : Fin (m + 1) → K, q ∈ F.E (i.val + 2) →
          q ∈ (E.E ((σ⁻¹ i.castSucc).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val := hproper
      rw [not_forall] at hnotall
      obtain ⟨q, hq⟩ := hnotall
      rw [not_imp] at hq
      obtain ⟨hqQ, hqS⟩ := hq
      have hq0 : q ≠ 0 := by
        intro hq0; exact hqS (hq0 ▸ Submodule.zero_mem _)
      have hqP : q ∉ F.E i.val := fun hqP => hqS (Submodule.mem_sup_right hqP)
      have hNdim : finrank K ↥(F.E i.val ⊔ K ∙ q) = i.val + 1 := by
        have hdisj : F.E i.val ⊓ K ∙ q = ⊥ := by
          rw [← disjoint_iff]
          exact Submodule.disjoint_span_singleton_of_notMem hqP
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq (F.E i.val) (K ∙ q)
        rw [hdisj, finrank_bot, finrank_span_singleton hq0, F.dim i.val (by omega),
          add_zero] at hsup
        omega
      have hNQ : F.E i.val ⊔ K ∙ q ≤ F.E (i.val + 2) :=
        sup_le hPQ ((Submodule.span_singleton_le_iff_mem _ _).mpr hqQ)
      refine ⟨F.E i.val ⊔ K ∙ q, le_sup_left, hNQ, hNdim, ?_⟩
      have hjmem := q2cFM_jump_mem (E := E) (P := F.E i.val) (Q := F.E (i.val + 2))
        (M := F.E i.val ⊔ K ∙ q) le_sup_left hNQ hPQ hQdim
        (by rw [hNdim, F.dim i.val (by omega)]) q2cFM_huv hs ha₂
      rw [min_eq_left (le_of_lt huvlt), max_eq_right (le_of_lt huvlt)] at hjmem
      rcases hjmem with hj | hj
      · exfalso
        have hspec := q2cFM_jump_spec E (F.E i.val) (F.E (i.val + 2)) (F.E i.val ⊔ K ∙ q) hNQ hPQ
        rw [hj] at hspec
        exact hqS (hspec (Submodule.mem_sup_right (Submodule.subset_span (by simp))))
      · exact hj
    · have hNQ : (E.E ((σ⁻¹ i.succ).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val ≤
          F.E (i.val + 2) := sup_le inf_le_right hPQ
      have hNdim : finrank K
          ↥((E.E ((σ⁻¹ i.succ).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val) = i.val + 1 := by
        have h1 : min (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val < (σ⁻¹ i.succ).val + 1 := by
          rw [min_eq_right (le_of_lt huvgt)]; omega
        have h2 : (σ⁻¹ i.succ).val + 1 ≤
            max (σ⁻¹ i.castSucc).val (σ⁻¹ i.succ).val := by
          rw [max_eq_left (le_of_lt huvgt)]; omega
        rw [hs ((σ⁻¹ i.succ).val + 1) (by omega),
          q2cFM_ind_sum_one (u := (σ⁻¹ i.castSucc).val) (v := (σ⁻¹ i.succ).val)
            (a := (σ⁻¹ i.succ).val + 1) h1 h2,
          F.dim i.val (by omega)]
      refine ⟨(E.E ((σ⁻¹ i.succ).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val,
        le_sup_right, hNQ, hNdim, ?_⟩
      have hjmem := q2cFM_jump_mem (E := E) (P := F.E i.val) (Q := F.E (i.val + 2))
        (M := (E.E ((σ⁻¹ i.succ).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val)
        le_sup_right hNQ hPQ hQdim (by rw [hNdim, F.dim i.val (by omega)]) q2cFM_huv hs ha₂
      rw [min_eq_right (le_of_lt huvgt), max_eq_left (le_of_lt huvgt)] at hjmem
      rcases hjmem with hj | hj
      · exact hj
      · exfalso
        have hle := q2cFM_jump_min' E (F.E i.val) (F.E (i.val + 2))
          ((E.E ((σ⁻¹ i.succ).val + 1) ⊓ F.E (i.val + 2)) ⊔ F.E i.val) hNQ le_rfl
        omega
  obtain ⟨N, hPN, hNQ, hNdim, hNj⟩ := hN
  let F' := q2cFM_replaceFlag F i N hPN hNQ hNdim
  have hF'E : F'.E (i.val + 1) = N := q2cFM_replaceFlag_E F i N hPN hNQ hNdim
  have hF'PM : F.E i.val ≤ F'.E (i.val + 1) := by rw [hF'E]; exact hPN
  have hF'Q : F'.E (i.val + 1) ≤ F.E (i.val + 2) := by rw [hF'E]; exact hNQ
  have hF'dim : finrank K ↥(F'.E (i.val + 1)) = finrank K ↥(F.E i.val) + 1 := by
    rw [hF'E, hNdim, F.dim i.val (by omega)]
  have hF'j : q2cFM_jump E (F.E i.val) (F.E (i.val + 2)) (F'.E (i.val + 1)) =
      (σ⁻¹ i.succ).val + 1 := by rw [hF'E]; exact hNj
  exact ⟨F', q2cFM_replaceFlag_adj F i N hPN hNQ hNdim,
    q2cFM_hasPos_right (q2cFM_replaceFlag_adj F i N hPN hNQ hNdim) h hF'PM hF'Q hPQ hF'dim hF'j⟩

theorem relPos_adj {E F F' : FlagK K (m + 1)} {i : Fin m}
    (hadj : (flagSys K m).adj i F F') :
    relPos E F' = relPos E F ∨ relPos E F' = adjSwap i * relPos E F := by
  rcases hasPos_adj hadj (hasPos_relPos E F) with h | h
  · exact Or.inl (hasPos_iff.mp h)
  · exact Or.inr (hasPos_iff.mp h)

theorem relPos_eq_adjSwap_iff (E F : FlagK K (m + 1)) (i : Fin m) :
    relPos E F = adjSwap i ↔ E ≠ F ∧ (flagSys K m).adj i E F := by
  constructor
  · intro hrel
    have hne : E ≠ F := by
      intro heq
      exact q2cFM_adjSwap_ne_one i (by rw [← hrel, heq, relPos_self])
    refine ⟨hne, ?_⟩
    intro j hj
    by_cases hjm : j ≤ m + 1
    · have hpos : HasPos E F (adjSwap i) := hasPos_iff.mpr hrel
      have hrk := hpos j j hjm hjm
      simp only [rk] at hrk
      rw [q2cFM_permRk_adjSwap_self i hjm hj] at hrk
      have hE := E.dim j hjm
      have hF := F.dim j hjm
      have heq : E.E j ⊓ F.E j = E.E j :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hrk, hE])
      exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp heq) (by rw [hE, hF])
    · have htop : m + 1 ≤ j := by omega
      rw [E.top j htop, F.top j htop]
  · rintro ⟨hne, hadj⟩
    rcases relPos_adj (E := E) (F := E) (F' := F) hadj with h | h
    · rw [relPos_self] at h
      exact absurd ((relPos_eq_one_iff E F).mp h) hne
    · rwa [relPos_self, mul_one] at h

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
