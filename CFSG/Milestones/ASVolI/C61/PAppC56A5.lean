module

public import CFSG.Milestones.ASVolI.C61.PAppCExcl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl
public import CFSG.Milestones.ASVolI.C61.PAppCCls3

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem c56A5Case {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (hcs : burnsideC56_CS G T M H S L) (h5 : IsAltType L 5) (hj : conjJoin S L = L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    C56_7Concl S H L M₀ := by
  obtain ⟨C⟩ := nonempty_cfg hcs hj h5
  have hne : S ≠ M₀ := fun h => by
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have m₀ : Mate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hU0 : blockU0 S L = blockU L := A5.blockU0_eq_blockU hj
  have hBD : baumD S L = blockD S L := Mate.baumD_eq (m := m₀) C
  refine ⟨?_, ?_, hBD, ?_, Mate.Q_isMax (m := m₀) C, (Mate.J_eq_B (m := m₀) C).symm, ?_⟩
  · rw [hU0, hj]
    exact (Mate.blockQ_eq_blockU (m := m₀) C).symm
  · rw [hBD]
    exact Mate.D_elem (m := m₀) C
  · rw [hBD, hU0, sup_comm]
    exact C.Q_eq
  · intro x hx hxS
    have m : Mate S T M₀ x := ⟨hSM, hMT, h2, hx, hxS⟩
    have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (Mate.V_le_S (m := m) C).trans C.hSN
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hBD]
      exact Mate.D_inf_conj (m := m) C
    · rw [hBD, hU0]
      exact Mate.B_eq (m := m) C
    · intro _ hty
      exfalso
      rcases hty with h3 | ⟨n, hn, hlin⟩
      · exact not_alt3_of_alt5 h5 h3
      · exact not_lin2_of_alt5 C.hL h5 hn hlin
    · intro _ _ r hr hrB
      have hrS : r ∈ S := hr.1
      have hrL : r ∈ L := by
        have := hr.2
        rwa [hj] at this
      have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im (conjR (blockU L) x) := by
        rw [Mate.im_V (m := m) C]; exact (mem_Estd _).2 t1_mem_Eset
      obtain ⟨v, hv, hπ⟩ := (C.P.mem_im_pf hVN).1 ht1
      obtain ⟨hYmax, hYidx⟩ := Mate.Yv_isMax (m := m) C hv hπ
      refine ⟨Yv S L v, hYidx, fun B' => ⟨fun hB' => ?_, fun hB' => ?_⟩⟩
      · rcases Mate.type_cases (m := m) C hB' with h | h | h | h
        · exact Or.inl (Mate.eq_Q_of_type_bot (m := m) C hB' h)
        · exact Or.inr (Or.inr (Or.inl (Mate.eq_Yv_of_type_t1 (m := m) C hB' h hv hπ)))
        · exact Or.inr (Or.inr (Or.inr (Mate.eq_conj_Yv_of_type_t2 (m := m) C hrS hrL hrB hB' h hv hπ)))
        · exact Or.inr (Or.inl ((Mate.eq_VD_of_type_E (m := m) C hB' h).trans (Mate.Qx_eq (m := m) C).symm))
      · rcases hB' with rfl | rfl | rfl | rfl
        · exact Mate.Q_isMax (m := m) C
        · exact Mate.Qx_isMax (m := m) C
        · exact hYmax
        · exact C56.isMaxElemAbelian_conjSubgroup hYmax (Subgroup.le_normalizer hrS)
    · intro hne'
      exact absurd hj hne'

end CFSG.QuasithinUnique.burnsideC56_P.AppC
