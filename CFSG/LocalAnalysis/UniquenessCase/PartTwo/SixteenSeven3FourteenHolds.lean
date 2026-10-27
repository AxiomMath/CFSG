module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenBranchA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenNotCartan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_not_case168_11_of_three (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h3 : Case168_3 D ⊥ V hV L) : ¬ Case168_11 D ⊥ V hV L := by
  intro h11
  have h37 : D.sig = {7} := h11.2.2.2
  have h33 : D.sig = {3} := h3.2.2
  rw [h33] at h37
  simp at h37

theorem s16c1614_residual_of_min (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (hM : S16GapMGtOne D) (h13b : R16_13_2 D) (hgap : S16GapFourteenBlock D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G}
    (hU : Min1614 D V U) : E3.mQuot V U = D.k + 2 ∧ Residual1614At D V L hV U := by
  have hk := s16c1614_lt_rMV_of_counterex D hSg h1219 hx h61 h127 hc
  by_cases hΓ : U ∈ gammaEleven D.M V
  · exact (s16c1614_false_of_cartan D hSg h1219 h13b hc hU
      (s16c1614_cartan_of_mem_gamma D hSg h1219 hx h61 h127 hM hc hU hΓ) hk).elim
  · rcases hgap V L hV hc U hU hΓ with hC | hres
    · exact (s16c1614_false_of_cartan D hSg h1219 h13b hc hU hC hk).elim
    · exact hres

theorem r16_14_corr_holds (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hM : S16GapMGtOne D) (h13b : R16_13_2 D) (hgap : S16GapFourteenBlock D) :
    R16_14Corr D := by
  intro V L hV hc
  have key : ∀ U : Subgroup G, Min1614 D V U →
      E3.mQuot V U = D.k + 2 ∧ Residual1614At D V L hV U := fun U hU =>
    s16c1614_residual_of_min D hSg h1219 hx h61 h127 hM h13b hgap hc hU
  by_cases hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ centralizer (U : Set G) ≤ D.M
  · obtain ⟨U₀, hU₀V, hU₀C, hU₀r⟩ := s16c1614_exists_mQuot_eq_rMV D hne
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hU₀ : Min1614 D V U₀ := ⟨hU₀V, hU₀C, hU₀r, hlt.le⟩
      have hm := (key U₀ hU₀).1
      rw [hm] at hU₀r
      exact absurd hU₀r.symm (ne_of_lt hlt)
    · intro hr
      have hmin : ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = D.k + 2 →
          ¬ centralizer (U : Set G) ≤ D.M → Min1614 D V U := by
        intro U hUV hm hUC
        exact ⟨hUV, hUC, by rw [hr]; exact_mod_cast hm, hr.le⟩
      have hU₀ : Min1614 D V U₀ := ⟨hU₀V, hU₀C, hU₀r, hr.le⟩
      rcases (key U₀ hU₀).2 with ⟨h3, h27, -⟩ | ⟨h11, -⟩
      · refine Or.inl ⟨h3, h27, fun U hUV hm hUC => ?_⟩
        rcases (key U (hmin U hUV hm hUC)).2 with ⟨-, -, hdesc⟩ | ⟨h11, -⟩
        · exact hdesc
        · exact absurd h11 (s16c1614_not_case168_11_of_three D h3)
      · refine Or.inr ⟨h11, fun U hUV hm hUC => ?_⟩
        rcases (key U (hmin U hUV hm hUC)).2 with ⟨h3, -, -⟩ | ⟨-, hex⟩
        · exact absurd h11 (s16c1614_not_case168_11_of_three D h3)
        · exact hex
  · push Not at hne
    rw [s16c1614_rMV_eq_top D hne]
    exact ⟨le_top, fun h => absurd h (ENat.top_ne_coe _)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
