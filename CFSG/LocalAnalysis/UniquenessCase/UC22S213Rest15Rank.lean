module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Reduction
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.Adapters.LieModelSimple
import CFSG.LieType.Simplicity.TrialityD4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem rest15_rank_one_list_impossible
    (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G} (hL : L ∈ calC M)
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L)
    (hTL : ¬ S21_3ClosedTorusL3 L) (hU3 : ¬ S21_3ClosedU3 L)
    (hCh : ¬ S21_3ClosedChar M L) (hSmall : ¬ S21_3ClosedSmall M L)
    (hY : ¬ S21_3ClosedCharY M L)
    (hlist1 : (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSU 3 p f)) :
    False := by
  classical
  rcases hlist1 with ⟨p, f, hmod, hX⟩ | ⟨p, f, hmod, hX⟩
  · rcases uc22s213_closed_of_rank_three hGA hL (Or.inl rfl) hX with
      h | h | h | h | h | h | h | h | h
    · exact hC2 h
    · exact hL2 h
    · exact hTL h
    · exact hU3 h
    · exact hCh h
    · exact hSmall h
    · obtain ⟨_, rfl, rfl⟩ := h
      norm_num at hmod
    · cases h.1
    · obtain ⟨hp2, rfl, hM⟩ := h
      exact hY ⟨p, hp2, Or.inl hX, hM⟩
  · rcases uc22s213_closed_of_rank_three hGA hL (Or.inr rfl) hX with
      h | h | h | h | h | h | h | h | h
    · exact hC2 h
    · exact hL2 h
    · exact hTL h
    · exact hU3 h
    · exact hCh h
    · exact hSmall h
    · cases h.1
    · obtain ⟨_, rfl, rfl⟩ := h
      norm_num at hmod
    · obtain ⟨hp2, rfl, hM⟩ := h
      exact hY ⟨p, hp2, Or.inr hX, hM⟩

theorem rest15_two_le_pRank_three
    (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G} (hL : L ∈ calC M)
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L)
    (hTL : ¬ S21_3ClosedTorusL3 L) (hU3 : ¬ S21_3ClosedU3 L)
    (hCh : ¬ S21_3ClosedChar M L) (hSmall : ¬ S21_3ClosedSmall M L)
    (hY : ¬ S21_3ClosedCharY M L) (hlist : S21_3List L) :
    2 ≤ CFSG.Open.pRank 3 L := by
  rcases hlist with hZ | ⟨h2, _⟩ | ⟨_, h1⟩
  · have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hperf : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
    have hfin : Finite (Bar2 L) :=
      Finite.of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (QuotientGroup.mk'_surjective _)
    obtain ⟨E, hEel, hEcard⟩ :=
      @CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center (Bar2 L) _ hfin 3
        hfact hperf (by norm_num) hZ
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
      CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hEel hEcard
    simpa only [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)] using h2
  · omega
  · exact (rest15_rank_one_list_impossible hGA hL hC2 hL2 hTL hU3 hCh hSmall hY h1).elim

theorem rest15_pRank_three_eq_two
    (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G} (hL : L ∈ calC M)
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L)
    (hTL : ¬ S21_3ClosedTorusL3 L) (hU3 : ¬ S21_3ClosedU3 L)
    (hCh : ¬ S21_3ClosedChar M L) (hSmall : ¬ S21_3ClosedSmall M L)
    (hY : ¬ S21_3ClosedCharY M L) (hlist : S21_3List L)
    (h3 : CFSG.Open.pRank 3 L ≤ 2) : CFSG.Open.pRank 3 L = 2 :=
  le_antisymm h3
    (rest15_two_le_pRank_three hGA hL hC2 hL2 hTL hU3 hCh hSmall hY hlist)

theorem rest15_lieModel_barInf_of_isSL3PiType_bar2 {M L : Subgroup G}
    (hL : L ∈ calC M) (hSL : PartOne.Section8.IsSL3PiType (Bar2 L)) :
    ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧
      LieModel (BarInf L) t 3 p f := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rcases hSL with ⟨p, f, _, h⟩ | ⟨p, f, _, h⟩ | ⟨p, f, _, h⟩ | ⟨p, f, _, h⟩
  · have : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    have hc : center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
    obtain ⟨q⟩ := uc22p21k_quotCenter_equiv hc
    exact ⟨.PSL, p, f, Or.inl rfl, LieModel.of_mulEquiv (e.trans q).symm h⟩
  · have : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    have hc : center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
    obtain ⟨q⟩ := uc22p21k_quotCenter_equiv hc
    exact ⟨.PSU, p, f, Or.inr rfl, LieModel.of_mulEquiv (e.trans q).symm h⟩
  · exact ⟨.PSL, p, f, Or.inl rfl, LieModel.of_mulEquiv e.symm h.2.2⟩
  · exact ⟨.PSU, p, f, Or.inr rfl, LieModel.of_mulEquiv e.symm h.2.2⟩


theorem rest15_models_of_isSL3PiType_bar2
    (hGA : GriessAllModelsStatement) {M L : Subgroup G} (hL : L ∈ calC M)
    (hSL : PartOne.Section8.IsSL3PiType (Bar2 L))
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L)
    (hTL : ¬ S21_3ClosedTorusL3 L) (hU3 : ¬ S21_3ClosedU3 L)
    (hCh : ¬ S21_3ClosedChar M L) (hSmall : ¬ S21_3ClosedSmall M L)
    (hY : ¬ S21_3ClosedCharY M L) :
    LieModel (BarInf L) .PSL 3 2 2 ∨ LieModel (BarInf L) .PSU 3 2 3 := by
  obtain ⟨t, p, f, ht, hX⟩ := rest15_lieModel_barInf_of_isSL3PiType_bar2 hL hSL
  exact rest15_models_of_rank_three (uc22s213_closed_of_rank_three hGA hL ht hX)
    hC2 hL2 hTL hU3 hCh hSmall hY ht hX


theorem rest15_bar2_models_of_barInf_models {M L : Subgroup G}
    (hL : L ∈ calC M)
    (hX : LieModel (BarInf L) .PSL 3 2 2 ∨ LieModel (BarInf L) .PSU 3 2 3) :
    IsSL3 (Bar2 L) 2 ∨ IsSU3 (Bar2 L) 3 := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rcases hX with h | h
  · exact Or.inl ⟨hL.2.2, LieModel.of_mulEquiv e h⟩
  · exact Or.inr ⟨hL.2.2, LieModel.of_mulEquiv e h⟩


section TrialityParameters


theorem rest15_triality_parameters
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) (hC2 : ¬ S21_3Closed2 L)
    (hT : ¬ S21_3ClosedTorus L) {p f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 p f) :
    p = 2 ∧ (f = 1 ∨ f = 2) := by
  have hp : p.Prime := hmodel.admissible.1
  have hf : 1 ≤ f := hmodel.admissible.2.1
  have hp2 : p = 2 := by
    by_contra hne
    letI : Fact p.Prime := ⟨hp⟩
    have hTw : CFSG.Blueprint.TwistedChevalleyModel (Bar2 L) .D4 (p ^ f) :=
      (hmodel.chevalleyExceptionalModel (by decide)).2
    have hRank := CFSG.SectionRank.four_le_pRank_of_trialityD4Model hf hTw
    rw [pRank_bar2_eq_of_odd hp hne] at hRank
    exact hC2 (Or.inl ⟨p, hp, hne, hRank⟩)
  subst p
  have hf2 : f ≤ 2 := by
    by_contra hgt
    obtain ⟨r, hr, hr5, hrd, hrf⟩ :=
      exists_prime_five_le_dvd_pow_sub_one_not_dvd_exponent Nat.prime_two (by omega : 3 ≤ f)
    letI : IsSimpleGroup (Bar2 L) := (CFSG.LieType.Simplicity.fam_3d4_simplicity
      (Bar2 L) 2 f (hmodel.chevalleyExceptionalModel (by decide))).2
    have hZ : center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
    have hInf : CFSG.Blueprint.LieModel (BarInf L) .trialityD4 0 2 f :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hmodel
    exact hT (Or.inr ⟨r, 2, f, hr, hr5, hrd, hrf, Or.inr (Or.inl ⟨rfl, hInf⟩)⟩)
  exact ⟨rfl, by omega⟩


end TrialityParameters

end CFSG.LocalAnalysis.UniquenessCase.UC22
