module

public import CFSG.GroupTheory.WeirSylow.CrossRankLinear
public import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
public import CFSG.HardMathSupport.Lang.Proving.FieldCubeRoots
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1061
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.H13.KGFactLieOutAbL
public import CFSG.RankThree.PartOne.LIT.RankProjective
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_projSp_two_eq_two {K : Type} [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.PGLModel.projSp 2 K)) = 2 := by
  have h3K : (3 : K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.three_ne_zero_of_card h3
  refine le_antisymm ?_ ?_
  · exact CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le (r := 3) Nat.prime_three
      (by norm_num) h3K
  · have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.PGLModel.projSp 2 K)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
        (CFSG.PGLModel.projSpEquivStatedProj 2 K)
    rw [hEq]
    exact CFSG.Quasithin.R3c3.two_le_pRank_three_statedProj_statedSp_two

theorem pRank_three_statedSL_three_eq_two {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL 3 K)) = 2 := by
  obtain ⟨ζ, hζ1, hζ3⟩ :=
    CFSG.HardMathSupport.Lang.Proving.exists_ne_one_pow_three_of_three_dvd K h3
  refine le_antisymm ?_ ?_
  · exact CFSG.RankThree.PartOne.LIT.pRank_le_two_of_det_gl (r := 3) Nat.prime_three
      (CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.three_ne_zero_of_dvd h3)
      (by norm_num) (StatedSL 3 K)
      (fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSL hg)
  · exact CFSG.Quasithin.FFC.ThreeRank2.pRank_two_le
      (CFSG.Quasithin.FFC.threeRank2_statedSL_three hζ3 hζ1)

theorem pRank_three_eq_two_of_lieModel_PSU_three_of_mod_two {p f : ℕ}
    (hq3 : p ^ f % 3 = 2) (h : LieModel X .PSU 3 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI := hKfield
  letI := hKfin
  have hf : 1 ≤ f := hadm.2.1
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hadm.1.pos
  have h3q : 3 ∣ p ^ f + 1 := by
    refine ⟨p ^ f / 3 + 1, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hadm.1, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3q
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hE9 := CFSG.Quasithin.H13.KGLieOut.hasElemAb_nine_psu3 (q := p ^ f) hq1 hK h3q
    obtain ⟨A, hA, hcard⟩ := hE9
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) (E := A) le_top hA
      (k := 2) (by rw [hcard]; norm_num)

theorem pRank_three_eq_two_of_lieModel_PSL_four_of_mod_two {p f : ℕ}
    (hq3 : p ^ f % 3 = 2) (h : LieModel X .PSL 4 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hC : StatedClassicalModel X .PSL 4 p f := h.statedClassicalModel (by decide)
  obtain ⟨-, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hC
  letI := hKfield
  letI := hKfin
  have h3q : 3 ∣ p ^ f + 1 := by
    refine ⟨p ^ f / 3 + 1, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hdvd : 3 ∣ Nat.card K + 1 := by rwa [hK]
  have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 4 K))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL 4 K)) :=
    CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_eq (p := 3) (d := 4) (by norm_num)
      (fun c hc => CFSG.GroupTheory.WeirSylow.pow_eq_one_of_scalar_mem_statedSL hc)
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSL_le_div_two
      (p := 3) (K := K) (n := 4) (hp := by decide) (by norm_num) hdvd
    simpa using hle
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e, hEq]
    exact CFSG.Quasithin.FFC.ThreeRank2.pRank_two_le
      (CFSG.Quasithin.FFC.threeRank2_statedSL (K := K) (n := 4) (by norm_num))

theorem pRank_three_eq_two_of_lieModel_PSL_five_of_mod_two {p f : ℕ}
    (hq3 : p ^ f % 3 = 2) (h : LieModel X .PSL 5 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hC : StatedClassicalModel X .PSL 5 p f := h.statedClassicalModel (by decide)
  obtain ⟨-, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hC
  letI := hKfield
  letI := hKfin
  have h3q : 3 ∣ p ^ f + 1 := by
    refine ⟨p ^ f / 3 + 1, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hdvd : 3 ∣ Nat.card K + 1 := by rwa [hK]
  have hEq : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 5 K))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL 5 K)) :=
    CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_eq (p := 3) (d := 5) (by norm_num)
      (fun c hc => CFSG.GroupTheory.WeirSylow.pow_eq_one_of_scalar_mem_statedSL hc)
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSL_le_div_two
      (p := 3) (K := K) (n := 5) (hp := by decide) (by norm_num) hdvd
    simpa using hle
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e, hEq]
    exact CFSG.Quasithin.FFC.ThreeRank2.pRank_two_le
      (CFSG.Quasithin.FFC.threeRank2_statedSL (K := K) (n := 5) (by norm_num))

theorem pRank_three_eq_two_of_lieModel_PSU_four_of_mod_one {p f : ℕ}
    (hq3 : p ^ f % 3 = 1) (h : LieModel X .PSU 4 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hC : StatedClassicalModel X .PSU 4 p f := h.statedClassicalModel (by decide)
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hC
  letI := hKfield
  letI := hKfin
  have hf : 1 ≤ f := hadm.2.1
  have h3q : 3 ∣ p ^ f - 1 := by
    refine ⟨p ^ f / 3, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hp3 : p ≠ 3 := by
    intro hp
    subst hp
    have h3dvd : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega : f ≠ 0)
    have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) := Nat.dvd_sub h3dvd h3q
    have hge : 1 ≤ 3 ^ f := Nat.one_le_pow f 3 (by norm_num)
    rw [show 3 ^ f - (3 ^ f - 1) = 1 by omega] at h1
    omega
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSU_le_div_two
      (p := 3) (hp := by decide) (L := K) (q := p ^ f) (n := 4) hK (by norm_num) h3q
    simpa using hle
  · exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four
      (n := 4) (by norm_num) hp3 (h.statedClassicalModel (by decide))

theorem pRank_three_eq_two_of_lieModel_PSU_five_of_mod_one {p f : ℕ}
    (hq3 : p ^ f % 3 = 1) (h : LieModel X .PSU 5 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hC : StatedClassicalModel X .PSU 5 p f := h.statedClassicalModel (by decide)
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hC
  letI := hKfield
  letI := hKfin
  have hf : 1 ≤ f := hadm.2.1
  have h3q : 3 ∣ p ^ f - 1 := by
    refine ⟨p ^ f / 3, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hp3 : p ≠ 3 := by
    intro hp
    subst hp
    have h3dvd : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega : f ≠ 0)
    have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) := Nat.dvd_sub h3dvd h3q
    have hge : 1 ≤ 3 ^ f := Nat.one_le_pow f 3 (by norm_num)
    rw [show 3 ^ f - (3 ^ f - 1) = 1 by omega] at h1
    omega
  refine le_antisymm ?_ ?_
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hle := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSU_le_div_two
      (p := 3) (hp := by decide) (L := K) (q := p ^ f) (n := 5) hK (by norm_num) h3q
    simpa using hle
  · exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four
      (n := 5) (by norm_num) hp3 (h.statedClassicalModel (by decide))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
