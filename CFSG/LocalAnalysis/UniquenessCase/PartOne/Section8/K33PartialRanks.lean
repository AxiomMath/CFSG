module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
public import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup Matrix CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open scoped commutatorElement IsMulCommutative

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_eq_two_of_isAlt_of_le_eight {n : ℕ} (hn6 : 6 ≤ n) (hn8 : n ≤ 8)
    (h : IsAlt X n) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  refine le_antisymm ?_ (two_le_pRank_three_of_isAlt hn6 h)
  obtain ⟨e⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact CFSG.SectionRank.pRank_alternating_le_two hn8 Nat.prime_three (by norm_num)

theorem pRank_three_eq_two_of_isAlt_six (h : IsAlt X 6) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
  pRank_three_eq_two_of_isAlt_of_le_eight (by norm_num) (by norm_num) h

theorem pRank_three_eq_two_of_isSpor_M11
    (h : IsSpor X .M11) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  refine le_antisymm ?_ (two_le_pRank_three_of_isSpor_M11 h)
  obtain ⟨e⟩ := h
  have hcardX : Nat.card X = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three ?_
  rw [hcardX]
  norm_num

private theorem pRank_three_eq_two_of_native_cubic
    {M : Type} [Group M] [Finite M]
    (hfac : (Nat.card M).factorization 3 = 3)
    {x y : M} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) : CFSG.Open.pRank 3 (⊤ : Subgroup M) = 2 := by
  have h2 : CFSG.pRank 3 M = 2 :=
    CFSG.RankThree.Asc83Table.ex27_pRank hx hy hzx hzy hz1 hfac
  exact (CFSG.SectionRank.pRank_eq_open_pRank_top 3 M).symm.trans h2

theorem pRank_three_eq_two_of_isSpor_M12
    (h : IsSpor X .M12) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12) := Finite.of_equiv X e.toEquiv
  have hcardX : Nat.card X = 95040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have hcardC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M12) = 95040 :=
    (Nat.card_congr e.toEquiv).symm.trans hcardX
  have hfac : (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M12)).factorization 3 = 3 :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
      Nat.prime_three (by rw [hcardC]; norm_num)
      ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
    CFSG.SectionRank.M12_sylow3_cubic_witness
  have h2c : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M12)) = 2 :=
    pRank_three_eq_two_of_native_cubic hfac hx hy hzx hzy hz
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2c

theorem pRank_three_eq_two_of_isSpor_J4
    (h : IsSpor X .J4) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) := Finite.of_equiv X e.toEquiv
  have hcardX : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  have hcardC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) =
      86775571046077562880 := (Nat.card_congr e.toEquiv).symm.trans hcardX
  have hfac : (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4)).factorization 3 = 3 :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
      Nat.prime_three (by rw [hcardC]; norm_num)
      ⟨by rw [hcardC]; norm_num, by rw [hcardC]; norm_num⟩
  obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ :=
    CFSG.SectionRank.J4_sylow3_cubic_witness
  have h2c : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J4)) = 2 :=
    pRank_three_eq_two_of_native_cubic hfac hx hy hzx hzy hz
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).trans h2c

theorem pRank_three_eq_two_of_lieModel_PSL_three_three_one
    (h : LieModel X .PSL 3 3 1) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ (two_le_pRank_three_of_lieModel_PSL_three_three_one h)
  have hcl := LieModel.statedClassicalModel h (by decide)
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eX⟩⟩ := hcl.2
  letI := hKfield
  letI := hKfin
  have hK : Nat.card K = 3 := by rw [hKcard]; norm_num
  have hPSL : CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) ≤ 2 := by
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)) :=
      CFSG.SectionRank.pRank_quotient_eq (Subgroup.center (SpecialLinearGroup (Fin 3) K))
        (by rw [CFSG.RankThree.PartTwo.Census.center_SL_three_card_eq_one hK]; norm_num)
    rw [h1]
    exact CFSG.RankThree.PartTwo.Census.pRank_three_SL_three_le hK
  have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K ≃* StatedProj (StatedSL 3 K) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (eX.trans ePSL.symm)]
  exact hPSL

theorem pRank_three_eq_two_of_lieModel_PSU_three_three_one
    (h : LieModel X .PSU 3 3 1) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ (two_le_pRank_three_of_lieModel_PSU_three_three_one h)
  have hcl := LieModel.statedClassicalModel h (by decide)
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eX⟩⟩ := hcl.2
  letI := hKfield
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = 9 := by rw [hKcard]; norm_num
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hStated : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 3 K))) ≤ 2 := by
    have hF' : Nat.card K = (3 ^ 1) ^ 2 := by rw [hK]; norm_num
    obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF' 3
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 3 K))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 K)) :=
      CFSG.SectionRank.pRank_quotient_eq _
        (by
          rw [CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hK,
            Subgroup.card_bot]
          norm_num)
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 K)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) 3)) :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
        ((CFSG.LieType.Universal.Unitary.conjEquiv P hP).trans
          (MulEquiv.subgroupCongr
            (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF' 3)))).symm
    rw [h1, h2]
    exact CFSG.RankThree.PartTwo.Census.pRank_three_SU_three_le hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eX]
  exact hStated

private theorem pRank_three_le_two_of_noE27
    (h : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoE27 X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hE
  by_contra hlt
  push Not at hlt
  have hEp : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hk3 : 3 ≤ k := by
    rw [hk] at hlt
    by_contra hklt
    have hk2 : k ≤ 2 := by omega
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hdvd : 3 ^ 3 ∣ Nat.card ↥E := by
    rw [hk]
    exact pow_dvd_pow 3 hk3
  obtain ⟨K, hKcard, -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    (p := 3) (n := 3) Nat.prime_three (H := ⊥) (L := E) (by simp) hdvd bot_le
  have hKcomm : IsMulCommutative ↥K := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    have hc := hE.1.is_comm.comm (⟨(a : X), hKE a.2⟩ : ↥E) (⟨(b : X), hKE b.2⟩ : ↥E)
    exact congrArg (fun z : ↥E => (z : X)) hc
  have hKpow : ∀ x ∈ K, x ^ 3 = 1 := fun x hxK => by
    have hx := hE.2 x (hKE hxK)
    simpa using hx
  refine h ⟨K, ⟨hKcomm, hKpow⟩, ?_⟩
  rw [hKcard]
  norm_num

section G2Certificates

theorem pRank_three_eq_two_of_lieModel_G2_two {f : ℕ} (h : LieModel X .G2 0 2 f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  refine le_antisymm ?_ ?_
  · have hno : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoE27 X :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_g2Low X .G2 0 2 f
        (LieModel.admissible h) (by decide) ⟨rfl, by norm_num⟩ h
    exact pRank_three_le_two_of_noE27 hno
  · exact CFSG.Quasithin.R3c3.two_le_pRank_three_isG2
      (LieModel.chevalleyExceptionalModel h (by decide))

end G2Certificates

section TrialityD4Certificates

theorem pRank_three_eq_two_of_lieModel_trialityD4_two_one
    (h : LieModel X .trialityD4 0 2 1) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  refine le_antisymm ?_ ?_
  · have hno : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoE27 X :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_triD4Low X .trialityD4 0 2 1
        (LieModel.admissible h) (by decide) ⟨rfl, by norm_num⟩ h
    exact pRank_three_le_two_of_noE27 hno
  · exact CFSG.Quasithin.R3c3.two_le_pRank_three_is3D4
      (LieModel.chevalleyExceptionalModel h (by decide))

end TrialityD4Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
