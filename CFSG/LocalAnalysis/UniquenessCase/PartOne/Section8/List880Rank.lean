module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Quasithin.EmptyFaithful.S1421QA15N1
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27E
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUR
public import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem two_le_pRank_three_top_of_mulEquiv {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y)
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact h

theorem two_le_pRank_three_of_isSpor_M11 (h : IsSpor X .M11) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M11) := by
    change Finite CFSG.Blueprint.NativeSporadic.M11
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_M11_1515e

theorem two_le_pRank_three_of_isSpor_M12
    (h : IsSpor X .M12) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12) := by
    change Finite CFSG.Blueprint.NativeSporadic.M12
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_M12_1515e

theorem two_le_pRank_three_of_isSpor_M22 (h : IsSpor X .M22) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
    change Finite CFSG.Blueprint.NativeSporadic.M22
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_M22_1515e

theorem two_le_pRank_three_of_isSpor_M23 (h : IsSpor X .M23) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M23) := by
    change Finite CFSG.Blueprint.NativeSporadic.M23
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_M23_1515e

theorem two_le_pRank_three_of_isSpor_M24
    (h : IsSpor X .M24) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite CFSG.Blueprint.NativeSporadic.M24 := Subtype.finite
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M24) := by
    change Finite CFSG.Blueprint.NativeSporadic.M24
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_M24_1515e

theorem two_le_pRank_three_of_isMathieu (h : IsMathieu X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases h with h | h | h | h | h
  · exact two_le_pRank_three_of_isSpor_M11 h
  · exact two_le_pRank_three_of_isSpor_M12 h
  · exact two_le_pRank_three_of_isSpor_M22 h
  · exact two_le_pRank_three_of_isSpor_M23 h
  · exact two_le_pRank_three_of_isSpor_M24 h

theorem two_le_pRank_three_of_isSpor_J2
    (h : IsSpor X .J2) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    Finite.of_equiv X e.toEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := by
    change Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2)
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_J2_1515e

theorem two_le_pRank_three_of_isSpor_HS
    (h : IsSpor X .HS) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
    Finite.of_equiv X e.toEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.HS := by
    change Finite (CFSG.Blueprint.NativeSporadic.Carrier .HS)
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_HS_1515e

theorem two_le_pRank_three_of_isSpor_Ru
    (h : IsSpor X .Ru) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    Finite.of_equiv X e.toEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Ru := by
    change Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru)
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_Ru_1515e

theorem two_le_pRank_three_of_isSpor_J4
    (h : IsSpor X .J4) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    Finite.of_equiv X e.toEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.J4 := by
    change Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4)
    infer_instance
  exact two_le_pRank_three_top_of_mulEquiv e CFSG.Quasithin.two_le_pRank_J4_1515e

theorem two_le_pRank_three_of_isA6Z3 (h : IsA6Z3 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h.2.2
  exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three
    (by norm_num) (CFSG.Quasithin.R3c3.two_le_pRank_three_alt (n := 6) (by norm_num) e)

theorem two_le_pRank_three_of_isA7Z3 (h : IsA7Z3 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h.2.2
  exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three
    (by norm_num) (CFSG.Quasithin.R3c3.two_le_pRank_three_alt (n := 7) (by norm_num) e)

theorem two_le_pRank_three_of_isM22Z3 (h : IsM22Z3 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three (by norm_num)
    (two_le_pRank_three_of_isSpor_M22 h.2.2)

theorem two_le_pRank_three_of_isAlt {n : ℕ} (hn : 6 ≤ n) (h : IsAlt X n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  exact CFSG.Quasithin.R3c3.two_le_pRank_three_alt hn e

theorem two_le_pRank_three_of_lieModel_PSL_five_two_one
    (h : LieModel X .PSL 5 2 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_two_one (n := 5) (Or.inr rfl)
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem two_le_pRank_three_of_lieModel_PSL_three_three_one
    (h : LieModel X .PSL 3 3 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_three
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem two_le_pRank_three_of_isSp4 {n : ℕ} (h : IsSp4 X n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.R3c3.two_le_pRank_three_isPSp_two
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem two_le_pRank_three_of_lieModel_PSU_three_three_one
    (h : LieModel X .PSU 3 3 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_isPSU_three_three
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem two_le_pRank_three_of_isG2
    {n : ℕ} (h : IsG2 X n) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.R3c3.two_le_pRank_three_isG2
    (CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide))

theorem two_le_pRank_three_of_isG2Der_one {n : ℕ}
    (h : n = 1 ∧ LieModel X .PSU 3 3 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  two_le_pRank_three_of_lieModel_PSU_three_three_one h.2

theorem two_le_pRank_three_of_isG2Der
    {n : ℕ} (h : IsG2Der X n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases h with ⟨rfl, h⟩ | ⟨hn, h⟩
  · exact two_le_pRank_three_of_isG2Der_one ⟨rfl, h⟩
  · exact two_le_pRank_three_of_isG2 (n := n) h

theorem three_dvd_sq_two_pow_sub_one (m : ℕ) : 3 ∣ (2 ^ m) ^ 2 - 1 := by
  have hsq : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
    calc
      (2 ^ m) ^ 2 = 2 ^ (m * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * m) := by rw [mul_comm]
  have hmod : (2 ^ m) ^ 2 % 3 = 1 := by
    rw [hsq]
    exact CFSG.Quasithin.R3c.two_pow_mod_three_of_even ⟨m, by ring⟩
  have hdiv : (2 ^ m) ^ 2 = 3 * ((2 ^ m) ^ 2 / 3) + 1 := by
    have h := Nat.mod_add_div ((2 ^ m) ^ 2) 3
    omega
  exact ⟨(2 ^ m) ^ 2 / 3, by omega⟩

theorem two_le_pRank_three_of_isSU5 {m : ℕ} (h : IsSU5 X m) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hC : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 m :=
    CFSG.Blueprint.LieModel.statedClassicalModel h.2 (by decide)
  exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three
    (by norm_num)
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_psu_of_dvd
      (n := 5) (f := m) (by norm_num) hC Nat.prime_three (by norm_num)
      (three_dvd_sq_two_pow_sub_one m))

theorem two_le_pRank_three_of_isSU5Four (h : IsSU5Four X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  two_le_pRank_three_of_isSU5 h.1

@[expose] def List880RankTwoProved (X : Type) [Group X] : Prop := List880 X

theorem two_le_pRank_three_of_list880RankTwoProved
    (h : List880RankTwoProved X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  unfold List880RankTwoProved List880 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact two_le_pRank_three_of_isMathieu h
  · exact two_le_pRank_three_of_isSpor_J2 h
  · exact two_le_pRank_three_of_isSpor_HS h
  · exact two_le_pRank_three_of_isSpor_Ru h
  · exact two_le_pRank_three_of_isSpor_J4 h
  · exact two_le_pRank_three_of_isA6Z3 h
  · exact two_le_pRank_three_of_isA7Z3 h
  · exact two_le_pRank_three_of_isM22Z3 h
  · exact two_le_pRank_three_of_isAlt (by norm_num) h
  · exact two_le_pRank_three_of_isAlt (by norm_num) h
  · exact two_le_pRank_three_of_isAlt (by norm_num) h
  · exact two_le_pRank_three_of_lieModel_PSL_five_two_one h
  · exact two_le_pRank_three_of_lieModel_PSL_three_three_one h
  · obtain ⟨n, hn⟩ := h
    exact two_le_pRank_three_of_isSp4 hn
  · obtain ⟨n, hn⟩ := h
    exact two_le_pRank_three_of_isG2Der hn
  · obtain ⟨m, hm, hSU5⟩ := h
    exact two_le_pRank_three_of_isSU5 hSU5
  · exact two_le_pRank_three_of_isSU5Four h

theorem two_le_pRank_three_of_list880
    {X : Type} [Group X] [Finite X] (h : List880 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  two_le_pRank_three_of_list880RankTwoProved h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
