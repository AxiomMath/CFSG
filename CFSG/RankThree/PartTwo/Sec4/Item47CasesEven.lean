module

public import CFSG.RankThree.PartTwo.Sec4.Item47CasesOdd
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem two_pow_mod_three_of_even {n : ℕ} (h : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {n : ℕ} (h : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem projSU_eq_map_statedSU (n p f : ℕ) [Fact p.Prime] :
    projSU n p f = (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f)
      (GaloisField p (2 * f))).map (ProjGenLinGroup.mk : GL (Fin n) _ →* _) :=
  (CFSG.PGLModel.projImage_statedSU n p f).symm

@[expose] noncomputable def projSUEquivStatedProj (n p f : ℕ) [Fact p.Prime] :
    projSU n p f ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f) (GaloisField p (2 * f))) :=
  CFSG.PGLModel.projSUEquivStatedProj n p f

theorem isSimpleGroup_projectiveSL_three (K : Type) [Field K] :
    IsSimpleGroup (projectiveSL 3 K) :=
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm.isSimpleGroup

theorem alt47_of_psl2_even {n : ℕ} (hn : 1 ≤ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 n)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  set E := e₁.trans (projSLEquivPSL (GaloisField 2 n))
  rcases inducesKindPSL2_diagonal_or_field L ha3 hout E with hd | hf
  · exact (false_of_inducesKind_diagonal psl2_inndiag_cube hd ha3).elim
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨n, hn, Or.inl ⟨e₁⟩⟩,
      InducesStdKind.psl2 (GaloisField 2 n) ⟨E, hf⟩⟩))

theorem alt47_of_projSL_three_even (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G))
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {n : ℕ} (hn : 1 ≤ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := card_galoisField 2 n hn
  set E := e₁.trans (projSLEquivProjectiveSL 3 (GaloisField 2 n))
  rcases inducesKindPSL_diagonal_or_field L (le_refl 3) ha3 hout E with hd | hf
  · rcases Nat.even_or_odd n with hev | hodd
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
        Or.inr (Or.inl ⟨two_pow_mod_three_of_even hev, ⟨e₁⟩⟩),
        InducesStdKind.psl 3 (GaloisField 2 n) (le_refl 3) ⟨E, hd⟩⟩)))
    · exact (false_of_inducesKind_diagonal (psl_inndiag_cube
        (Or.inr (not_three_dvd_card_units hK (two_pow_mod_three_of_odd hodd)))) hd ha3).elim
  · rcases Nat.even_or_odd n with hev | hodd
    · have : IsSimpleGroup (projectiveSL 3 (GaloisField 2 n)) :=
        isSimpleGroup_projectiveSL_three _
      exact (false_of_inducesKindPSL_field_even hG h3 hK hev ha3 hout
        (center_eq_bot_of_mulEquiv_isSimpleGroup hq E) hf).elim
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨n, hodd, Or.inr (Or.inl ⟨e₁⟩)⟩,
        InducesStdKind.psl 3 (GaloisField 2 n) (le_refl 3) ⟨E, hf⟩⟩))

theorem alt47_of_projSU_three_even (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    {n : ℕ} (hn : 1 ≤ n) (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 n) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  ·
    obtain rfl : n = 1 := by omega
    have := Sec13.isSolvable_projSU_two
    exact (false_of_isQuasisimple_of_isSolvable hq
      (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)).elim
  · have hU := unitaryFieldData_galoisField 2 n hn
    have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
    set E := e₁.trans (projSUEquivUnitaryPSU 2 n hU)
    rcases inducesKindPSU3_diagonal_or_field L hq2 ha3 hout E with hd | hf
    · rcases Nat.even_or_odd n with hev | hodd
      · have := two_pow_mod_three_of_even hev
        exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd ha3).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
          Or.inr (Or.inr ⟨two_pow_mod_three_of_odd hodd, ⟨e₁⟩⟩),
          InducesStdKind.psu3 hU hq2 ⟨E, hd⟩⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inl ⟨e₁⟩))⟩,
        InducesStdKind.psu3 hU hq2 ⟨E, hf⟩⟩))

theorem alt47_of_projSp_two_even (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G))
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {n : ℕ} (hn : 1 ≤ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := card_galoisField 2 n hn
  set E := e₁.trans (projSpEquivStatedProj 2 (GaloisField 2 n))
  rcases inducesKindPSp4Even_diagonal_or_field L ha3 hout E with hd | hf
  · exact (false_of_inducesKind_diagonal psp4Even_inndiag_cube hd ha3).elim
  · rcases Nat.even_or_odd n with hev | hodd
    · have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
        rw [hK]
        obtain ⟨k, rfl⟩ := hev
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n))) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp _ 2 (by norm_num)
          (Or.inl (Or.inr h4))
      exact (false_of_inducesKindPSp4Even_field_even hG h3 hK hev ha3 hout
        (center_eq_bot_of_mulEquiv_isSimpleGroup hq E) hf).elim
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨n, hodd, Or.inr (Or.inr (Or.inl ⟨e₁⟩))⟩,
        InducesStdKind.psp4even (GaloisField 2 n) ⟨E, hf⟩⟩))

theorem false_of_projSU_four_even
    (hin : Inputs47NoD4)
    (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G))
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {n : ℕ} (hn : 1 ≤ n)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 n) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [card_galoisField 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU _ 2 n hK 4 (by norm_num)
      (by simp)
  have hZ := center_eq_bot_of_mulEquiv_isSimpleGroup hq (e₁.trans (projSUEquivStatedProj 4 2 n))
  exact false_of_hasLocalWitness_inducedAutHom hG h3 ha3 hout hZ e₁ fun ha =>
    hin.witnessU4 n hn _ (inducedAutHom_pow_eq_one L e₁ ha ha3)
      ((not_isInnerAut_inducedAutHom_iff L e₁ ha).mpr hout)

theorem alt47_of_slThreeEps_even (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    {n : ℕ} (hn : 1 ≤ n) (hL : IsSLThreeEpsAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ n)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hL
  ·
    set E := e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    rcases inducesKindSL_diagonal_or_field L (le_refl 3) ha3 hout E with
      ⟨E', hx, hd⟩ | ⟨E', hx, hf⟩
    · rcases Nat.even_or_odd n with hev | hodd
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
          Or.inl ⟨K, inferInstance, inferInstance,
            Or.inl ⟨hK, two_pow_mod_three_of_even hev, ⟨e₁⟩⟩⟩,
          InducesStdKind.sl 3 K (le_refl 3) ⟨E', hx, hd⟩⟩)))
      · exact (hd.2 (psl_inndiag_cube
          (Or.inr (not_three_dvd_card_units hK (two_pow_mod_three_of_odd hodd))) _ hd.1
          (descendAut_inducedAutHom_pow_three hx ha3))).elim
    · rcases Nat.even_or_odd n with hev | hodd
      · obtain ⟨m, rfl⟩ := hev
        exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨m, by omega, Or.inr (Or.inr (Or.inr
          ⟨K, inferInstance, inferInstance, by rw [hK, two_mul], ⟨e₁⟩⟩))⟩,
          InducesStdKind.sl 3 K (le_refl 3) ⟨E', hx, hf⟩⟩))
      · have h3n : ¬ 3 ∣ 2 ^ n - 1 := by
          have := two_pow_mod_three_of_odd hodd
          omega
        obtain ⟨e₂⟩ := nonempty_statedSL_mulEquiv_projSL (p := 2) hn hK h3n
        exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨n, hodd, Or.inr (Or.inl ⟨e₁.trans e₂⟩)⟩,
          InducesStdKind.sl 3 K (le_refl 3) ⟨E', hx, hf⟩⟩))
  ·
    have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    ·
      obtain rfl : n = 1 := by omega
      have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      have := Fintype.ofFinite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K)
      have hsolv : Group.IsSolvable (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
          (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      exact (false_of_isQuasisimple_of_isSolvable hq
        (Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective)).elim
    · have hq2 : 2 < 2 ^ n :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
      have E : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 n K 3 := e₁
      rcases inducesKindSU3_diagonal_or_field L hU hq2 ha3 hout E with
        ⟨E', hx, hd⟩ | ⟨E', hx, hf⟩
      · rcases Nat.even_or_odd n with hev | hodd
        · have := two_pow_mod_three_of_even hev
          exact (hd.2 (psu3_inndiag_cube (by omega) _ hd.1
            (suDescend_inducedAutHom_pow_three hq2 hx ha3))).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
            Or.inl ⟨K, inferInstance, inferInstance,
              Or.inr ⟨hK, two_pow_mod_three_of_odd hodd, ⟨e₁⟩⟩⟩,
            InducesStdKind.su3 hU hq2 ⟨E', hx, hd⟩⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨n, hn, Or.inr (Or.inl
          ⟨K, inferInstance, inferInstance, hK, ⟨e₁⟩⟩)⟩,
          InducesStdKind.su3 hU hq2 ⟨E', hx, hf⟩⟩))

end CFSG.RankThree.PartTwo.Sec4
