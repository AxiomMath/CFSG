module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

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

theorem card_galoisField (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    Nat.card (GaloisField p e) = p ^ e :=
  GaloisField.card p e (by omega)

theorem not_three_dvd_card_units {K : Type} [Field K] {q : ℕ} (hK : Nat.card K = q)
    (hq : q % 3 = 2) : ¬ 3 ∣ Nat.card Kˣ := by
  rw [Nat.card_units, hK]
  omega

theorem descendAut_inducedAutHom_pow_three {n : ℕ} {K : Type} [Field K]
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin n) K} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) :
    descendAut n K (inducedAutHom L e ⟨a, ha⟩) ^ 3 = 1 := by
  rw [← map_pow, inducedAutHom_pow_eq_one L e ha ha3, map_one]

theorem suDescend_inducedAutHom_pow_three {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f)
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (inducedAutHom L e ⟨a, ha⟩)) ^ 3 = 1 := by
  rw [← map_pow, ← map_pow, inducedAutHom_pow_eq_one L e ha ha3, map_one, map_one]

theorem alt47_of_psl2_odd {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p e)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hK := card_galoisField p e he
  have : Finite (GaloisField p e ≃+* GaloisField p e) := finite_ringAut Fact.out hK
  set E := e₁.trans (projSLEquivPSL (GaloisField p e))
  rcases inducesKindPSL2_diagonal_or_field L ha3 hout E with hd | hf
  · exact (false_of_inducesKind_diagonal psl2_inndiag_cube hd ha3).elim
  · have h3e : 3 ∣ e := by
      have := three_dvd_card_of_inducesKind_field
        (ψ := CFSG.GorensteinWalter.psl2FieldAut (GaloisField p e)) rfl hf ha3
      rwa [card_ringAut_eq Fact.out he hK] at this
    obtain ⟨e', rfl⟩ := h3e
    exact Or.inl ⟨p, e', inferInstance, hp2, by omega, ⟨e₁⟩,
      InducesStdKind.psl2 (GaloisField p (3 * e')) ⟨E, hf⟩⟩

section Two

variable {p e : ℕ} [Fact p.Prime]

theorem pow_mod_three_of_three_lt (hp3 : 3 < p) : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
  have hp : p.Prime := Fact.out
  have h3 : ¬ 3 ∣ p ^ e := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)) (by omega)
  omega

theorem alt47_of_slThreeEps (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hL : IsSLThreeEpsAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e)) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, ⟨hK, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ := hL
  ·
    have : Finite (K ≃+* K) := finite_ringAut hp hK
    set E := e₁.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    rcases inducesKindSL_diagonal_or_field L (le_refl 3) ha3 hout E with
      ⟨E', hx, hd⟩ | ⟨E', hx, hf⟩
    · rcases pow_mod_three_of_three_lt (e := e) hp3 with hq | hq
      · exact Or.inr (Or.inl ⟨p, e, inferInstance, hp3, he1, he2,
          Or.inl ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, hq, ⟨e₁⟩⟩⟩,
          InducesStdKind.sl 3 K (le_refl 3) ⟨E', hx, hd⟩⟩)
      · exact (hd.2 (psl_inndiag_cube (Or.inr (not_three_dvd_card_units hK hq)) _ hd.1
          (descendAut_inducedAutHom_pow_three hx ha3))).elim
    · have := three_dvd_card_of_isField (ψ := fieldAut 3 K) rfl hf
        (descendAut_inducedAutHom_pow_three hx ha3)
      rw [card_ringAut_eq hp he1 hK] at this
      omega
  ·
    have hU : UnitaryFieldData p e K := ⟨hp, he1, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    have hK' : Nat.card K = p ^ (2 * e) := hU.card
    have : Finite (K ≃+* K) := finite_ringAut hp hK'
    have E : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p e K 3 := e₁
    rcases inducesKindSU3_diagonal_or_field L hU hq2 ha3 hout E with
      ⟨E', hx, hd⟩ | ⟨E', hx, hf⟩
    · rcases pow_mod_three_of_three_lt (e := e) hp3 with hq | hq
      · exact (hd.2 (psu3_inndiag_cube (by omega) _ hd.1
          (suDescend_inducedAutHom_pow_three hq2 hx ha3))).elim
      · exact Or.inr (Or.inl ⟨p, e, inferInstance, hp3, he1, he2,
          Or.inl ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hq, ⟨e₁⟩⟩⟩,
          InducesStdKind.su3 hU hq2 ⟨E', hx, hd⟩⟩)
    · have := three_dvd_card_of_isField (ψ := psuField hU) rfl hf
        (suDescend_inducedAutHom_pow_three hq2 hx ha3)
      rw [card_ringAut_eq hp (by omega) hK'] at this
      omega

theorem alt47_of_projSL_three (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField p e)) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hp : p.Prime := Fact.out
  have hK := card_galoisField p e he1
  have : Finite (GaloisField p e ≃+* GaloisField p e) := finite_ringAut hp hK
  set E := e₁.trans (projSLEquivProjectiveSL 3 (GaloisField p e))
  rcases inducesKindPSL_diagonal_or_field L (le_refl 3) ha3 hout E with hd | hf
  · rcases pow_mod_three_of_three_lt (e := e) hp3 with hq | hq
    · exact Or.inr (Or.inl ⟨p, e, inferInstance, hp3, he1, he2, Or.inr (Or.inl ⟨hq, ⟨e₁⟩⟩),
        InducesStdKind.psl 3 (GaloisField p e) (le_refl 3) ⟨E, hd⟩⟩)
    · exact (false_of_inducesKind_diagonal
        (psl_inndiag_cube (Or.inr (not_three_dvd_card_units hK hq))) hd ha3).elim
  · have := three_dvd_card_of_inducesKind_field (ψ := fieldAut 3 (GaloisField p e)) rfl hf ha3
    rw [card_ringAut_eq hp he1 hK] at this
    omega

theorem alt47_of_projSU_three (hp3 : 3 < p) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 p e) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) : Alt47 L a := by
  have hp : p.Prime := Fact.out
  have hU := unitaryFieldData_galoisField p e he1
  have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  have : Finite (GaloisField p (2 * e) ≃+* GaloisField p (2 * e)) := finite_ringAut hp hU.card
  set E := e₁.trans (projSUEquivUnitaryPSU p e hU)
  rcases inducesKindPSU3_diagonal_or_field L hq2 ha3 hout E with hd | hf
  · rcases pow_mod_three_of_three_lt (e := e) hp3 with hq | hq
    · exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd ha3).elim
    · exact Or.inr (Or.inl ⟨p, e, inferInstance, hp3, he1, he2, Or.inr (Or.inr ⟨hq, ⟨e₁⟩⟩),
        InducesStdKind.psu3 hU hq2 ⟨E, hd⟩⟩)
  · have := three_dvd_card_of_inducesKind_field (ψ := psuField hU) rfl hf ha3
    rw [card_ringAut_eq hp (by omega) hU.card] at this
    omega

end Two

section Three

theorem false_of_g2_prime {X : Type} [Group X] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (h : Blueprint.ChevalleyExceptionalModel X .G2 p 1)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* X) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, ⟨eG⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  rw [pow_one] at hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K p]
    omega
  have hK4 : 4 ≤ Nat.card K := by omega
  have : Finite (K ≃+* K) := finite_ringAut hp (f := 1) (by rw [hK, pow_one])
  obtain ⟨E', hf⟩ := inducesKindG2_field L hK3 hK4 ha3 hout (e₁.trans eG)
  have := three_dvd_card_of_inducesKind_field (ψ := g2FieldHom K) rfl hf ha3
  rw [card_ringAut_eq hp le_rfl (by rw [hK, pow_one])] at this
  omega

theorem false_of_list46_three
    (hin : Inputs47NoD4) {p : ℕ}
    [Fact p.Prime] (hp3 : 3 < p)
    (hL : Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 p 1 ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField p 1))))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have hp : p.Prime := Fact.out
  have hK := card_galoisField p 1 le_rfl
  have : Finite (GaloisField p 1 ≃+* GaloisField p 1) := finite_ringAut hp hK
  rcases hL with hG2 | he₁ | ⟨hp1, he₁⟩ | ⟨-, he₁⟩
  · exact false_of_g2_prime hp3 hG2 (MulEquiv.refl _) ha3 hout
  ·
    obtain ⟨e₁⟩ := he₁
    have : CharP (GaloisField p 1) p := inferInstance
    have hodd : ringChar (GaloisField p 1) ≠ 2 := by
      rw [ringChar.eq (GaloisField p 1) p]
      omega
    set E := e₁.trans (projSpEquivStatedProj 2 (GaloisField p 1))
    rcases inducesKindPSp_two_diagonal_or_field L hodd ha3 hout E with hd | hf
    · exact false_of_inducesKind_diagonal psp_inndiag_cube hd ha3
    · have := three_dvd_card_of_inducesKind_field
        (ψ := SymplecticHigher.fieldAut 2 (GaloisField p 1)) rfl hf ha3
      rw [card_ringAut_eq hp le_rfl hK] at this
      omega
  · obtain ⟨e₁⟩ := he₁
    exact false_of_cubeInner e₁ (cubeInner_of_not_three_dvd_card_outer (hin.outU4p p hp3 hp1))
      ha3 hout
  ·
    obtain ⟨e₁⟩ := he₁
    set E := e₁.trans (projSLEquivProjectiveSL 4 (GaloisField p 1))
    rcases inducesKindPSL_diagonal_or_field L (by norm_num) ha3 hout E with hd | hf
    · exact false_of_inducesKind_diagonal (psl_inndiag_cube (Or.inl (by norm_num))) hd ha3
    · have := three_dvd_card_of_inducesKind_field (ψ := fieldAut 4 (GaloisField p 1)) rfl hf
        ha3
      rw [card_ringAut_eq hp le_rfl hK] at this
      omega

end Three

section Seven

theorem false_of_projSL_of_coprime {n p f : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hf3 : ¬ 3 ∣ f) (hcop : ¬ 3 ∣ n ∨ ¬ 3 ∣ p ^ f - 1)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL n (GaloisField p f)) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have hp : p.Prime := Fact.out
  have hK := card_galoisField p f hf
  have : Finite (GaloisField p f ≃+* GaloisField p f) := finite_ringAut hp hK
  set E := e₁.trans (projSLEquivProjectiveSL n (GaloisField p f))
  rcases inducesKindPSL_diagonal_or_field L hn ha3 hout E with hd | hfd
  · refine false_of_inducesKind_diagonal (psl_inndiag_cube ?_) hd ha3
    rcases hcop with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [Nat.card_units, hK])
  · have := three_dvd_card_of_inducesKind_field (ψ := fieldAut n (GaloisField p f)) rfl hfd ha3
    rw [card_ringAut_eq hp hf hK] at this
    exact hf3 this

theorem false_of_projSU_three_of_coprime {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq2 : 2 < p ^ f)
    (hf3 : ¬ 3 ∣ 2 * f) (hcop : ¬ 3 ∣ p ^ f + 1)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 p f) {a : G}
    (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have hp : p.Prime := Fact.out
  have hU := unitaryFieldData_galoisField p f hf
  have : Finite (GaloisField p (2 * f) ≃+* GaloisField p (2 * f)) := finite_ringAut hp hU.card
  set E := e₁.trans (projSUEquivUnitaryPSU p f hU)
  rcases inducesKindPSU3_diagonal_or_field L hq2 ha3 hout E with hd | hfd
  · exact false_of_inducesKind_diagonal (psu3_inndiag_cube hcop) hd ha3
  · have := three_dvd_card_of_inducesKind_field (ψ := psuField hU) rfl hfd ha3
    rw [card_ringAut_eq hp (by omega) hU.card] at this
    exact hf3 this

theorem false_of_list46_seven
    (hin : Inputs47NoD4)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 5 2 2))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hL with he₁ | he₁ | he₁ <;> obtain ⟨e₁⟩ := he₁
  · exact false_of_projSL_of_coprime (by norm_num) le_rfl (by norm_num) (Or.inl (by norm_num))
      e₁ ha3 hout
  · have hK := card_galoisField 2 1 le_rfl
    have : Finite (GaloisField 2 1 ≃+* GaloisField 2 1) := finite_ringAut Nat.prime_two hK
    set E := e₁.trans (projSpEquivStatedProj 3 (GaloisField 2 1))
    rcases inducesKindPSp_diagonal_or_field L (le_refl 3) ha3 hout E with hd | hf
    · exact false_of_inducesKind_diagonal psp_inndiag_cube hd ha3
    · have := three_dvd_card_of_inducesKind_field
        (ψ := SymplecticHigher.fieldAut 3 (GaloisField 2 1)) rfl hf ha3
      rw [card_ringAut_eq Nat.prime_two le_rfl hK] at this
      omega
  · exact false_of_cubeInner e₁ (cubeInner_of_not_three_dvd_card_outer hin.outU54) ha3 hout

theorem false_of_list46_eight
    (hin : Inputs47NoD4)
    (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hL : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 3 e)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 3 e))) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ≤ 3 ∧
        (Blueprint.ChevalleyExceptionalModel
            ((L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))
            .G2 3 1 ∨
          Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
            Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* projSU 4 3 1))))
    {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hL with ⟨e, he1, he2, he₁ | he₁⟩ | he₁ | ⟨-, hc⟩
  · obtain ⟨e₁⟩ := he₁
    exact false_of_projSL_of_coprime (le_refl 3) he1 (by omega)
      (Or.inr (by
        have : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
        have h1 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
        omega)) e₁ ha3 hout
  · obtain ⟨e₁⟩ := he₁
    have hq2 : 2 < 3 ^ e := lt_of_lt_of_le (by norm_num) (Nat.le_self_pow (by omega) 3)
    exact false_of_projSU_three_of_coprime he1 hq2 (by omega)
      (by
        have : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
        omega) e₁ ha3 hout
  · obtain ⟨e₁⟩ := he₁
    exact false_of_projSL_of_coprime (by norm_num) le_rfl (by norm_num) (Or.inl (by norm_num))
      e₁ ha3 hout
  · have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq.1
    have hY : CubeInner ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
      rcases hc with hG2 | he₂
      · exact cubeInner_of_not_three_dvd_card_outer (hin.outG23 _ hG2)
      · obtain ⟨e₂⟩ := he₂
        exact (cubeInner_of_not_three_dvd_card_outer hin.outU43).of_mulEquiv e₂
    exact false_of_cubeInner (MulEquiv.refl _) (cubeInner_of_center_quotient hY) ha3 hout

end Seven

end CFSG.RankThree.PartTwo.Sec4
