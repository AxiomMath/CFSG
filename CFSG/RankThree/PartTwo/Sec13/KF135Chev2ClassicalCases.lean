module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ClassicalRankU
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.RankThree.PartTwo.Sec13.K135OutP
public import CFSG.RankThree.PartOne.KF.F122PSUSplit
public import CFSG.RankThree.PartOne.K1214.SylowSp4
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamLinear
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.LieType.SeitzGeneration.OuterQuotient
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.Sec13.KF135Proof
open CFSG.RankThree.PartOne.OutStructure (OutPChain)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem dvd_two_pow_sub_one_iff {n p : ℕ} : p ∣ 2 ^ n - 1 ↔ ((2 ^ n : ℕ) : ZMod p) = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, sub_eq_zero]

theorem dvd_two_pow_add_one_iff {n p : ℕ} : p ∣ 2 ^ n + 1 ↔ ((2 ^ n : ℕ) : ZMod p) = -1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]

theorem neg_one_ne_one_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; exact hp2)

theorem not_dvd_three_of_seven_le {p : ℕ} (hp7 : 7 ≤ p) {m : ℕ} : ¬ p ∣ Nat.gcd 3 m :=
  CFSG.RankThree.PartTwo.Sec13.F135Last.not_dvd_gcd_of_lt (by norm_num) (by omega)

theorem le_inner_of_card_outer {S T : Type} [Group S] [Finite S] [Group T] (e : S ≃* T) {p N : ℕ}
    (hout : Nat.card (Outer T) = N) (hp : p.Prime) (hN : ¬ p ∣ N) {P : Subgroup (MulAut S)}
    (hP : IsPGroup p P) : P ≤ (MulAut.conj : S →* MulAut S).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [hk, Nat.card_congr (equivalence e).toEquiv, hout]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)

theorem card_outer_projSU_three {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Outer (projSU 3 2 n)) = 2 * n * Nat.gcd 3 (2 ^ n + 1) := by
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 n (by omega)
  have hq : ¬ (3 = 3 ∧ 2 ^ n = 2) := fun ⟨_, h⟩ => by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  rw [Nat.card_congr (equivalence (CFSG.RankThree.PartTwo.Sec4.projSUEquivUnitaryPSU 2 n hU)).toEquiv]
  exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
    (n := 3) hU le_rfl hq).2.2.2.2.1

theorem card_outer_projSp_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Outer (projSp 2 (GaloisField 2 n))) = 2 * n := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn (card_galoisField_two (by omega))
  rw [Nat.card_congr
    (equivalence (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))).toEquiv]
  exact (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hn hFr
    hord hzp).2.2.2.2.2.1

theorem two_le_localRank_projSL_three {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hx : ((2 ^ n : ℕ) : ZMod p) = 1) : 2 ≤ localRank p (projSL 3 (GaloisField 2 n)) := by
  set K := GaloisField 2 n
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, card_galoisField_two (by omega)]
    exact dvd_two_pow_sub_one_iff.2 hx
  have h := CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (K := K) (m := 2) (n := 3) hp hrK
    (by norm_num) (by norm_num) (Or.inr fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  let ε : projSL 3 K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    (CFSG.PGLModel.projSLEquivStatedProj 3 K).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := Finite.of_equiv _ ε.toEquiv
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ε hp]

theorem two_le_localRank_projSp_two {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hx : ((2 ^ n : ℕ) : ZMod p) = 1) : 2 ≤ localRank p (projSp 2 (GaloisField 2 n)) := by
  set K := GaloisField 2 n
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, card_galoisField_two (by omega)]
    exact dvd_two_pow_sub_one_iff.2 hx
  have h := CFSG.RankThree.PartOne.KFU.le_localRank_statedSp_torus (K := K) (n := 2) hp (by omega)
    hrK (by norm_num)
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.PGLModel.projSpEquivStatedProj 2 K) hp]

theorem two_le_localRank_projSU_four_of_eq_one {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hx : ((2 ^ n : ℕ) : ZMod p) = 1) : 2 ≤ localRank p (projSU 4 2 n) := by
  set K := GaloisField 2 (2 * n)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hl := CFSG.RankThree.PartOne.two_le_localRank_statedSU_split (K := K) (n := 4) h hp
    (by omega) (dvd_two_pow_sub_one_iff.2 hx) le_rfl
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.PGLModel.projSUEquivStatedProj 4 2 n) hp]

theorem two_le_localRank_projSU_four_of_eq_neg_one {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hx : ((2 ^ n : ℕ) : ZMod p) = -1) : 2 ≤ localRank p (projSU 4 2 n) := by
  set K := GaloisField 2 (2 * n)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hl := CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (K := K) h (r := p)
    (k := 1) (n := 4) hp (dvd_two_pow_add_one_iff.2 hx) (by norm_num)
    (Or.inr fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.PGLModel.projSUEquivStatedProj 4 2 n) hp]

theorem isMulCommutative_sylow_projSU_three {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp7 : 7 ≤ p)
    (Q : Sylow p (projSU 3 2 n)) : IsMulCommutative (Q : Subgroup (projSU 3 2 n)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K := GaloisField 2 (2 * n)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [card_galoisField_two (by omega)]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
    omega
  obtain ⟨e₀, he, hpe⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_order_data (K := K) hpK
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv
    (CFSG.PGLModel.projSUEquivStatedProj 3 2 n)
    (fun R => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_statedProj
      (fun P hP => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL_matrix
        (hp.odd_of_ne_two (by omega)) hpK he hpe
        (lt_of_le_of_lt (Nat.div_le_self 3 e₀) (by omega)) hP)
      (CFSG.Open.StatedSU 3 (2 ^ n) K) R) Q

theorem isMulCommutative_sylow_projSp_two {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : ((2 ^ n : ℕ) : ZMod p) = -1) (Q : Sylow p (projSp 2 (GaloisField 2 n))) :
    IsMulCommutative (Q : Subgroup (projSp 2 (GaloisField 2 n))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd : p ∣ 2 ^ n + 1 := dvd_two_pow_add_one_iff.2 hx
  have hne := CFSG.RankThree.PartTwo.Sec13.F135Last.two_pow_ne_of_two_le' hn
  have hX := CFSG.RankThree.PartTwo.Sec13.F135Last.stated_of_lieModel (MulEquiv.refl _)
    (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSp (n := 2) (p := 2) (e := n)
      ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)
  have h0 : 2 ^ n + 1 ≠ 0 := by positivity
  have he1 : 1 ≤ (2 ^ n + 1).factorization p := hp.factorization_pos_of_dvd h0 hd
  exact KF135Chev2Exc.isMulCommutative_of_sylowShape
    (CFSG.RankThree.PartOne.K1214.sylowShape_of_psp4Model hp hp2 he1
      (Nat.ordProj_mul_ordCompl_eq_self (2 ^ n + 1) p).symm (Nat.not_dvd_ordCompl hp h0) hX) Q

section Families

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem false_of_kF135Hyp_projSL_two {n : ℕ} (hn : 1 ≤ n) (e : S ≃* projSL 2 (GaloisField 2 n))
    (h : KF135Hyp S p P x u V) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · exact CFSG.RankThree.PartTwo.Sec13.F135Last.not_simple_projSL_two 2 (Or.inl rfl) h.simple
      h.nonab e
  · have hne := CFSG.RankThree.PartTwo.Sec13.F135Last.two_pow_ne_of_two_le' hn2
    have hout : OutPChain p S := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psl e hp hp7
      (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSL (n := 2) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2,
          fun h => hne.2 (Prod.mk.inj h).2⟩) (by norm_num) (fun h => absurd h (by norm_num))
    exact KF135Chev2Exc.false_of_rankLE1 h hout
      ((rankLE1_projSL_two hp (by omega) (natCast_ne_zero_galoisField hp (by omega))).of_mulEquiv
        e.symm)

theorem false_of_kF135Hyp_projSL_three {n : ℕ} (hn : 1 ≤ n)
    (e : S ≃* projSL 3 (GaloisField 2 n)) (h : KF135Hyp S p P x u V) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  by_cases h1 : ((2 ^ n : ℕ) : ZMod p) = 1
  · refine KF135Chev2Exc.false_of_two_le_localRank h ?_
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact two_le_localRank_projSL_three hn hp hp7 h1
  · have hout : OutPChain p S := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psl e hp hp7
      (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSL (n := 3) (p := 2) (e := n)
        ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h, fun h => by simp at h⟩)
      (by norm_num) (fun _ => CFSG.RankThree.PartTwo.Sec13.F135Last.not_dvd_gcd_of_lt
        (by norm_num) (by omega))
    exact KF135Chev2Exc.false_of_rankLE1 h hout
      ((rankLE1_projSL_three_of_ne_one hn hp hp7 h1).of_mulEquiv e.symm)

theorem false_of_kF135Hyp_projSU_four {n : ℕ} (hn : 1 ≤ n) (e : S ≃* projSU 4 2 n)
    (h : KF135Hyp S p P x u V) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  by_cases h1 : ((2 ^ n : ℕ) : ZMod p) = 1
  · refine KF135Chev2Exc.false_of_two_le_localRank h ?_
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact two_le_localRank_projSU_four_of_eq_one hn hp hp7 h1
  by_cases h2 : ((2 ^ n : ℕ) : ZMod p) = -1
  · refine KF135Chev2Exc.false_of_two_le_localRank h ?_
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact two_le_localRank_projSU_four_of_eq_neg_one hn hp hp7 h2
  have hout : OutPChain p S := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psu e hp hp7
    (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSU (n := 4) (p := 2) (e := n)
      ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h⟩) (by norm_num)
    (CFSG.RankThree.PartTwo.Sec13.F135Last.not_dvd_gcd_of_lt (by norm_num) (by omega))
  by_cases h4 : ((2 ^ n : ℕ) : ZMod p) ^ 2 = -1
  · have hrq : ¬ p ∣ 2 ^ n + 1 := fun hd => h2 (dvd_two_pow_add_one_iff.1 hd)
    have hr := rankLE1_projSU_of_lt_ordNegQ (m := 4) hn (by norm_num) hp (by omega) hp2 hrq
      (by rw [ordNegQ_eq_four_of_sq_eq_neg_one hp hp2 h4]; norm_num)
    exact KF135Chev2Exc.false_of_rankLE1 h hout (hr.of_mulEquiv e.symm)
  · exact KF135Chev2Exc.false_of_rankLE1 h hout
      ((rankLE1_projSU_four_of_ne hn hp hp7 h1 h2 h4).of_mulEquiv e.symm)

theorem false_of_kF135Hyp_projSU_three_of_not_e2 {n : ℕ} (hn : 1 ≤ n) (e : S ≃* projSU 3 2 n)
    (h : KF135Hyp S p P x u V) (hE2 : ¬ (p ∣ n ∧ ((2 ^ n : ℕ) : ZMod p) = -1)) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · exact CFSG.RankThree.PartTwo.Sec13.F135Last.not_simple_projSU_three_two h.simple h.nonab e
  have hne := CFSG.RankThree.PartTwo.Sec13.F135Last.two_pow_ne_of_two_le' hn2
  have hout : OutPChain p S := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psu e hp hp7
    (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSU (n := 3) (p := 2) (e := n)
      ⟨Nat.prime_two, by omega, le_refl 3, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)
    (CFSG.RankThree.PartTwo.Sec13.F135Last.not_dvd_gcd_of_lt (by norm_num) (by omega))
  by_cases h1 : ((2 ^ n : ℕ) : ZMod p) = 1
  · have hrq : ¬ p ∣ 2 ^ n + 1 := fun hd => by
      have := dvd_two_pow_add_one_iff.1 hd
      rw [h1] at this
      exact neg_one_ne_one_zmod hp hp2 this.symm
    have hr := rankLE1_projSU_of_lt_ordNegQ (m := 3) hn (by norm_num) hp (by omega) hp2 hrq
      (by rw [ordNegQ_eq_two_of_eq_one hp hp2 h1]; norm_num)
    exact KF135Chev2Exc.false_of_rankLE1 h hout (hr.of_mulEquiv e.symm)
  by_cases h2 : ((2 ^ n : ℕ) : ZMod p) = -1
  · have hpn : ¬ p ∣ n := fun hd => hE2 ⟨hd, h2⟩
    have hinn := le_inner_of_card_outer e (card_outer_projSU_three hn2) hp
      (fun hd => by
        rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
          · have := Nat.le_of_dvd (by norm_num) hd
            omega
          · exact hpn hd
        · exact not_dvd_three_of_seven_le hp7 hd) h.pgroup
    exact KF135Chev2Exc.false_of_rankLE2_inner h hinn
      ((rankLE2_projSU_three hn hp hp2).of_mulEquiv e.symm)
      (fun Q => by
        haveI : Fact p.Prime := ⟨hp⟩
        exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
          (isMulCommutative_sylow_projSU_three hn hp hp7) Q)
  · exact KF135Chev2Exc.false_of_rankLE1 h hout
      ((rankLE1_projSU_three_of_ne hn hp hp7 h1 h2).of_mulEquiv e.symm)

theorem false_of_kF135Hyp_projSp_two_of_not_e2 {n : ℕ} (hn : 1 ≤ n)
    (e : S ≃* projSp 2 (GaloisField 2 n)) (h : KF135Hyp S p P x u V)
    (hE2 : ¬ (p ∣ n ∧ ((2 ^ n : ℕ) : ZMod p) = -1)) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · exact CFSG.RankThree.PartTwo.Sec13.F135Last.not_simple_projSp_two_two h.simple h.nonab e
  by_cases h1 : ((2 ^ n : ℕ) : ZMod p) = 1
  · refine KF135Chev2Exc.false_of_two_le_localRank h ?_
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact two_le_localRank_projSp_two hn hp hp7 h1
  have hne := CFSG.RankThree.PartTwo.Sec13.F135Last.two_pow_ne_of_two_le' hn2
  have hout : OutPChain p S := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psp e hp hp7
    (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSp (n := 2) (p := 2) (e := n)
      ⟨Nat.prime_two, by omega, le_refl 2, fun h => hne.1 (Prod.mk.inj h).2⟩) (by norm_num)
    (fun _ => rfl)
  by_cases h2 : ((2 ^ n : ℕ) : ZMod p) = -1
  · have hpn : ¬ p ∣ n := fun hd => hE2 ⟨hd, h2⟩
    have hinn := le_inner_of_card_outer e (card_outer_projSp_two hn) hp
      (fun hd => by
        rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · have := Nat.le_of_dvd (by norm_num) hd
          omega
        · exact hpn hd) h.pgroup
    exact KF135Chev2Exc.false_of_rankLE2_inner h hinn
      ((rankLE2_projSp_two hp hp2 (natCast_ne_zero_galoisField hp hp2)).of_mulEquiv e.symm)
      (fun Q => by
        haveI : Fact p.Prime := ⟨hp⟩
        exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
          (isMulCommutative_sylow_projSp_two hn2 hp hp2 h2) Q)
  · exact KF135Chev2Exc.false_of_rankLE1 h hout
      ((rankLE1_projSp_two_of_ne hn hp hp7 h1 h2).of_mulEquiv e.symm)

end Families

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
