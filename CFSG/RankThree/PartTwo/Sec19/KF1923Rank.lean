module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalBlock
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockRank
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.HardMathSupport.Foote.Proving.CoverThree.CentreSL3
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankAny
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsRot
import CFSG.Quasithin.EmptyFaithful.R3c3Rank
import CFSG.Quasithin.Vol2.Ch4Sec2T425C27E
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.Sec12.Item122
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.Assembly.RankThreeEven (projSL projSp projSU projOmegaMinus)

theorem exists_prime_five_le_dvd_two_pow_sub_one {k : ℕ} (hk : 2 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ (2 * k) - 1 := by
  have h16 : 2 ^ 4 ∣ 2 ^ (2 * k) := pow_dvd_pow 2 (by omega)
  have hpos : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  have hmod : (2 ^ (2 * k) - 1) % 16 = 15 := by
    norm_num at h16
    omega
  have hpow3 : ∀ a : ℕ,
      3 ^ a % 16 = 1 ∨ 3 ^ a % 16 = 3 ∨ 3 ^ a % 16 = 9 ∨ 3 ^ a % 16 = 11 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h | h <;> rw [h] <;> norm_num
  by_contra hcon
  push Not at hcon
  have hdiv3 : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ (2 * k) - 1 → d = 3 := by
    intro d hd hdN
    rcases Nat.lt_or_ge d 5 with hlt | hge
    · interval_cases d
      · exact absurd hd Nat.not_prime_zero
      · exact absurd hd Nat.not_prime_one
      · omega
      · rfl
      · exact absurd hd (by norm_num)
    · exact absurd hdN (hcon d hd hge)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 ^ (2 * k) - 1 = 3 ^ a :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) hdiv3⟩
  rw [ha] at hmod
  rcases hpow3 a with h | h | h | h <;> omega

theorem two_le_pRank_statedSL_three_of_orderOf {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) {ζ : Kˣ} (hζ : orderOf ζ = p) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(CFSG.Open.StatedSL 3 K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  set d : Fin 3 → Kˣ := ![ζ, ζ⁻¹, 1] with hd
  set f : Fin 3 → Kˣ := ![1, ζ, ζ⁻¹] with hf
  have hdprod : ∏ i, d i = 1 := by
    simp [hd, Fin.prod_univ_three]
  have hfprod : ∏ i, f i = 1 := by
    simp [hf, Fin.prod_univ_three]
  have hdp : d ^ p = 1 := by
    funext i
    fin_cases i <;> simp [hd, hζp]
  have hfp : f ^ p = 1 := by
    funext i
    fin_cases i <;> simp [hf, hζp]
  let x : ↥(CFSG.Open.StatedSL 3 K) :=
    ⟨CFSG.SectionRank.ClassicalEven.torusDiag d,
      CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL hdprod⟩
  let y : ↥(CFSG.Open.StatedSL 3 K) :=
    ⟨CFSG.SectionRank.ClassicalEven.torusDiag f,
      CFSG.SectionRank.ClassicalEven.torusDiag_mem_SL hfprod⟩
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    show CFSG.SectionRank.ClassicalEven.torusDiag d ^ p = 1
    rw [← map_pow, hdp, map_one]
  have hyp : y ^ p = 1 := by
    apply Subtype.ext
    show CFSG.SectionRank.ClassicalEven.torusDiag f ^ p = 1
    rw [← map_pow, hfp, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : CFSG.SectionRank.ClassicalEven.torusDiag d =
        CFSG.SectionRank.ClassicalEven.torusDiag (1 : Fin 3 → Kˣ) := by
      have := congrArg Subtype.val h
      change CFSG.SectionRank.ClassicalEven.torusDiag d = 1 at this
      rw [map_one]
      exact this
    have h0 := congrFun (CFSG.SectionRank.ClassicalEven.torusDiag_injective h') 0
    exact hζ1 (by simpa [hd] using h0)
  have hy1 : y ≠ 1 := by
    intro h
    have h' : CFSG.SectionRank.ClassicalEven.torusDiag f =
        CFSG.SectionRank.ClassicalEven.torusDiag (1 : Fin 3 → Kˣ) := by
      have := congrArg Subtype.val h
      change CFSG.SectionRank.ClassicalEven.torusDiag f = 1 at this
      rw [map_one]
      exact this
    have h0 := congrFun (CFSG.SectionRank.ClassicalEven.torusDiag_injective h') 1
    exact hζ1 (by simpa [hf] using h0)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hxy : Commute x y := by
    apply Subtype.ext
    exact ((Commute.all d f).map CFSG.SectionRank.ClassicalEven.torusDiag).eq
  have hxw : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec ![0, 0, 1] =
      ![0, 0, 1] := by
    change (Matrix.diagonal fun i => ((d i : Kˣ) : K)).mulVec ![0, 0, 1] = ![0, 0, 1]
    funext i
    fin_cases i <;> simp [hd, Matrix.mulVec_diagonal]
  have hyw : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec ![0, 0, 1] ≠
      ![0, 0, 1] := by
    intro h
    change (Matrix.diagonal fun i => ((f i : Kˣ) : K)).mulVec ![0, 0, 1] = ![0, 0, 1] at h
    have h2 := congrFun h 2
    simp [hf, Matrix.mulVec_diagonal] at h2
    exact hζ1 (by simpa using h2)
  exact CFSG.ClassicalGroups.SLnThreeLocal.two_le_pRank_of_mulVec (Subgroup.mem_top x)
    (Subgroup.mem_top y) hxo hyo hxy hxw hyw

theorem kfBigPrime_holds : KFBigPrime := by
  classical
  intro X _ _ k hk ⟨e⟩
  obtain ⟨p, hp, hp5, hpd⟩ := exists_prime_five_le_dvd_two_pow_sub_one hk
  have hcard : Nat.card (GaloisField 2 (2 * k)) = 2 ^ (2 * k) :=
    GaloisField.card 2 (2 * k) (by omega)
  haveI : Fintype (GaloisField 2 (2 * k)) := Fintype.ofFinite _
  have hunits : Nat.card (GaloisField 2 (2 * k))ˣ = 2 ^ (2 * k) - 1 := by
    rw [Nat.card_units, hcard]
  have hdvd : p ∣ Fintype.card (GaloisField 2 (2 * k))ˣ := by
    rw [← Nat.card_eq_fintype_card, hunits]
    exact hpd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card p hdvd
  refine ⟨p, hp, hp5, ?_⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by omega : 1 < p)
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _))]
  exact two_le_pRank_statedSL_three_of_orderOf hp hζ

noncomputable def statedProjEquivSelfOfCenter {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (Matrix.GeneralLinearGroup ι K)) (hH : Subgroup.center H = ⊥) :
    CFSG.Open.StatedProj H ≃* H := by
  have hS : (CFSG.Open.StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hgS
    rw [Subgroup.mem_subgroupOf] at hgS
    have hgc : g ∈ Subgroup.center (Matrix.GeneralLinearGroup ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hgS
    have hmem : (⟨g, hg⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_center_iff.1 hgc h.1)
    rw [hH] at hmem
    exact hmem
  exact (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot

theorem two_pow_mod_three_of_odd_aux {a : ℕ} (ha : Odd a) : 2 ^ a % 3 = 2 := by
  obtain ⟨m, rfl⟩ := ha
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem isL3OddType_of_specialLinear {X : Type} [Group X] {a : ℕ} (ha : Odd a)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 a)) : IsL3OddType X := by
  have ha0 : a ≠ 0 := ha.pos.ne'
  have hK : Nat.card (GaloisField 2 a) % 3 = 2 := by
    rw [GaloisField.card 2 a ha0]
    exact two_pow_mod_three_of_odd_aux ha
  have hZ := CFSG.RankThree.PartTwo.KFacts.center_statedSL_three_eq_bot hK
  exact ⟨a, ha, ⟨e.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _).trans
    ((statedProjEquivSelfOfCenter _ hZ).symm.trans
      (CFSG.PGLModel.projSLEquivStatedProj 3 _).symm))⟩⟩

theorem twoLe_of_specialLinear_even {X : Type} [Group X] [Finite X] {a : ℕ} (ha : Even a)
    (ha1 : 1 ≤ a) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 a)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨ω, h3, h1⟩ := CFSG.Quasithin.R3c.exists_cube_root_of_card_two_pow ha
    (GaloisField.card 2 a (by omega))
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _))]
  exact (CFSG.Quasithin.FFC.threeRank2_statedSL_three h3 h1).pRank_two_le

theorem twoLe_of_projSL_three_even {X : Type} [Group X] [Finite X] {a : ℕ} (ha : Even a)
    (ha1 : 1 ≤ a) (e : X ≃* projSL 3 (GaloisField 2 a)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨ω, h3, h1⟩ := CFSG.Quasithin.R3c.exists_cube_root_of_card_two_pow ha
    (GaloisField.card 2 a (by omega))
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (CFSG.PGLModel.projSLEquivStatedProj 3 _))]
  exact CFSG.Quasithin.R3c.two_le_pRank_three_statedProj_statedSL_three h3 h1

theorem twoLe_of_projSL {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] (e : X ≃* projSL n K) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (CFSG.PGLModel.projSLEquivStatedProj n K))]
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.psl_two_le_pRank_three hn

theorem twoLe_of_projSp_two {X : Type} [Group X] [Finite X] {a : ℕ}
    (e : X ≃* projSp 2 (GaloisField 2 a)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 _))]
  exact CFSG.Quasithin.R3c3.two_le_pRank_three_statedProj_statedSp_two

theorem twoLe_of_projSU_four {X : Type} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* projSU 4 2 a) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four (by norm_num)
    (by norm_num) (CFSG.RankThree.PartTwo.Sec21.statedClassicalModel_psu_of_mulEquiv_projSU ha e)

noncomputable def zSL2 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) :=
  ⟨Matrix.of ![![0, 1], ![1, 1]], by
    have h2 : (2 : GaloisField 2 1) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 2 1) 2
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : GaloisField 2 1) * h2⟩

theorem zSL2_pow_three : zSL2 ^ 3 = 1 := by
  have h2 : (2 : GaloisField 2 1) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 2 1) 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (Matrix.of ![![0, 1], ![1, 1]] : Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) ^ 3 = 1
  simp only [pow_three, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_add_one_eq_two, h2]

theorem zSL2_ne_one : zSL2 ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) =>
    (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) 0 1) h
  simp [zSL2] at h01

theorem zSL2_orderOf : orderOf zSL2 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime zSL2_pow_three zSL2_ne_one

theorem twoLe_of_projSp_three_one {X : Type} [Group X] [Finite X]
    (e : X ≃* projSp 3 (GaloisField 2 1)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (CFSG.Open.StatedSp 3 (GaloisField 2 1)) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    ((e.trans (CFSG.PGLModel.projSpEquivStatedProj 3 _)).trans
      (statedProjEquivSelfOfCenter _ hZ))]
  exact CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.two_le_pRank_of_block_mulSingle
    Nat.prime_three zSL2_orderOf (by decide : (0 : Fin 3) ≠ 1) (Subgroup.mem_top _)
    (Subgroup.mem_top _)

theorem twoLe_of_projOmegaMinus {X : Type} [Group X] [Finite X] {b c : GaloisField 2 1}
    (e : X ≃* projOmegaMinus 3 (GaloisField 2 1) b c) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have h := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three
    (K := GaloisField 2 1) (n := 4) le_rfl b c
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (GaloisField 2 1) b c))).symm)]
  exact le_trans (by norm_num) h

theorem twoLe_of_projSU_three_three {X : Type} [Group X] [Finite X]
    (e : X ≃* projSU 3 3 1) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : CFSG.Quasithin.IsPSU 3 3 1 X :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 2, inferInstance, inferInstance,
      by rw [GaloisField.card 3 2 (by norm_num)]; norm_num,
      ⟨e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 3 1)⟩⟩
  exact CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_isPSU_three_three hC

theorem twoLe_of_isTripleA6 {X : Type} [Group X] [Finite X]
    (hT : CFSG.RankThree.PartTwo.Sec19.IsTripleA6 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, he⟩ := hT
  obtain ⟨e⟩ := he
  exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center X) Nat.prime_three
    (by norm_num) (CFSG.Quasithin.R3c3.two_le_pRank_three_alt (by norm_num) e)

theorem kf3a_of_isoGTwoEven
    (hG2 : ∀ (m : ℕ) (X : Type) [Group X] [Finite X],
      CFSG.RankThree.PartTwo.Sec8.IsoGTwoEven X m → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) :
    KF3a := by
  intro X _ _ hX hnot
  obtain ⟨-, hmem⟩ := hX
  rcases hmem with hL | hS | hT
  · rcases hL with ⟨n, hn, h | h | h | hG⟩ | h | h | h | h | h | h | h | h | ⟨b, c, -, h⟩ | h
    · obtain ⟨e⟩ := h
      rcases Nat.even_or_odd n with he | ho
      · exact twoLe_of_specialLinear_even he hn e
      · exact (hnot (isL3OddType_of_specialLinear ho e)).elim
    · obtain ⟨e⟩ := h
      rcases Nat.even_or_odd n with he | ho
      · exact twoLe_of_projSL_three_even he hn e
      · exact (hnot ⟨n, ho, ⟨e⟩⟩).elim
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSp_two e
    · exact hG2 n X hG
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSU_four le_rfl e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSU_four (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSL (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSL (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSL (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSL (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSL (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSp_three_one e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projOmegaMinus e
    · obtain ⟨e⟩ := h
      exact CFSG.Quasithin.R3c3.two_le_pRank_three_alt (by norm_num) e
  · rcases hS with h | h
    · obtain ⟨e⟩ := h
      exact CFSG.Quasithin.R3c3.two_le_pRank_three_alt (by norm_num) e
    · obtain ⟨e⟩ := h
      exact twoLe_of_projSU_three_three e
  · exact twoLe_of_isTripleA6 hT

theorem kf2_of_center_eq_bot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Nat.card (Subgroup.center X) ∣ 3 ∧ (3 ∣ Nat.card (Subgroup.center X) →
      (∃ n : ℕ, Even n ∧ 1 ≤ n ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ∨
        CFSG.RankThree.PartTwo.Sec19.IsTripleA6 X) := by
  rw [h, Subgroup.card_bot]
  exact ⟨one_dvd _, fun h3 => absurd h3 (by norm_num)⟩

theorem center_eq_bot_of_iso_simple {X M : Type} [Group X] [Group M] [IsSimpleGroup M]
    (e : X ≃* M) (hperf : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  exact CFSG.RankThree.PartTwo.KFacts.false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1

theorem center_eq_bot_of_iso_center {X M : Type} [Group X] [Group M] (e : X ≃* M)
    (hM : Subgroup.center M = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  exact CFSG.RankThree.PartTwo.KFacts.false_of_center_eq_bot_of_mulEquiv e hM hz hz1

theorem center_eq_bot_of_projSL {X : Type} [Group X] (hperf : Group.IsPerfect X) {n a : ℕ}
    (hn : 2 ≤ n) (ha : 1 ≤ a) (hna : n = 2 → 2 ≤ a)
    (e : X ≃* projSL n (GaloisField 2 a)) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup (projSL n (GaloisField 2 a)) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ n 2 a
      (CFSG.RankThree.PartTwo.Sec21.statedClassicalModel_psl_of_mulEquiv_projSL hn ha hna
        (MulEquiv.refl _))).2
  exact center_eq_bot_of_iso_simple e hperf

theorem kf2_of_isoGTwoEven
    (hG2 : ∀ (m : ℕ) (X : Type) [Group X],
      CFSG.RankThree.PartTwo.Sec8.IsoGTwoEven X m → Subgroup.center X = ⊥) : KF2 := by
  intro X _ _ hX
  obtain ⟨hq, hmem⟩ := hX
  obtain ⟨hperf, -, -⟩ := hq
  rcases hmem with hL | hS | hT
  · rcases hL with ⟨n, hn, h | h | h | hG⟩ | h | h | h | h | h | h | h | h | ⟨b, c, hbc, h⟩ | h
    ·
      obtain ⟨e⟩ := h
      haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
      have hcardF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
      have hc := CFSG.RankThree.PartTwo.Sec12.card_center_eq_of_mulEquiv e
      rw [hc, CFSG.HardMathSupport.Foote.Proving.natCard_center_SL3_field, hcardF]
      refine ⟨Nat.gcd_dvd_left _ _, fun h3 => Or.inl ?_⟩
      have h3' : 3 ∣ 2 ^ n - 1 := dvd_trans h3 (Nat.gcd_dvd_right _ _)
      have hev : Even n := by
        rcases Nat.even_or_odd n with he | ho
        · exact he
        · have := two_pow_mod_three_of_odd_aux ho
          omega
      exact ⟨n, hev, hn, ⟨e⟩⟩
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) hn
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      have hZ : Subgroup.center (CFSG.Open.StatedSp 2 (GaloisField 2 n)) = ⊥ :=
        CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_center
        ((e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 _)).trans
          (statedProjEquivSelfOfCenter _ hZ)) hZ)
    ·
      exact kf2_of_center_eq_bot (hG2 n X hG)
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (projSU 4 2 1) :=
        CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSU le_rfl le_rfl
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_simple e hperf)
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (projSU 4 2 3) :=
        CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSU le_rfl (by norm_num)
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_simple e hperf)
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) le_rfl
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) le_rfl
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) le_rfl
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      exact kf2_of_center_eq_bot (center_eq_bot_of_projSL hperf (by norm_num) le_rfl
        (fun h => absurd h (by norm_num)) e)
    ·
      obtain ⟨e⟩ := h
      have hZ : Subgroup.center (CFSG.Open.StatedSp 3 (GaloisField 2 1)) = ⊥ :=
        CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_center
        ((e.trans (CFSG.PGLModel.projSpEquivStatedProj 3 _)).trans
          (statedProjEquivSelfOfCenter _ hZ)) hZ)
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
          (CFSG.Open.StatedQuadMinus 4 (GaloisField 2 1) b c))) :=
        CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
          (n := 4) (K := GaloisField 2 1) le_rfl hbc
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_simple
        (e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (GaloisField 2 1) b c))).symm) hperf)
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
        alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
      exact kf2_of_center_eq_bot (center_eq_bot_of_iso_simple e hperf)
  ·
    exact kf2_of_center_eq_bot
      (CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.center_eq_bot_of_isSmall194 hS hperf)
  ·
    have hc := hT.1
    exact ⟨by rw [hc], fun _ => Or.inr hT⟩

theorem kf3a_holds :
    KF3a :=
  kf3a_of_isoGTwoEven fun _ _ _ _ hX => by
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hX
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center _) Nat.prime_three
      (by norm_num) CFSG.LieType.Chevalley.two_le_pRank_three_adjointQuotient_G2

theorem kf2_holds :
    KF2 :=
  kf2_of_isoGTwoEven fun _ _ _ hX => by
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := hX
    exact center_eq_bot_of_iso_center e CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

end CFSG.RankThree.PartTwo.Late
