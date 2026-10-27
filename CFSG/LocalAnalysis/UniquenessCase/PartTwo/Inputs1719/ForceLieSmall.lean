module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorGroup
public import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bA6
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
public import CFSG.RankThree.PartOne.SEITZ7.D4CentN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
public import CFSG.ClassicalInvolution.Q3.Q3YAbs
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1920ForceThreeA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem lieModel_of_cover_L32 {X Q : Type} [Group X] [Finite X] [Group Q]
    (hq : CFSG.Open.IsQuasisimple X) (h2 : CFSG.pCore 2 X = ⊥)
    (hQ : Nonempty (Q ≃* X ⧸ center X)) (hL : LieModel Q .PSL 3 2 1) :
    LieModel X .PSL 3 2 1 := by
  obtain ⟨e⟩ := hQ
  obtain ⟨g⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hL.statedClassicalModel_of_ne_zero (by norm_num))
  obtain ⟨π, hπ, hker⟩ := CFSG.AGLEmbedding.exists_surjective_ker_eq_center (e.symm.trans g)
  have : Group.IsPerfect X := ⟨hq.1⟩
  have hodd : Odd (Nat.card π.ker) := by rw [hker]; exact s15_Three_odd_center h2
  have hbot := CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor.ker_eq_bot_of_perfect_odd_cover
    π hπ hker.le hodd
  have hZ : center X = ⊥ := hker ▸ hbot
  obtain ⟨f⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hZ e.symm
  exact LieModel.of_mulEquiv f.symm hL

theorem false_of_cover_A6 {X Q : Type} [Group X] [Finite X] [Group Q] {Y : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple X) (h2 : CFSG.pCore 2 X = ⊥)
    (hQ : Nonempty (Q ≃* X ⧸ center X)) (hA : IsAlt Q 6) (hpar : IsNontrivialParabolic X Y)
    (hT1 : ∀ P : Subgroup X, IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x)
    (hT2 : (∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y) :
    False := by
  obtain ⟨e⟩ := hQ
  obtain ⟨a⟩ := hA
  obtain ⟨π, hπ, hker⟩ := CFSG.AGLEmbedding.exists_surjective_ker_eq_center (e.symm.trans a)
  have : Group.IsPerfect X := ⟨hq.1⟩
  have hodd : Odd (Nat.card π.ker) := by rw [hker]; exact s15_Three_odd_center h2
  obtain ⟨-, h67⟩ := CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num)
    (by norm_num) π hπ hker.le hodd
  rcases h67 (Or.inl rfl) with h1 | h3
  · have hZ : center X = ⊥ := by rw [← hker]; exact Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨f⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hZ (e.symm.trans a)
    have hinn : ∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range :=
      CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.mem_range_conj_of_mulEquiv f
        CFSG.LocalAnalysis.GLTheoremA.alt6_aut_three_inner
    obtain ⟨S, hS⟩ := exists_sylow_three_normalizer_le hT2 hinn hZ
    obtain ⟨T, hT⟩ := exists_sylow_two_le_of_isNontrivialParabolic hpar
    have hcard : Nat.card X = 360 := by
      rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h45 : Y.index ∣ 45 :=
      index_dvd_of_sylow_le (p := 2) (k := 3) (by rw [hcard]; norm_num) (by norm_num) T hT
    have h40 : Y.index ∣ 40 :=
      index_dvd_of_sylow_le (p := 3) (k := 2) (by rw [hcard]; norm_num) (by norm_num) S
        (le_normalizer.trans hS)
    have hmod : Y.index ≡ 1 [MOD 3] :=
      CFSG.RankThree.PartOne.SEITZ7.index_modEq_one_of_normalizer_le S hS
    have h5 : Y.index ∣ 5 := Nat.dvd_gcd h45 h40
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with h | h
    · exact hpar.2.1 (Subgroup.index_eq_one.mp h)
    · rw [h] at hmod
      exact absurd hmod (by decide)
  · obtain ⟨P, hP, x, hx, y, hy, hx3, hy3, hxy⟩ :=
      exists_noncommute_three_of_isA6ModZ3 ⟨⟨hq, ⟨e.symm.trans a⟩⟩, by rw [← hker]; exact h3⟩
    exact hxy (hT1 P hP x hx y hy hx3 hy3)

theorem false_of_cover_L42 {X Q : Type} [Group X] [Finite X] [Group Q] {Y : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple X) (h2 : CFSG.pCore 2 X = ⊥)
    (hQ : Nonempty (Q ≃* X ⧸ center X)) (hL : LieModel Q .PSL 4 2 1)
    (hpar : IsNontrivialParabolic X Y)
    (hT2 : (∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y) :
    False := by
  obtain ⟨e⟩ := hQ
  obtain ⟨a⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hL
  obtain ⟨π, hπ, hker⟩ := CFSG.AGLEmbedding.exists_surjective_ker_eq_center (e.symm.trans a)
  have : Group.IsPerfect X := ⟨hq.1⟩
  have hodd : Odd (Nat.card π.ker) := by rw [hker]; exact s15_Three_odd_center h2
  obtain ⟨h58, -⟩ := CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num)
    (by norm_num) π hπ hker.le hodd
  have hZ : center X = ⊥ := hker ▸ h58 (Or.inr rfl)
  obtain ⟨f⟩ := CFSG.GH74.Generic.nonempty_mulEquiv_of_center_eq_bot hZ e.symm
  obtain ⟨K, _, _, hK, ⟨g⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one
      (hL.statedClassicalModel_of_ne_zero (by norm_num))
  have hinn : ∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range :=
    CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.mem_range_conj_of_mulEquiv (f.trans g)
      fun β hβ => by
        obtain ⟨y, hy⟩ :=
          CFSG.RankThree.PartTwo.Sec21.Hering214.inner_of_pow_three_eq_one hK (by norm_num) hβ
        exact MonoidHom.mem_range.mpr ⟨y, hy.symm⟩
  obtain ⟨S, hS⟩ := exists_sylow_three_normalizer_le hT2 hinn hZ
  obtain ⟨T, hT⟩ := exists_sylow_two_le_of_isNontrivialParabolic hpar
  have hcard : Nat.card X = 20160 := by
    rw [Nat.card_congr (f.trans a).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h315 : Y.index ∣ 315 :=
    index_dvd_of_sylow_le (p := 2) (k := 6) (by rw [hcard]; norm_num) (by norm_num) T hT
  have h2240 : Y.index ∣ 2240 :=
    index_dvd_of_sylow_le (p := 3) (k := 2) (by rw [hcard]; norm_num) (by norm_num) S
      (le_normalizer.trans hS)
  have hmod : Y.index ≡ 1 [MOD 3] :=
    CFSG.RankThree.PartOne.SEITZ7.index_modEq_one_of_normalizer_le S hS
  have h35 : Y.index ∣ 35 := Nat.dvd_gcd h315 h2240
  obtain ⟨n, hn⟩ : ∃ n, Y.index = n := ⟨_, rfl⟩
  rw [hn] at h35 hmod
  have hle : n ≤ 35 := Nat.le_of_dvd (by norm_num) h35
  unfold Nat.ModEq at hmod
  have h17 : n = 1 ∨ n = 7 := by interval_cases n <;> omega
  rcases h17 with rfl | rfl
  · exact hpar.2.1 (Subgroup.index_eq_one.mp hn)
  · have hdvd := Subgroup.index_normalCore_dvd_factorial_index (H := Y)
    rw [hn] at hdvd
    have := CFSG.ClassicalInvolution.Q3.Q3Y.isSimpleGroup_of_center_eq_bot hq hZ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, hcard] at hdvd
      exact absurd hdvd (by decide)
    · exact hpar.2.1 (eq_top_iff.mpr (ht ▸ Y.normalCore_le))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
