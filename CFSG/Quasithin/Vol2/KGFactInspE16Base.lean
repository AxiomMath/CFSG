module

public import CFSG.Quasithin.Vol2.KGFactInspBase
public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Ord

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
  StatedScalars
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

structure E16Cfg {X : Type} [Group X] [Finite X] (S R K : Subgroup X) : Prop where
  normal : S.Normal
  simple : IsSimpleGroup ↥S
  noncomm : ∃ a b : ↥S, a * b ≠ b * a
  list : A23List ↥S
  cent : Subgroup.centralizer (S : Set X) = ⊥
  le : K ≤ S
  perfect : ⁅K, K⁆ = K
  le_normalizer : K ≤ Subgroup.normalizer (R : Set X)
  normalizer_le : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X)
  chi : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ 2 ∧
    ∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker
  eq_core : R = pCoreOf 2 K
  elem : IsElemAbelian 2 R
  card : Nat.card ↥R = 2 ^ 4

namespace E16Cfg

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X}

theorem R_le_S (h : E16Cfg S R K) : R ≤ S :=
  h.eq_core ▸ (Subgroup.map_subtype_le _).trans h.le

theorem isPGroup (h : E16Cfg S R K) : IsPGroup 2 ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card h.card

theorem ne_bot (h : E16Cfg S R K) : R ≠ ⊥ := fun hb => by
  have := h.card
  rw [hb, Subgroup.card_bot] at this
  norm_num at this

theorem cfg (h : E16Cfg S R K) : KGInsp43.Cfg S R K 2 :=
  ⟨h.normal, h.simple, h.cent, le_rfl, h.ne_bot, h.isPGroup, h.le, h.perfect, h.le_normalizer,
    h.normalizer_le, h.chi⟩

theorem sixteen_dvd (h : E16Cfg S R K) : 16 ∣ Nat.card ↥S := by
  have := Subgroup.card_dvd_of_le h.R_le_S
  rwa [h.card] at this

theorem five_dvd (h : E16Cfg S R K) : 5 ∣ Nat.card ↥S := by
  obtain ⟨F, _, _, hF, χ, hχ, -⟩ := h.chi
  have h60 : Nat.card SL(2, F) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hF]
    norm_num
  have hK : 60 ∣ Nat.card ↥K := h60 ▸ Subgroup.card_dvd_of_surjective hχ
  exact ((by norm_num : 5 ∣ 60).trans hK).trans (Subgroup.card_dvd_of_le h.le)

theorem four_le_pRank_two (h : E16Cfg S R K) : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pRank_top_subtype]
  exact CFSG.SectionRank.le_pRank (by norm_num) h.R_le_S h.elem h.card

theorem false_of_pRank_two_le (h : E16Cfg S R K)
    (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup ↥S) ≤ 2) : False := by
  have := h.four_le_pRank_two
  omega

theorem false_of_two_le_pRank_three (h3 : CFSG.Open.pRank 3 S ≤ 1)
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥S)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pRank_top_subtype] at h
  omega

end E16Cfg

theorem pRank_two_statedProj_le_two {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj H)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  have hZ : ¬ 2 ∣ Nat.card ↥((StatedScalars (Fin 3) K).subgroupOf H) := by
    intro h2Z
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥((StatedScalars (Fin 3) K).subgroupOf H)) 2 h2Z
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp z.2
    have hzH := hdet _ (z : ↥H).2
    have hz2 : ((z : ↥H) : GL (Fin 3) K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
      rfl
    rw [← hc] at hzH hz2
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hzH
    have hc2 : (c : K) ^ 2 = 1 := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hz2
      simpa [Matrix.GeneralLinearGroup.coe_scalar, sq] using this
    have hc1 : (c : K) = 1 := by
      have h3 : (c : K) ^ 3 = (c : K) * (c : K) ^ 2 := by ring
      rw [hc2, mul_one] at h3
      rw [← h3, hzH]
    have hz1 : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hc]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hc1]
      simp
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  rw [CFSG.SectionRank.pRank_quotient_eq _ hZ]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hle : Nat.card (E.map H.subtype) ≤ 4 := by
    apply CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← sq, hE.2 x hx, map_one]
    · rintro _ ⟨x, -, rfl⟩
      exact hdet _ x.2
  rw [Subgroup.card_map_of_injective H.subtype_injective] at hle
  simpa using hle

theorem pRank_two_le_two_of_psl3_odd {A : Type} [Group A] [Finite A] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : StatedClassicalModel A .PSL 3 p f) :
    CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  refine pRank_two_statedProj_le_two hodd fun x hx => ?_
  have hle : StatedSL 3 K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    rw [StatedSL, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext hy
  have := hle hx
  rw [MonoidHom.mem_ker] at this
  exact congrArg Units.val this

theorem pRank_two_le_two_of_psu3_odd {A : Type} [Group A] [Finite A] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : StatedClassicalModel A .PSU 3 p f) :
    CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow.pow
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  refine pRank_two_statedProj_le_two hodd fun x hx => ?_
  have hle : StatedSU 3 (p ^ f) K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
    rw [StatedSU, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext hy.1
  have := hle hx
  rw [MonoidHom.mem_ker] at this
  exact congrArg Units.val this

theorem two_pow_mod_five_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem not_five_dvd_card_psl3_of_odd {A : Type} [Group A] {f : ℕ} (hf : Odd f)
    (hm : StatedClassicalModel A .PSL 3 2 f) : ¬ 5 ∣ Nat.card A := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  rw [Nat.card_congr
    (e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)).toEquiv]
  intro h5
  have hmul := CFSG.QuasithinUnique.Unc25G2.A312Sub.card_projectiveSL_three_mul (K := K)
  rw [hK] at hmul
  have h5' : 5 ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) :=
    hmul ▸ h5.mul_right _
  have hq := two_pow_mod_five_of_odd hf
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hq2 : (2 ^ f) ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  have hq3 : (2 ^ f) ^ 3 % 5 = 3 ∨ (2 ^ f) ^ 3 % 5 = 2 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h] <;> norm_num
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  have h1' : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ hq1
  have hp5 : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp5).mp h5' with h | h
  · omega
  · rcases (Nat.Prime.dvd_mul hp5).mp h with h | h <;> omega

end CFSG.Quasithin.H13.KGInsp4316
