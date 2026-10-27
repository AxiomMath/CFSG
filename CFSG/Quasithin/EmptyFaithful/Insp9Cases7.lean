module

public import CFSG.Quasithin.EmptyFaithful.Insp9Top
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases2
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace Insp9

section Core

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem Data.not_le_center (h : Data D₁ D₂ J N) : ¬ N ≤ Subgroup.center D := by
  intro hc
  have hJ : J ≤ Subgroup.center D := h.J_le_N.trans hc
  have hbot : ⁅oTwoUpper D₂, J⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x _ j hj
    have := Subgroup.mem_center_iff.mp (hJ hj) x
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr this
  exact h.oTwoUpper_ne_bot (h.comm ▸ hbot)

theorem Data.N_eq_top_of_qs (h : Data D₁ D₂ J N) (hq : CFSG.IsQuasisimple D) : N = ⊤ := by
  have := h.normal
  exact (qs_normal_le_center_or_top hq N).resolve_left h.not_le_center

theorem case10_core (h : Data D₁ D₂ J N) (hs : B56Setting D N) (hq : CFSG.IsQuasisimple D)
    {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) (hp3 : p ^ 3 ∣ Nat.card D)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 5) : InspGoal D N := by
  have hN := h.N_eq_top_of_qs hq
  have hqsN : CFSG.IsQuasisimple ↥N :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (topEquivOfEq hN).symm hq
  have hql := hs.ql_of_quasisimple hqsN
  have h6 : ¬ 2 ^ 6 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 6) (by norm_num)
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := by
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv]
    exact fun hd => h6 ((Nat.pow_dvd_pow 2 (by norm_num : 6 ≤ 8)).trans hd)
  rcases inspList_or_bad hql h8 with hgood | hbad
  · exact Or.inr ⟨hgood, by rw [hN]; exact le_top⟩
  · exfalso
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv] at hbad
    have hp130 : p < 130 := by
      by_contra hcon
      have hle : p ^ 3 ≤ 2097024 := by
        have h1 : p ^ 3 ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos hp3
        have h2 : Nat.card D ≤ 2097024 := by
          revert hbad
          unfold badQL
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_singleton]
          omega
        omega
      have : 130 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    have hdec : ∀ q ∈ Finset.range 130, (q % 8 = 3 ∨ q % 8 = 5) → ∀ n ∈ badQL,
        q ^ 3 ∣ n → 2 ^ 6 ∣ n := by
      unfold badQL; decide +kernel
    exact h6 (hdec p (Finset.mem_range.mpr hp130) hp _ hbad hp3)

end Core

theorem isQuasisimple_of_perfect_of_simple {S : Type} [Group S] [Group.IsPerfect S]
    [IsSimpleGroup S] : CFSG.IsQuasisimple S := by
  refine CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup ?_
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative S ⟨⟨hcon⟩⟩

theorem isQuasisimple_statedSL_three (K : Type) [Field K] :
    CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le le_rfl K

theorem isQuasisimple_statedProj_statedSL_three (K : Type) [Field K] [Finite K] :
    CFSG.IsQuasisimple (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  have hperf : Group.IsPerfect ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) := (isQuasisimple_statedSL_three K).1
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) :=
    (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.isSimpleGroup
  exact isQuasisimple_of_perfect_of_simple

theorem isQuasisimple_statedSU_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) : CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p K) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSU_three_of_prime hp hp3 K hK

theorem isQuasisimple_statedProj_statedSU_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) :
    CFSG.IsQuasisimple (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p K) := (isQuasisimple_statedSU_three hp hp3 K hK).1
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) := by
    have h1 := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p 1
      (by simpa using hK) 3 le_rfl (by intro h; simp at h; omega)
    rw [pow_one] at h1
    exact h1
  exact isQuasisimple_of_perfect_of_simple

theorem pow_three_dvd_card_statedSL (K : Type) [Field K] [Finite K] :
    Nat.card K ^ 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    show 3 * (3 - 1) / 2 = 3 from rfl]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_card_statedProj_statedSL (K : Type) [Field K] [Finite K] :
    Nat.card K ^ 3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd 3 (Nat.card K - 1) ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
    ((Nat.gcd_dvd_right 3 _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)).mul_right _
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_card_statedSU {p : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) : p ^ 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p K) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.OddCover.card_statedSU_three_eq_mul hK]
  exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _

theorem pow_three_dvd_card_statedProj_statedSU {p : ℕ} (hp : p.Prime) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) : p ^ 3 ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := p) (f := 1)
    (n := 3) hp le_rfl (by simpa using hK) (by norm_num)
  simp only [pow_one] at h
  have e2 : ((((p : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) = p ^ 2 - 1 := by
    have : (1 : ℕ) ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, show (((p : ℕ) : ℤ) ^ 2 - 1) =
      (((p ^ 2 - 1 : ℕ)) : ℤ) by push_cast [this]; ring, Int.toNat_natCast]
  have e3 : ((((p : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat) = p ^ 3 + 1 := by
    rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num, show (((p : ℕ) : ℤ) ^ 3 - -1) =
      ((p ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  rw [h, show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), e2, e3]
  have h1 : Nat.gcd 3 (p + 1) ∣ p ^ 3 + 1 := by
    refine (Nat.gcd_dvd_right 3 (p + 1)).trans ?_
    simpa using Odd.nat_add_dvd_pow_add_pow p 1 (by decide : Odd 3)
  have hg : Nat.gcd 3 (p + 1) ∣ (p ^ 2 - 1) * (p ^ 3 + 1) := h1.mul_left _
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem isSLEps3_qs_dvd {D : Type} [Group D] [Finite D] {p : ℕ} (h : F6.IsSLEps3 p D) :
    CFSG.IsQuasisimple D ∧ p ^ 3 ∣ Nat.card D := by
  obtain ⟨hp, K, _, _, h1 | h3⟩ := h
  · obtain ⟨hmod, hK, he | he⟩ := h1
    · obtain ⟨e⟩ := he
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_statedSL_three K), ?_⟩
      rw [Nat.card_congr e.toEquiv, ← hK]
      exact pow_three_dvd_card_statedSL K
    · obtain ⟨e⟩ := he
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (isQuasisimple_statedProj_statedSL_three K), ?_⟩
      rw [Nat.card_congr e.toEquiv, ← hK]
      exact pow_three_dvd_card_statedProj_statedSL K
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨hmod, hK, he | he⟩ := h3
    · obtain ⟨e⟩ := he
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (isQuasisimple_statedSU_three hp hp3 K hK), ?_⟩
      rw [Nat.card_congr e.toEquiv]
      exact pow_three_dvd_card_statedSU hp K hK
    · obtain ⟨e⟩ := he
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (isQuasisimple_statedProj_statedSU_three hp hp3 K hK), ?_⟩
      rw [Nat.card_congr e.toEquiv]
      exact pow_three_dvd_card_statedProj_statedSU hp K hK

theorem inspCase10 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseTen H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 5 := by
    rcases hP with hP | hP
    · rw [hP.card_inf]; norm_num
    · rw [inf_comm, hP.card_inf]; norm_num
  obtain ⟨p, hp8, hpS⟩ : ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ F6.IsSLEps3 p D := by
    rcases hP with hP | hP
    · exact hP.1
    · exact hP.1
  obtain ⟨hq, hp3⟩ := isSLEps3_qs_dvd hpS
  exact case10_core h hs hq hp8 hp3 hT

end Insp9

end CFSG.Quasithin
