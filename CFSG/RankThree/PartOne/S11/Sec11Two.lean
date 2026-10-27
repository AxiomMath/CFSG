module

public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial

@[expose] def Sec6SixFieldAutomorphismPlane : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ c ∈ A, c ≠ 1 → ∀ J ∈ sectionTenAt p (sectionTenZeroStar p A ∩ sectionTenTwo p A) c,
      EvenLieType (J ⧸ Subgroup.center J) → ¬ p ∣ Nat.card (Subgroup.center J) →
      ∃ a d : G, a ∈ A ∧ d ∈ A ∧ d ≠ 1 ∧
        A = Subgroup.zpowers a ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧
        Subgroup.zpowers d = A ⊓ J ∧ InducesFieldAut p a J

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thetaQuotientAction_eq_conj_of_mem {p : ℕ} {A L : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (L : Set G)) (a : A) (ha : (a : G) ∈ L) :
    thetaQuotientAction p hA a =
      MulAut.conj ((⟨a, ha⟩ : L) : L ⧸ aschbacherSolvableCore p L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    change thetaQuotientConj p L ⟨a, hA a.2⟩ _ = _
    rw [thetaQuotientConj_mk, MulAut.conj_apply]
    have : (L.normalizerMonoidHom ⟨a, hA a.2⟩ l : L) = ⟨a, ha⟩ * l * ⟨a, ha⟩⁻¹ := by
      apply Subtype.ext
      simp
    rw [this]
    rfl

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {c x : G} (hxc : x * c = c * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (show Commute c x from hxc.symm) k).eq

theorem inSec11Two_of_inspections (hS : SchreierFor InCatalog) (h107 : InSec10Seven)
    (h108 : InSec10EightMoving) (h66 : Sec6SixFieldAutomorphismPlane) : InSec11Two := by
  intro G _ _ p A h c hcA hc1 J hJ
  have hJ02 : J ∈ sectionTenZeroStar p A := hJ.1.1
  have hJ2 : J ∈ sectionTenTwo p A := hJ.1.2
  have hJc : J ∈ thetaComponentsAt p c := hJ.2
  have hEven : EvenLieType (J ⧸ Subgroup.center J) := h107 G p A h J hJ02
  have hp := sectionTenSetup_prime h
  obtain ⟨hq, hAJ, -⟩ := moving_maximal_data_at hS h hJ02 hcA hc1 hJc
  have hθ : aschbacherSolvableCore p J ≤ Subgroup.center J := theta_le_center_of_quasisimple hp hq
  have hnZ : ¬ p ∣ Nat.card (Subgroup.center J) := by
    intro hpZ
    rcases h108 G p A h c hcA hc1 J ⟨hJ02, hJc⟩ with hsimple | ⟨hp5, -, -, -, hcont⟩
    ·
      have hN : ((Subgroup.center J).map (QuotientGroup.mk' (aschbacherSolvableCore p J))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      have := hsimple
      have := hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.center J).map (QuotientGroup.mk' (aschbacherSolvableCore p J))) with
        hbot | htop
      · have hle : Subgroup.center J ≤ aschbacherSolvableCore p J := by
          have := (Subgroup.map_eq_bot_iff _).mp hbot
          rwa [QuotientGroup.ker_mk'] at this
        have heq : aschbacherSolvableCore p J = Subgroup.center J := le_antisymm hθ hle
        have hnd := (solvable_prime_complement_core_characterization (H := J) hp).2.2.1
        rw [heq] at hnd
        exact hnd hpZ
      · exfalso
        obtain ⟨a, b, hab⟩ := hq.2.2
        apply hab
        induction a using QuotientGroup.induction_on with
        | H x =>
          have hx : (QuotientGroup.mk' (aschbacherSolvableCore p J)) x ∈
              (Subgroup.center J).map (QuotientGroup.mk' (aschbacherSolvableCore p J)) := by
            rw [htop]; exact Subgroup.mem_top _
          obtain ⟨z, hz, hzx⟩ := hx
          have hzx' : z⁻¹ * x ∈ aschbacherSolvableCore p J := by
            rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hzx
            exact hzx
          have hxz : x ∈ Subgroup.center J := by
            have := (Subgroup.center J).mul_mem hz (hθ hzx')
            simpa using this
          have : (x : J ⧸ Subgroup.center J) = 1 := (QuotientGroup.eq_one_iff x).mpr hxz
          rw [this, one_mul, mul_one]
    ·
      subst hp5
      have hAe : IsElementaryAbelian 5 A := h.2.2.2.2.2.2.1
      obtain ⟨-, S, hSL, hS1, hS2, hAS, -⟩ := hJ02.1
      have hAle : ∀ x ∈ A, x ∈ J := by
        intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]; exact J.one_mem
        · have hxp : x ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) x hx
          have hxord : orderOf x = 5 := by
            rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hxp) with h2 | h2
            · exact absurd (orderOf_eq_one_iff.mp h2) hx1
            · exact h2
          have hxc : x * c = c * x := by
            have := hAe.is_comm.comm ⟨x, hx⟩ ⟨c, hcA⟩
            simpa using congrArg Subtype.val this
          have hXle : Subgroup.zpowers x ≤ A := (Subgroup.zpowers_le).mpr hx
          have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
            (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_commute hxc)
          have hXJ := hcont (Subgroup.zpowers x) hXN (by rw [Nat.card_zpowers, hxord])
            ⟨S, hS1, hS2, hSL, hXle.trans hAS⟩
          exact hXJ (Subgroup.mem_zpowers x)
      have hone : J ∈ sectionTenOne 5 A := by
        refine ⟨(sectionTenZeroStar_subset 5 A).2.2.1 hJ02.2, hAJ, ?_⟩
        rintro _ ⟨a, rfl⟩
        exact ⟨_, (thetaQuotientAction_eq_conj_of_mem hAJ a (hAle a a.2)).symm⟩
      exact hJ2.2 hone
  obtain ⟨a, d, haA, hdA, hd1, hAeq, hdJ, hfa⟩ := h66 G p A h c hcA hc1 J hJ hEven hnZ
  exact ⟨hEven, hnZ, a, d, haA, hdA, hd1, hAeq, hdJ, hfa⟩

end CFSG.RankThree.PartOne
