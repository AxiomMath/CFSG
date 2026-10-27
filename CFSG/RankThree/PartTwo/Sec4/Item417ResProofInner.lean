module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTheta
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec4.Census.FromTheoremThree
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)


namespace Res417

variable {G : Type} [Group G] [Finite G]

theorem isSLThreePiTheta_of_isoLThreePi
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hG : SectionFourHyp G)
    {L : Subgroup G} (hL : IsComponent L) {c : G} (hcL : c ∈ L)
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : orderOf c = 3) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hpi : IsoLThreePi (L ⧸ Subgroup.center L) p e) : IsSLThreePiTheta L := by
  have hp : p.Prime := Fact.out
  have hθZ := aschbacherSolvableCore_le_center hL.1
  obtain ⟨hqX, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hL.1
    (aschbacherSolvableCore 3 L) hθZ
  let eZ : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃*
      L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hθZ)
  have hpiX := isoLThreePi_congr eZ hpi
  have hZ3 := Census.isPGroup_center_thetaQuotient L
  have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC y y.2)
  have hZne : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≠ ⊥ := by
    intro hbot
    have hmem : ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [hcen]
      exact ⟨_, hcZ, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
    apply hθ3
    have hord : orderOf (⟨⟨c, hcL⟩, hmem⟩ : aschbacherSolvableCore 3 L) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3]
    have h := orderOf_dvd_natCard (⟨⟨c, hcL⟩, hmem⟩ : aschbacherSolvableCore 3 L)
    rwa [hord] at h
  have hq3 : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
    rcases hpi with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hbd : p = 2 ∨ e ≤ 2 := by
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    right
    have hp3 : p ≠ 3 := by
      rintro rfl
      have : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      omega
    have hp3' : 3 < p := Census.three_lt_of_prime hp hp2 hp3
    have hZ48 := card_center_dvd_forty_eight hGA hL.1 he hpi
    have hpZ : ¬ p ∣ Nat.card (Subgroup.center L) := by
      intro hpd
      have h48 := (Nat.Prime.dvd_mul hp).mp
        ((hpd.trans hZ48).trans (by norm_num : (48 : ℕ) ∣ 2 ^ 4 * 3))
      rcases h48 with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
        exact hp2 this
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    have hloc : localRank p (L ⧸ Subgroup.center L) < 3 :=
      ((Classical2.localRank_quotient_le hp hp2 _ hpZ).trans
        (localRank_subgroup_le hp L)).trans_lt (hG.localRank_lt p hp hp3')
    rcases hpi with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have : Finite (projSL 3 (GaloisField p e)) := Finite.of_equiv _ φ.toEquiv
      have h1 := Census.le_localRank_projSL_three hp2 he
      rw [← Census.localRank_eq_of_mulEquiv φ hp] at h1
      omega
    · have : Finite (projSU 3 p e) := Finite.of_equiv _ φ.toEquiv
      have h1 := Census.le_localRank_projSU_three hp2 he
      rw [← Census.localRank_eq_of_mulEquiv φ hp] at h1
      omega
  have hEps := Census.coverSLThree46 _ hqX hZ3 hZne p e he hbd hpiX
  exact ⟨p, e, inferInstance, he,
    Or.inl (KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hEps hq3 hZne)⟩

end Res417

open Res417

section Certs


@[expose] def IsInnerInConf417 {G : Type} [Group G] [Finite G] (L A E : Subgroup G) (c : G)
    (m : ℕ) : Prop :=
  SectionFourHyp G ∧ CFSG.pCore 2 G = ⊥ ∧ IsComponent L ∧
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) ∧
    IsQuad417 L A E c m ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
    (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∧
    ¬ IsSLThreePiTheta L ∧ (∀ a ∈ A, ¬ InducesOuterTheta a L) ∧ c ∈ L

@[expose] def Item417InA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6)) → Alt417 L A m

@[expose] def Item417InA7M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      (Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.M22)) → Alt417 L A m

@[expose] def Item417InG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 3 1 → Alt417 L A m

@[expose] def Item417InU43McL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      (Nonempty (L ⧸ Subgroup.center L ≃* projSU 4 3 1) ∨
        Nonempty (L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.McL)) → Alt417 L A m

@[expose] def Item417InJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      Nonempty (L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.J3) → Alt417 L A m

@[expose] def Item417InON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerInConf417 L A E c m →
      Nonempty (L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.ON) → Alt417 L A m

theorem item4_17InnerIn_of (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h43 : Item4_3) (hA6 : Item417InA6) (hA7 : Item417InA7M22) (hG2 : Item417InG2)
    (hU43 : Item417InU43McL) (hJ3 : Item417InJ3) (hON : Item417InON) : Item4_17InnerIn := by
  intro G _ _ hG h2 L hL hstar A E c m hq hAL h1 hSL hout hcL
  have hconf : IsInnerInConf417 L A E c m := ⟨hG, h2, hL, hstar, hq, hAL, h1, hSL, hout, hcL⟩
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hq.2.2.1 ▸ Subgroup.mem_zpowers c
    exact this.2
  have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC y y.2)
  have h3Z : 3 ∣ Nat.card (Subgroup.center L) := by
    have hord : orderOf (⟨⟨c, hcL⟩, hcZ⟩ : Subgroup.center L) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hq.2.2.2.1]
    exact hord ▸ orderOf_dvd_natCard _
  rcases h43 L (sectionFourHyp_subgroup hG L) hL.1 h3Z with ⟨p, e, _, he, hpi⟩ | h | h | h | h |
      h | h | h | h
  · exact (hSL (isSLThreePiTheta_of_isoLThreePi hGA hG hL hcL hcC hq.2.2.2.1 he hpi)).elim
  · exact hA6 G L A E c m hconf h
  · exact hA7 G L A E c m hconf (Or.inl h)
  · exact hG2 G L A E c m hconf h
  · exact hU43 G L A E c m hconf (Or.inl h)
  · exact hA7 G L A E c m hconf (Or.inr h)
  · exact hJ3 G L A E c m hconf h
  · exact hU43 G L A E c m hconf (Or.inr h)
  · exact hON G L A E c m hconf h

end Certs

end CFSG.RankThree.PartTwo.Sec4
