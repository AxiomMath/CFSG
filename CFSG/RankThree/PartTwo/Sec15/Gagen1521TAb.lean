module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
import CFSG.RankThree.PartTwo.Sec15.Gagen1521TInner
import CFSG.RankThree.PartTwo.Sec18.Item188Abs
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionLifting
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponentsAux
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.ClassicalGroups.PCoreSection
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_P_of_pow_eq_one_of_commute {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {p : ℕ} {P : Subgroup G} (hP : Data1519 A (lB A) L p P)
    {X Q : Subgroup G} (hX : X ∈ scriptY2 A) (hQX : Q ≤ X) (hQp : IsPGroup p Q) (hPQ : P ≤ Q) :
    ∀ x ∈ Q, x ^ p = 1 → (∀ y ∈ P, y * x = x * y) → x ∈ P := by
  have hp : p.Prime := hP.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := hP.2.1
  have hPe : CFSG.Assembly.IsElemAbelian p P := hP.2.2.2.1
  have hPcard : Nat.card P = p ^ 2 := hP.2.2.2.2.1
  have hXN : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf ha hb
  have hQN : Q ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := hQX.trans hXN
  have hQ3 : CFSG.pRank p ↥Q < 3 :=
    lt_of_le_of_lt
      (CFSG.RankThree.PartOne.OddCore37.pRank_le_localRank_of_le_normalizer (q := p) hp
        hX.2 (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X) hQN)
      (h.localRank_lt p hp hp3)
  intro x hxQ hxp hxP
  by_contra hxP'
  have hx1 : x ≠ 1 := by rintro rfl; exact hxP' P.one_mem
  have hxord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hxp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have hdisj : P ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hzx : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hz.2
    have hzord : orderOf z = p := by
      have hdvd : orderOf z ∣ p := by
        have := Subgroup.card_dvd_of_le hzx
        rwa [Nat.card_zpowers, Nat.card_zpowers, hxord] at this
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h1
    have hzeq : Subgroup.zpowers z = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge hzx ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hxord]
    have hxPz : x ∈ P := by
      have hxz : x ∈ Subgroup.zpowers z := by
        rw [hzeq]
        exact Subgroup.mem_zpowers x
      exact Subgroup.zpowers_le.mpr hz.1 hxz
    exact hxP' hxPz
  have hPN : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a x := hxP a ha
    rw [show a * x ^ k * a⁻¹ = x ^ k by
      rw [hc.zpow_right k, mul_assoc, mul_inv_cancel, mul_one]]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hcard : Nat.card (P ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := P) (K := Subgroup.zpowers x) hPN
    rw [hdisj, Subgroup.card_bot, mul_one, hPcard, Nat.card_zpowers, hxord] at h
    rw [h]
    ring
  have hcontr : 3 ≤ CFSG.pRank p ↥Q := by
    have h3 : 3 ≤ CFSG.Open.pRank p Q :=
      CFSG.SectionRank.le_pRank hp.one_lt (sup_le hPQ (Subgroup.zpowers_le.mpr hxQ))
        (CFSG.RankThree.PartTwo.Sec15.isElemAbelian_sup_zpowers hPe hxp hxP) hcard
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥Q,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Q]
  omega

private theorem isMulCommutative_of_sec15 {A : Subgroup G} {c : G} {L : Subgroup G}
    (hK : KS1521SylAut) (h : Sec15R G A c L) (hLs : IsSimpleGroup ↥L)
    {p : ℕ} {P : Subgroup G} (hP : Data1519 A (lB A) L p P)
    {Q : Subgroup G} (hQp : IsPGroup p Q) (hPQ : P ≤ Q)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hΩ : ∀ x ∈ Q, x ^ p = 1 → (∀ y ∈ P, y * x = x * y) → x ∈ P) :
    IsMulCommutative Q := by
  have hp : p.Prime := hP.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := hP.2.1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, hm1, hiso, hchoice⟩ := hP.2.2.1
  have hPmem : P ∈ scriptQPi A (lB A) L (piOf p) := hP.2.2.2.2.2.1
  have hPL : P ≤ L := hPmem.1.2
  have hPp : IsPGroup p P := isPGroup_of_mem_scriptQPi hp hPmem
  have hcA : c ∈ A := h.toSec13Data.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hc3 : c ^ 3 = 1 := hA27.1.2 c hcA
  have h3θ : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    CFSG.RankThree.PartTwo.Sec14.Main148.three_dvd_card_of_types136
      (h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).1
  have h3L : 3 ∣ Nat.card L := h3θ.trans (Subgroup.card_quotient_dvd_card _)
  have hθ : aschbacherSolvableCore 3 ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with hb | ht
    · exact hb
    · exfalso
      have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 := by
        change (aschbacherSolvableCore 3 ↥L).index = 1
        rw [ht, Subgroup.index_top]
      rw [h1] at h3θ
      omega
  have hisoL : Sec4.IsoLThreePi ↥L 2 m := by
    have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
    rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · exact Or.inl ⟨h1, ⟨e.symm.trans φ⟩⟩
    · exact Or.inr ⟨h2, ⟨e.symm.trans φ⟩⟩
  obtain ⟨habs, hinn⟩ := hK ↥L m hm1 hisoL p hchoice hp3
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.toSec13Data.mem_lA.1
  have hcP : c ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC (hPL hq))
  set Q₁ : Subgroup G := Q ⊓ Subgroup.centralizer (P : Set G)
  have hQ1p : IsPGroup p Q₁ := hQp.to_le inf_le_left
  have hcQ1 : c ∈ Subgroup.normalizer (Q₁ : Set G) :=
    CFSG.RankThree.PartTwo.Sec18.Item188Proof.mem_normalizer_inf hcQ
      (CFSG.RankThree.PartTwo.Sec18.Item188Proof.mem_normalizer_centralizer_of_forall
        (S := (P : Set G)) (g := c)
        (fun q hq => (Subgroup.mem_centralizer_iff.mp hcP q hq).symm))
  have hR3 : Nat.card (Subgroup.zpowers c) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc3
  have hRcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Q₁) := by
    obtain ⟨k, hk⟩ := hQ1p.exists_card_eq
    rw [hk]
    rcases (Nat.dvd_prime Nat.prime_three).mp hR3 with h1 | h3
    · rw [h1]
      exact Nat.coprime_one_left _
    · rw [h3]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
  have hfixCP : ∀ y ∈ Subgroup.zpowers c, ∀ x ∈ Q₁, x ^ p = 1 → y * x = x * y := by
    intro y hy x hx hxp
    have hxP : x ∈ P :=
      hΩ x hx.1 hxp (fun q hq => Subgroup.mem_centralizer_iff.mp hx.2 q hq)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute c x from (Subgroup.mem_centralizer_iff.mp hcP x hxP).symm).zpow_left j
  have hcent : Subgroup.zpowers c ≤ Subgroup.centralizer (Q₁ : Set G) :=
    CFSG.AGLEmbedding.coprime_le_centralizer_of_forall_pow_eq_one hp2 hQ1p hRcop
      (Subgroup.zpowers_le.mpr hcQ1) hfixCP
  have hcCQ1 : ∀ x ∈ Q₁, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_zpowers c)) x hx).symm
  have hRB : ⁅Subgroup.zpowers c, P⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr hcP
  have hQcent : Q ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    refine CFSG.RankThree.PartTwo.Sec18.Item188Proof.centralizes_of_thompson_AxB
      (p := p) (P := Q) (R := Subgroup.zpowers c) (B := P) hQp ?_ hPp ?_ ?_ hRB ?_
    · rcases (Nat.dvd_prime Nat.prime_three).mp hR3 with h1 | h3
      · rw [h1]
        exact Nat.coprime_one_left p
      · rw [h3]
        exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    · exact Subgroup.zpowers_le.mpr hcQ
    · exact hPQ.trans Subgroup.le_normalizer
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (show Commute c x from hcCQ1 x hx).zpow_left j
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hQcent hx) c (Subgroup.mem_zpowers c)).symm
  have hQNL : Q ≤ Subgroup.normalizer (L : Set G) :=
    hQc.trans (CFSG.RankThree.PartTwo.Sec14.centralizer_le_normalizer_of_three_dvd
      h.toSec14Std h3L)
  haveI hLperf : Group.IsPerfect ↥L :=
    CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt h.toSec13Data.mem_lA.1
  haveI hLnontriv : Nontrivial ↥L := hLs.toNontrivial
  have hnc : ¬ IsMulCommutative ↥L := Group.IsPerfect.not_isMulCommutative ↥L
  have hpair : ∃ x y : ↥L, x * y ≠ y * x := by
    by_contra hcon
    exact hnc ⟨⟨fun a b => by
      by_contra hab
      exact hcon ⟨a, b, hab⟩⟩⟩
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.center_eq_bot_of_isSimpleGroup hpair
  exact isMulCommutative_of_le_normalizer_of_inner (p := p) hZ habs hinn hQp hQNL hPL hΩ

theorem isMulCommutative_and_mem_of_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (hK : KS1521SylAut) (h : Sec15R G A c L) (hLs : IsSimpleGroup ↥L) {p : ℕ} {P : Subgroup G}
    (hP : Data1519 A (lB A) L p P)
    {X Q : Subgroup G} (hX : X ∈ scriptY2 A) (hQX : Q ≤ X) (hQp : IsPGroup p Q) (hPQ : P ≤ Q)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) :
    IsMulCommutative Q ∧ ∀ x ∈ Q, x ^ p = 1 → x ∈ P := by
  have hΩ := mem_P_of_pow_eq_one_of_commute h hP hX hQX hQp hPQ
  have hQab : IsMulCommutative Q :=
    isMulCommutative_of_sec15 hK h hLs hP hQp hPQ hcQ hΩ
  refine ⟨hQab, fun x hxQ hxp => hΩ x hxQ hxp (fun y hy => ?_)⟩
  haveI : IsMulCommutative Q := hQab
  exact congrArg Subtype.val (mul_comm' (⟨y, hPQ hy⟩ : Q) ⟨x, hxQ⟩)

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
