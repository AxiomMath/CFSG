module

public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProof
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step148KTypeSigmaThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      ∀ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f → 1 ≤ e' → 3 ∣ f →
        Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') →
        (letI := ker148_normal hY.2; IsLThreeEpsAt ↥(img148 A Y K) p f) →
        letI := ker148_normal hY.2
        Sec4.IsoLThreePi ↥(img148 A Y K) p f

namespace Item148Res4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem mem_range_conj_of_pow_three {X : Type} [Group X] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) (h3f : ¬ 3 ∣ f) (hX : Sec8.IsoLThreeMinusPi X p f) (σ : MulAut X)
    (hσ : σ ^ 3 = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  ·
    have h : UnitaryFieldData p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, GaloisField.card p (2 * f) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    set τ : X ≃* unitaryPSU h 3 := e.trans φ.symm with hτ
    have hβ3 : MulAut.congr τ σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
    have hq2 : 2 < p ^ f := by
      have h2 : 2 ≤ p ^ f := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
      have h2' : p ^ f ≠ 2 := fun h2 => by rw [h2] at hq; norm_num at hq
      omega
    by_cases hD : MulAut.congr τ σ ∈ (psuConj h).range
    · exact (isInnerAut_congr τ σ).mp (isInnerAut_of_mem_psuConj_range h hq hD)
    · exfalso
      obtain ⟨s, hs, -⟩ := unitary_order_three_field_descent hq2 (MulAut.congr τ σ) hβ3 hD
      obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic hp.out (GaloisField p (2 * f))
        (GaloisField.card p (2 * f) (by omega))
      have h3 : 3 ∣ 2 * f := by
        rw [← hcard, ← hs]
        exact orderOf_dvd_natCard s
      exact h3f ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3))
  ·
    obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p f)
    set τ : X ≃* projectiveSL 3 (GaloisField p f) := e.trans φ with hτ
    have hK : Nat.card (GaloisField p f) % 3 = 2 := by
      rw [GaloisField.card p f (by omega)]
      exact hq
    have hβ3 : MulAut.congr τ σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
    by_cases hD : MulAut.congr τ σ ∈ linearAutGroup 3 (GaloisField p f)
    · exact (isInnerAut_congr τ σ).mp (isInnerAut_of_mem_linearAutGroup hK hD)
    · exfalso
      obtain ⟨s, hs, -⟩ := linear_order_three_field_descent le_rfl (MulAut.congr τ σ) hβ3 hD
      obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic hp.out (GaloisField p f)
        (GaloisField.card p f (by omega))
      have h3 : 3 ∣ f := by
        rw [← hcard, ← hs]
        exact orderOf_dvd_natCard s
      exact h3f h3

theorem card_le_three_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (h3 : ∀ x : H, x ^ 3 = 1) : Nat.card H ≤ 3 := by
  have hexp : Monoid.exponent H ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one h3
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

end Item148Res4

open Item148Res4

theorem step148KTypeSigma_of (h3 : Step148KTypeSigmaThree) : Step148KTypeSigma := by
  intro G _ _ A c L hstd Y hY hs hYB B Q e K Le hP hsec heΩ hLeA p f e' hp hf he' hLiso hKeps
  by_cases h3f : 3 ∣ f
  · exact h3 G A c L hstd Y hY hs hYB B Q e K Le hP hsec heΩ hLeA p f e' hp hf he' h3f hLiso hKeps
  have := ker148_normal hY.2
  by_contra hnot
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have he : e ∈ A := (zpowers_mem_omegaA_iff.mp heΩ).1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKM : K ≤ Y ⊔ A := hKY.trans le_sup_left
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hP.2.2.2.2.2.2.1
  have : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hKp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h0 : 3 ^ (f * e') % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by positivity))
    rcases hLiso with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
  have hq0 : p ^ f % 3 ≠ 0 := by
    intro h0
    have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h3p).symm
  have hminus : Sec8.IsoLThreeMinusPi ↥(img148 A Y K) p f := by
    rcases hKeps with ⟨⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · refine Or.inr ⟨?_, ⟨φ⟩⟩
      by_contra h2
      exact hnot (Or.inl ⟨by omega, ⟨φ⟩⟩)
    · refine Or.inl ⟨?_, ⟨φ⟩⟩
      by_contra h1
      exact hnot (Or.inr ⟨by omega, ⟨φ⟩⟩)
  have hinner := mem_range_conj_of_pow_three hf h3f hminus
  have hin : ∀ (a : G) (ha : a ∈ A), ∃ k : ℕ,
      InnerOn148 (img148 A Y K) (alpha148 A Y a ha * alpha148 A Y e he ^ k) := by
    intro a ha
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one]
    exact innerOn148_of_pow_three (img148_le_normalizer hAK (alpha148_mem_img148 ha))
      (alpha148_pow_three hA3 ha) hinner
  have hZ : Subgroup.center ↥(img148 A Y K) = ⊥ :=
    kf148CenterL3 _ hKp (Or.inr ⟨p, f, hp, hp3, hf, hKeps⟩)
  have hAeq : A = Subgroup.zpowers e ⊔ (A ⊓ K) :=
    eq_zpowers_sup_inf_of_innerOn hAF hAY hKY hAK he hZ hsec.le hin
  set ι : ↥(A ⊓ K) →* ↥(img148 A Y K) :=
    ((QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion
      ((inf_le_right : A ⊓ K ≤ K).trans hKM))).codRestrict _
      (fun a => mem_img148_iff.mpr ⟨a, (inf_le_right.trans hKM) a.2, a.2.2, rfl⟩) with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : alpha148 A Y a a.2.1 = alpha148 A Y b b.2.1 := congrArg Subtype.val hab
    exact Subtype.ext (alpha148_injective hA3 a.2.1 b.2.1 h1)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : ∀ x : ↥ι.range, x ^ 3 = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hA3 a a.2.1)
    rw [this, map_one]
    rfl
  have hP3 : IsPGroup 3 ↥ι.range := fun x => ⟨1, by rw [pow_one]; exact hR3 x⟩
  obtain ⟨P, hRP⟩ := hP3.exists_le_sylow
  have hPc : IsCyclic ↥(P : Subgroup ↥(img148 A Y K)) :=
    KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega) hminus P
  set T := ι.range.subgroupOf (P : Subgroup ↥(img148 A Y K)) with hT
  have hTc : IsCyclic ↥T := Subgroup.isCyclic T
  have hT3 : ∀ x : ↥T, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : ↥ι.range => (z : ↥(img148 A Y K)))
      (hR3 ⟨_, Subgroup.mem_subgroupOf.mp x.2⟩)
    simpa using this
  have hcardT : Nat.card ↥T = Nat.card ↥(A ⊓ K) := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv]
    exact Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv.symm
  have hAK3 : Nat.card ↥(A ⊓ K) ≤ 3 := hcardT ▸ card_le_three_of_isCyclic hT3
  have hN : A ⊓ K ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer (Subgroup.zpowers e : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (hAc e he a ha.1) k).eq
  have hdvd := card_sup_dvd_of_le_normalizer (Subgroup.zpowers e) (A ⊓ K) hN
  rw [← hAeq] at hdvd
  have he3 : Nat.card (Subgroup.zpowers e) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 e he))
  have hle := Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdvd
  have h27 : Nat.card A = 27 := hstd.toSec13Data.card_eq
  have : Nat.card (Subgroup.zpowers e) * Nat.card ↥(A ⊓ K) ≤ 3 * 3 :=
    Nat.mul_le_mul he3 hAK3
  omega

end CFSG.RankThree.PartTwo.Sec14
