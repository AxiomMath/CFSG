module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
import CFSG.LieType.SeitzGeneration.ExcPlaneF4Rest
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LieType.Simplicity.Finiteness
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBasic
import CFSG.Quasithin.Background.A3Structure36BPrime
import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
import CFSG.RankThree.PartOne.KE.A1SL2
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.A2Shape
import CFSG.RankThree.PartOne.KE.SigmaUntwisted
import CFSG.RankThree.PartOne.KLR.Master
import CFSG.RankThree.PartOne.KLR.SectorAssembly
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType.ExcFieldAutCentRankF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

section Transfer


private theorem card_fixSubfield_two {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (σ : K ≃+* K) :
    orderOf σ ∣ n ∧ Nat.card (fixSubfield σ) = 2 ^ (n / orderOf σ) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  have hSeq : fixSubfield σ = S := by
    ext c
    have hc : c ∈ S ↔ ∀ τ ∈ Subgroup.zpowers σ, τ c = c := by
      rw [← SetLike.mem_coe, hS]
      rfl
    rw [hc, mem_fixSubfield]
    constructor
    · intro h τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) c := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact h
      exact hle hτ
    · intro h
      exact h σ (Subgroup.mem_zpowers σ)
  rw [hSeq]
  exact hcard

private theorem dvd_pow_sub_one_iff_of_cast_eq {p q q₀ d : ℕ} (hq : 0 < q) (hq₀ : 0 < q₀)
    (h : (q : ZMod p) = (q₀ : ZMod p)) : p ∣ q ^ d - 1 ↔ p ∣ q₀ ^ d - 1 := by
  have hq1 : 1 ≤ q ^ d := Nat.one_le_pow d q hq
  have hq01 : 1 ≤ q₀ ^ d := Nat.one_le_pow d q₀ hq₀
  have key : ((q ^ d - 1 : ℕ) : ZMod p) = ((q₀ ^ d - 1 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hq1, Nat.cast_sub hq01, Nat.cast_pow, Nat.cast_pow, h]
  constructor
  · intro hh
    rw [← ZMod.natCast_eq_zero_iff (q ^ d - 1) p, key,
      ZMod.natCast_eq_zero_iff (q₀ ^ d - 1) p] at hh
    exact hh
  · intro hh
    rw [← ZMod.natCast_eq_zero_iff (q₀ ^ d - 1) p, ← key,
      ZMod.natCast_eq_zero_iff (q ^ d - 1) p] at hh
    exact hh

private theorem dvd_card_adjointGroup_fixSubfield_of_dvd {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : ¬ p ∣ Nat.card K)
    (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) (σ : K ≃+* K)
    (hcast : (Nat.card K : ZMod p) = (Nat.card (fixSubfield σ) : ZMod p))
    (hdvd : p ∣ Nat.card (adjointGroup .F4 K)) :
    p ∣ Nat.card (adjointGroup .F4 ↥(fixSubfield σ)) := by
  haveI : Finite ↥(fixSubfield σ) :=
    Finite.of_injective (Subtype.val : ↥(fixSubfield σ) → K) Subtype.val_injective
  rw [CFSG.RankThree.PartOne.KE.exactF4FiniteOrder K] at hdvd
  have hD : p ∣ Nat.card K ^ 6 - 1 ∨ p ∣ Nat.card K ^ 8 - 1 ∨
      p ∣ Nat.card K ^ 12 - 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd (hp.dvd_of_dvd_pow h) hq
          · exact absurd h hnd
        · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rw [CFSG.RankThree.PartOne.KE.exactF4FiniteOrder ↥(fixSubfield σ)]
  rcases hD with h6 | h8 | h12
  · have h6' : p ∣ Nat.card (fixSubfield σ) ^ 6 - 1 :=
      (dvd_pow_sub_one_iff_of_cast_eq Nat.card_pos Nat.card_pos hcast).1 h6
    exact ((h6'.mul_left _).mul_right _).mul_right _
  · have h8' : p ∣ Nat.card (fixSubfield σ) ^ 8 - 1 :=
      (dvd_pow_sub_one_iff_of_cast_eq Nat.card_pos Nat.card_pos hcast).1 h8
    exact (h8'.mul_left _).mul_right _
  · have h12' : p ∣ Nat.card (fixSubfield σ) ^ 12 - 1 :=
      (dvd_pow_sub_one_iff_of_cast_eq Nat.card_pos Nat.card_pos hcast).1 h12
    exact h12'.mul_left _

theorem exists_elemAbelian_fixSubfield {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    {B : Subgroup (adjointGroup .F4 K)} (hB : IsElemAbelian p B) :
    ∃ E : Subgroup (adjointGroup .F4 (fixSubfield σ)), IsElemAbelian p E ∧
      Nat.card B ≤ p * Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite ↥(fixSubfield σ) :=
    Finite.of_injective (Subtype.val : ↥(fixSubfield σ) → K) Subtype.val_injective
  haveI : CharP ↥(fixSubfield σ) 2 := Subfield.charP (fixSubfield σ) 2
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcardK : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [Nat.card_zmod] at h
    exact h
  have hf : 1 ≤ Module.finrank (ZMod 2) K := by
    by_contra h
    have h0 : Module.finrank (ZMod 2) K = 0 := by omega
    rw [h0, pow_zero] at hcardK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨hdvd, hfixcard⟩ := card_fixSubfield_two hf hcardK σ
  rw [hord] at hdvd hfixcard
  have hq_eq : Nat.card K = Nat.card (fixSubfield σ) ^ p := by
    rw [hfixcard, hcardK, ← pow_mul, Nat.div_mul_cancel hdvd]
  have hcast : ((Nat.card K : ℕ) : ZMod p) = ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) := by
    rw [hq_eq, Nat.cast_pow]
    exact ZMod.pow_card _
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  ·
    have hd₀ : p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 :=
      (dvd_pow_sub_one_iff_of_cast_eq Nat.card_pos Nat.card_pos hcast).1 hd
    have hB4 : Nat.card B ≤ p ^ 4 := card_le_pow_four hp hp2 hd hB
    obtain ⟨E, hE, hE3⟩ :=
      exists_elemAbelian_pow_three_le (K := ↥(fixSubfield σ)) hp hp2 hd₀
    refine ⟨E, hE, ?_⟩
    calc Nat.card B ≤ p ^ 4 := hB4
      _ = p * p ^ 3 := by ring
      _ ≤ p * Nat.card E := Nat.mul_le_mul_left p hE3
  ·
    have hqnd : ¬ p ∣ Nat.card K := by
      intro hpK
      rw [hcardK] at hpK
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hpK
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    have hB2 : Nat.card B ≤ p ^ 2 :=
      CFSG.LieType.SeitzGeneration.rankLE2_adjointGroup_F4 K hp hp2 hqnd hd B hB
    by_cases hpdvd : p ∣ Nat.card (adjointGroup .F4 ↥(fixSubfield σ))
    ·
      haveI : Finite (adjointGroup .F4 ↥(fixSubfield σ)) := generated_group_finite .F4 _
      obtain ⟨x, hx⟩ :=
        exists_prime_orderOf_dvd_card' (G := adjointGroup .F4 ↥(fixSubfield σ)) p hpdvd
      refine ⟨Subgroup.zpowers x,
        CFSG.Open.isElemAbelian_zpowers (by rw [← hx]; exact pow_orderOf_eq_one x), ?_⟩
      have hcardE : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
      calc Nat.card B ≤ p ^ 2 := hB2
        _ = p * Nat.card (Subgroup.zpowers x) := by rw [hcardE, pow_two]
    ·
      have hnotdvd : ¬ p ∣ Nat.card (adjointGroup .F4 K) := fun hdvd =>
        hpdvd (dvd_card_adjointGroup_fixSubfield_of_dvd hp hp2 hqnd hd σ hcast hdvd)
      haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
      have hBp : IsPGroup p B := CFSG.Open.IsElemAbelian.isPGroup hB
      obtain ⟨m, hm⟩ := hBp.exists_card_eq
      have hm0 : m = 0 := by
        by_contra h
        apply hnotdvd
        have hpm : p ∣ Nat.card B := by rw [hm]; exact dvd_pow_self p h
        exact hpm.trans (Subgroup.card_subgroup_dvd_card B)
      have hBcard : Nat.card B = 1 := by rw [hm, hm0, pow_zero]
      refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
      rw [hBcard, Subgroup.card_bot, mul_one]
      exact Nat.one_le_iff_ne_zero.2 hp.ne_zero

end Transfer

end CFSG.StandardType.ExcFieldAutCentRankF4
