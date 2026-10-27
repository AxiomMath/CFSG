module

public import CFSG.LocalAnalysis.UniqueFourCatalog.SporadicSmall
public import CFSG.LocalAnalysis.UniqueFourCatalog.SporadicCo2Th
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeterB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeY
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeCase
public import CFSG.LocalAnalysis.SectionRank.QTK.Spor
public import Certificates.Certificate8152
public import Certificates.Certificate9501
public import Certificates.Certificate9503
public import Certificates.Certificate9507
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeChecks

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog


section Beta

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census

variable {G H : Type} [Group G] [Finite G] [Group H] [Finite H]

theorem mem_uniqueFourBeta_of_localRank (e : G ≃* H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h4 : 4 ≤ localRank p H) : p ∈ uniqueFourBeta G := by
  have h4G : 4 ≤ localRank p G := by
    rw [localRank_eq_of_mulEquiv e hp]
    exact h4
  refine ⟨hp, hp2, ?_, h4G⟩
  obtain ⟨K, hK, hKr⟩ := CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_attained (G := G) p hp
    (by change 0 < localRank p G; omega)
  obtain ⟨E, -, -, hE⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained (G := G) p hp K
  have hpos : 0 < CFSG.Open.pRank p K := by
    change CFSG.Open.pRank p K = localRank p G at hKr
    omega
  exact CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank p hp K hpos

end Beta

section Gamma

open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem not_uniqueFour_of_liftableNormalizerGen (hS : Standing4 G) (h3 : 3 ∈ uniqueFourBeta G)
    (hL : LiftableNormalizerGen G) : ¬ uniqueFourUnique G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup G := hS.simple
  have hc : Subgroup.center G = ⊥ := MonsterThree.center_eq_bot_of_isSimple_nonabelian hS.nonab
  let e0 : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hcore : GLBWeakCore 3 (P : Subgroup G) = ⊤ :=
    weakCore_eq_top_of_normalizerGen hL e0 (by rw [hc]; exact IsPGroup.of_card (n := 0) (by simp)) P
  have hΓ : uniqueFourGamma 3 (P : Subgroup G) = ⊤ :=
    top_le_iff.mp (hcore ▸ CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore 3 _)
  exact not_uniqueFour_of_gamma_eq_top hS h3 P hΓ

end Gamma

section SporadicLarge

set_option linter.unusedSectionVars false

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census CFSG.Blueprint
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.BCox CFSG.SectionRank
open CFSG.SectionRank.Native

variable {G : Type} [Group G] [Finite G]

theorem two_lt_card_of_nonab (hS : Standing4 G) : 2 < Nat.card G := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨a, b, hab⟩ := hS.nonab
  have ha : a ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
  have hb : b ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
  have hne : a ≠ b := fun h => hab (by rw [h])
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ha.symm, hb.symm]), Finset.card_pair hne]
  have := Finset.card_le_univ ({1, a, b} : Finset G)
  rw [h3, Nat.card_eq_fintype_card] at *
  omega

theorem not_uniqueFour_of_B
    (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .B) :
    ¬ uniqueFourUnique G := by
  have : Finite NativeSporadic.B := Finite.of_equiv G e.toEquiv
  have : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv G e.toEquiv
  have hp : 3 ∈ uniqueFourBeta G :=
    mem_uniqueFourBeta_of_localRank e Nat.prime_three (by norm_num)
      Certificates.certificate8152
  have hc : 2 < Nat.card NativeSporadic.B := by
    have h := Nat.card_congr e.toEquiv
    exact (show Nat.card G = Nat.card NativeSporadic.B from h) ▸ two_lt_card_of_nonab hS
  exact not_uniqueFour_of_tcGenDatum hS e hp (tcGenDatum_B_three hc)

theorem not_uniqueFour_of_Fi22
    (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Fi22) : ¬ uniqueFourUnique G := by
  have : Finite NativeSporadic.Fi22 := Finite.of_equiv G e.toEquiv
  have : Finite (NativeSporadic.Carrier .Fi22) := Finite.of_equiv G e.toEquiv
  have hp : 3 ∈ uniqueFourBeta G :=
    mem_uniqueFourBeta_of_localRank e Nat.prime_three (by norm_num) four_le_localRank_three_Fi22
  exact not_uniqueFour_of_tcGenDatum hS e hp
    (tcGenDatum_of_check (spec3 77) (D := R3.Fi22Three.tcSpec) Nat.prime_three
      Certificates.certificate9501.1)

theorem not_uniqueFour_of_Fi23
    (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Fi23) : ¬ uniqueFourUnique G := by
  have : Finite NativeSporadic.Fi23 := Finite.of_equiv G e.toEquiv
  have : Finite (NativeSporadic.Carrier .Fi23) := Finite.of_equiv G e.toEquiv
  have hp : 3 ∈ uniqueFourBeta G :=
    mem_uniqueFourBeta_of_localRank e Nat.prime_three (by norm_num) four_le_localRank_three_Fi23
  exact not_uniqueFour_of_tcGenDatum hS e hp
    (tcGenDatum_of_check (spec3 253) (D := R3.Fi23Three.tcSpec) Nat.prime_three
      Certificates.certificate9507.1)

theorem not_uniqueFour_of_Co1
    (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .Co1) : ¬ uniqueFourUnique G := by
  have : Finite NativeSporadic.Co1 := Finite.of_equiv G e.toEquiv
  have : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv G e.toEquiv
  have hp : 3 ∈ uniqueFourBeta G :=
    mem_uniqueFourBeta_of_localRank e Nat.prime_three (by norm_num) four_le_localRank_three_Co1
  exact not_uniqueFour_of_tcGenDatum hS e hp
    (tcGenDatum_of_check (spec2 24) (D := R3.Co1Three.tcSpec) Nat.prime_three
      Certificates.certificate9503.1)

theorem not_uniqueFour_of_M (hS : Standing4 G) (e : G ≃* NativeSporadic.Carrier .M) :
    ¬ uniqueFourUnique G := by
  have : IsSimpleGroup G := hS.simple
  have hp : 3 ∈ uniqueFourBeta G :=
    mem_uniqueFourBeta_of_localRank (MulEquiv.refl G) Nat.prime_three (by norm_num)
      (CFSG.SectionRank.QTK.four_le_localRank_three_of_mulEquiv_nativeM e hS.nonab)
  have hnt : Nontrivial (NativeSporadic.Carrier .M) := e.toEquiv.symm.nontrivial
  exact not_uniqueFour_of_liftableNormalizerGen hS hp
    (LiftableNormalizerGen.of_mulEquiv e.symm (MonsterThree.liftableNormalizerGen_M hnt))

theorem not_pow_four_dvd_Fi24 :
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ 1255205709190661721292800 := by
  refine not_pow_four_dvd_of_primeFactors (N := 1255205709190661721292800) (by norm_num)
    {2, 3, 5, 7, 11, 13, 17, 23, 29} (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem not_uniqueFour_of_Fi24
    (hS : Standing4 G)
    (e : G ≃* NativeSporadic.Carrier .Fi24Prime) : ¬ uniqueFourUnique G := by
  have hcard : Nat.card (NativeSporadic.Carrier .Fi24Prime) = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have h4 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv, hcard]
    exact not_pow_four_dvd_Fi24
  have h3 : 3 ∈ uniqueFourBeta G :=
    CFSG.Yardstones.Mf4cdcdf2e013.three_mem_uniqueFourBeta_of_card hS h4
  have : Finite (NativeSporadic.Carrier .Fi24Prime) := Finite.of_equiv G e.toEquiv
  have : Finite NativeSporadic.Fi24prime := Finite.of_equiv G e.toEquiv
  exact not_uniqueFour_of_tcGenDatum hS e h3
    (tcGenDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
      (D := R3.Fi24Three.tcSpec) Nat.prime_three R3.Fi24Three.tcCheck_Fi24)

end SporadicLarge

section Dispatch

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem not_uniqueFour_of_sporadic
    (hS : Standing4 G) (s : TauCeti.SporadicName)
    (e : G ≃* CFSG.Blueprint.NativeSporadic.Carrier s) : ¬ uniqueFourUnique G := by
  cases s with
  | M11 => exact (Standing4.false_of_M11 hS e).elim
  | M12 => exact (Standing4.false_of_M12 hS e).elim
  | M22 => exact (Standing4.false_of_M22 hS e).elim
  | M23 => exact (Standing4.false_of_M23 hS e).elim
  | M24 => exact (Standing4.false_of_M24 hS e).elim
  | J1 => exact (Standing4.false_of_J1 hS e).elim
  | J2 => exact (Standing4.false_of_J2 hS e).elim
  | J3 => exact (Standing4.false_of_J3 hS e).elim
  | J4 => exact (Standing4.false_of_J4 hS e).elim
  | HS => exact (Standing4.false_of_HS hS e).elim
  | He => exact (Standing4.false_of_He hS e).elim
  | Ru => exact (Standing4.false_of_Ru hS e).elim
  | McL => exact (Standing4.false_of_McL hS e).elim
  | Ly => exact (Standing4.false_of_Ly hS e).elim
  | Suz => exact (Standing4.false_of_Suz hS e).elim
  | ONan => exact (Standing4.false_of_ON hS e).elim
  | Co3 => exact (Standing4.false_of_Co3 hS e).elim
  | HN => exact (Standing4.false_of_HN hS e).elim
  | Co1 => exact not_uniqueFour_of_Co1 hS e
  | Co2 => exact not_uniqueFour_of_Co2 hS e
  | Fi22 => exact not_uniqueFour_of_Fi22 hS e
  | Fi23 => exact not_uniqueFour_of_Fi23 hS e
  | Fi24Prime => exact not_uniqueFour_of_Fi24 hS e
  | Th => exact not_uniqueFour_of_Th hS e
  | B => exact not_uniqueFour_of_B hS e
  | M => exact not_uniqueFour_of_M hS e

end Dispatch

end CFSG.LocalAnalysis.UniqueFourCatalog
