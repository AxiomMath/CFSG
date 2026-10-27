module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5
public import CFSG.Quasithin.Vol2.F134LieSp4Borel
public import CFSG.Quasithin.Vol2.F134LieF4Group
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef
public import CFSG.Walter.J1
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem exists_le_stabilizer_of_ne_top {Q : Subgroup (StatedSp 2 K)}
    (hBQ : borelSubgroup 2 K ≤ Q) (hQ : Q ≠ ⊤) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ Q ≤ stabilizer 2 K (flag 2 K d) := by
  obtain ⟨hQI, -⟩ := borel_overgroups Q hBQ
  obtain ⟨d, hd⟩ : (borelCuts K Q).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hQ (by rw [hQI, h, flagStabilizer_empty])
  obtain ⟨h1, h2⟩ := borelCuts_le Q d hd
  refine ⟨d, by omega, fun g hg => ?_⟩
  rw [hQI] at hg
  exact mem_flagStabilizer.mp hg d hd

theorem exists_le_stabilizer_flag_of_card [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (StatedSp 2 K)} {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : a ≤ 3)
    (hPa : Nat.card P = p ^ a)
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ P ≤ stabilizer 2 K (flag 2 K d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU : CFSG.ABGLocalTools.IsSylowOf 2 (unipotent 2 K) ⊤ :=
    hS ▸ CFSG.Quasithin.F134.LieF4.isSylowOf_of_sylow S le_top
  have hUc : IsPGroup 2 (unipotent 2 K) := hS ▸ S.isPGroup'
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hUc
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (unipotent 2 K)) := by
    rw [hPa, hm]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hH : Nat.card (P ⊔ unipotent 2 K : Subgroup (StatedSp 2 K)) = 2 ^ m * p ^ a := by
    rw [card_sup_eq_of_mul' hcop hPU, hPa, hm, mul_comm]
  have hE2 : ∀ x ∈ SymplecticFour.radical K, x ^ 2 = 1 := by
    rintro _ ⟨C, hC, rfl⟩
    exact SymplecticFour.tau_sq hC
  have hE16 : 16 ≤ Nat.card (SymplecticFour.radical K) := by
    rw [SymplecticFour.card_radical]
    calc 16 ≤ 4 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK 3
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := S5.exists_proper_overgroup
    (CFSG.LieType.BorelTits.holds_statedSp 2 K 2) hU le_sup_right
    (SymplecticFour.radical_le_unipotent.trans le_sup_right) hE2 hE16 hp hp2 hH ha
  rw [normalizer_unipotent] at hNQ
  obtain ⟨d, hd, hQd⟩ := exists_le_stabilizer_of_ne_top hNQ hQ
  exact ⟨d, hd, le_sup_left.trans (hHQ.trans hQd)⟩

end CFSG.Quasithin.H13.NQCore.Psp4
