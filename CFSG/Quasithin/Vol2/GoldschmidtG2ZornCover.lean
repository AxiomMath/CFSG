module

public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.EmptyFaithful.SBd8SmallU33
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddCover
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.Quasithin.H13.G2Zorn

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.CentralExt

theorem ker_le_center_of_surjective {Q S : Type} [Group Q] [Group S] [Nontrivial S]
    (hQ : CFSG.IsQuasisimple Q) {φ : Q →* S} (hφ : Function.Surjective φ) :
    φ.ker ≤ Subgroup.center Q := by
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  obtain ⟨k, rfl⟩ := hφ s
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hQ ⟨k, hs⟩

section Two

theorem lieModel_g2_of_cover {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Odd (Nat.card (Subgroup.center Q))) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (φ : Q →* ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (hφ : Function.Surjective φ) : LieModel Q .G2 0 2 n := by
  have : CharP K 2 := B42G2Id.charP_two_of_card hK
  obtain ⟨eG⟩ := B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient hK hn
  let eA : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  have h3 : 3 ≤ Nat.card K := hK ▸ B42G2Id.three_le_two_pow hn
  have hAperf : Group.IsPerfect ↥(adjointGroup .G2 K) := isPerfect_g2_of_three_le_card K h3
  have : Nontrivial ↥(adjointGroup .G2 K) := nontrivial_g2 K
  let e : ↥(quasithinG2 K) ≃* ↥(adjointGroup .G2 K) := eG.trans eA
  have hGperf : Group.IsPerfect ↥(quasithinG2 K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hD : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K := Subgroup.commutator_eq_self
  let eS : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥(adjointGroup .G2 K) :=
    (MulEquiv.subgroupCongr hD).trans e
  let π : Q →* ↥(adjointGroup .G2 K) := eS.toMonoidHom.comp φ
  have hπ : Function.Surjective π := eS.surjective.comp hφ
  have hker : π.ker ≤ Subgroup.center Q := ker_le_center_of_surjective hQ hπ
  have hsec : ∃ σ : ↥(adjointGroup .G2 K) →* Q, ∀ g, π (σ g) = g := by
    by_cases h2 : n = 2
    · subst h2
      exact G2Four.g2_four_exists_section_of_odd (by rw [hK]; norm_num) Q π hπ hker
        (Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hker))
    · have h8 : 8 ≤ Nat.card K := by
        rw [hK]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact AdjointClosed.g2_exists_section_of_central (by omega) hπ hker
  obtain ⟨σ, hσ⟩ := hsec
  have : Group.IsPerfect Q := hQ.1
  have hinj : Function.Injective π :=
    (MonoidHom.ker_eq_bot_iff π).mp (SUOdd.ker_eq_bot_of_section hker hσ)
  let eQ : Q ≃* ↥(adjointGroup .G2 K) := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  refine Or.inr (Or.inl ⟨rfl, by simp [chevalleyExceptionalTags], ?_⟩)
  exact ⟨⟨Nat.prime_two, by omega, rfl, B42G2Id.three_le_two_pow hn⟩, K, inferInstance,
    inferInstance, hK, ⟨eQ.trans eA.symm⟩⟩

end Two

section One

theorem lieModel_psu_of_cover {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (φ : Q →* ↥⁅quasithinG2 K, quasithinG2 K⁆) (hφ : Function.Surjective φ) :
    LieModel Q .PSU 3 3 1 := by
  have hX : IsPSU 3 3 1 ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
    SBd8.trioIsPSU33 ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hcomm, ⟨eH⟩⟩ := GriessClassical.psu_odd_row hX (by decide)
  have hSperf : Group.IsPerfect ↥⁅quasithinG2 K, quasithinG2 K⁆ := ⟨hcomm⟩
  have : Finite ↥⁅quasithinG2 K, quasithinG2 K⁆ := Finite.of_surjective φ hφ
  have : Nontrivial ↥⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [← Finite.one_lt_card_iff_nontrivial,
      Vol2.Ch10.SecA.C10P01.card_g2Two_commutator (by simpa using hK)]
    norm_num
  have hker : φ.ker ≤ Subgroup.center Q := ker_le_center_of_surjective hQ hφ
  have hdvd := CFSG.RankThree.PartOne.card_ker_dvd_card_hopfMultiplier hSperf hQ.1 φ hφ hker
  have hg : Multiplier.genericOrders .PSU 3 3 1 = (1, 1) := by
    simp [Multiplier.genericOrders]
  have he : Multiplier.exceptionalOrders .PSU 3 3 1 = (1, 1) :=
    GriessClassical.exceptionalOrders_PSU_odd (by decide)
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      ↥⁅quasithinG2 K, quasithinG2 K⁆) = 1 := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
      Nat.card_congr eH.toEquiv]
    simp [Multiplier.generic, Multiplier.exceptional, hg, he]
  have hbot : φ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp (hcard ▸ hdvd))
  let eQ : Q ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
    MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hbot, hφ⟩
  exact Or.inl ⟨by simp [classicalTags], IsPSU.of_mulEquiv eQ.symm hX⟩

end One

end CFSG.Quasithin.H13.G2Zorn
