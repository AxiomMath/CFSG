module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
public import CFSG.Quasithin.Background.E2Two
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

open scoped MatrixGroups
open CFSG.Open CFSG.Quasithin CFSG.SectionRank.EvenCover

namespace CFSG.Quasithin.F146Field


namespace Cover

private theorem charP_two_of_card_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 2 * n) (by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])

theorem isBenderQuot_of_oddCover_psu {n : ℕ} (hn : 2 ≤ n) {Kb Ks : Type} [Group Kb] [Finite Kb]
    [Group Ks] (hperf : Group.IsPerfect Kb) (π : Kb →* Ks) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center Kb) (ho : ∀ x ∈ π.ker, Odd (orderOf x))
    (hpsu : IsPSU 3 2 n Ks) : IsBenderQuot n Kb := by
  obtain ⟨-, F, iF, iFin, hF, ⟨e⟩⟩ := hpsu
  have : CharP F 2 := charP_two_of_card_sq hF
  set SU := CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F with hSU
  set D : Subgroup SU := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf SU with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  set q : SU →* CFSG.Assembly.LowTwoRank.StatedProj SU := QuotientGroup.mk' D with hq
  set ρ : Kb →* CFSG.Assembly.LowTwoRank.StatedProj SU := e.toMonoidHom.comp π with hρdef
  have hρker : ρ.ker = π.ker := ker_comp_equiv e π
  have hρ : Function.Surjective ρ := e.surjective.comp hπ
  have hρc : ρ.ker ≤ Subgroup.center Kb := hρker ▸ hc
  have hodd : Odd (Nat.card ρ.ker) := hρker ▸ odd_card_ker π ho
  obtain ⟨σ, hσ, -⟩ := even_unitary_three_central_odd_extension_splitting (K := F) (f := n) hF hn
    (E := pullback ρ q) (π := pullbackFst ρ q) (pullbackFst_surjective hρ q)
    (pullbackFst_ker_le_center hρc q) (Odd.of_dvd_nat hodd (card_pullbackFst_ker_dvd ρ q))
  set φ : SU →* Kb := (MonoidHom.snd SU Kb).comp ((pullback ρ q).subtype.comp σ) with hφdef
  have hρφ : ρ.comp φ = q := comp_snd_section σ hσ
  have hρφ' : ∀ h, ρ (φ h) = q h := fun h => congrArg (· h) hρφ
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective D
  have hφsurj : Function.Surjective φ := by
    have := hperf
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_forall_mul_center fun x => ?_
    obtain ⟨h, hh⟩ := hqsurj (ρ x)
    refine ⟨φ h, ⟨h, rfl⟩, hρc ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρφ', hh, inv_mul_cancel]
  have hφker : φ.ker ≤ D := fun h hh => by
    have := hρφ' h
    rw [MonoidHom.mem_ker.mp hh, map_one] at this
    exact (QuotientGroup.eq_one_iff h).mp this.symm
  have hDcard : Nat.card D = Nat.gcd 3 (2 ^ n + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3) (by norm_num)).2.2
  have hdvd : Nat.card D ∣ 3 := hDcard ▸ Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp ((Subgroup.card_dvd_of_le hφker).trans hdvd) with
    h1 | h3
  · have hinj : Function.Injective φ :=
      (MonoidHom.ker_eq_bot_iff φ).mp (Subgroup.eq_bot_of_card_eq _ h1)
    exact Or.inr (Or.inr (Or.inl ⟨F, iF, iFin, hF,
      ⟨(MulEquiv.ofBijective φ ⟨hinj, hφsurj⟩).symm⟩⟩))
  · have hk3 := Subgroup.card_dvd_of_le hφker
    rw [h3] at hk3
    have hD3 : Nat.card D = 3 := Nat.dvd_antisymm hdvd hk3
    have hkerD : φ.ker = D := Subgroup.eq_of_le_of_card_ge hφker (by rw [h3, hD3])
    let e1 : Kb ≃* CFSG.Assembly.LowTwoRank.StatedProj SU :=
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hkerD)
    exact Or.inr (Or.inr (Or.inr ⟨F, iF, iFin, hF, ⟨e1⟩⟩))

end Cover

theorem isBenderQuot_of_oddCover {n : ℕ} {Kb Ks : Type} [Group Kb] [Finite Kb] [Group Ks]
    (hperf : Group.IsPerfect Kb) (π : Kb →* Ks) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center Kb) (ho : ∀ x ∈ π.ker, Odd (orderOf x))
    (hB : E2.IsBenderOf n Ks) : IsBenderQuot n Kb := by
  obtain ⟨hn, hpsl | hsz | hpsu⟩ := hB
  · exact isBenderQuot_of_oddCover_psl hn hperf π hπ hc ho hpsl
  · exact isBenderQuot_of_oddCover_sz hperf π hπ hc ho hsz
  · exact Cover.isBenderQuot_of_oddCover_psu hn hperf π hπ hc ho hpsu

end CFSG.Quasithin.F146Field
