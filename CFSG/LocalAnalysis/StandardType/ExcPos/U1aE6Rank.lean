module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.Walter.Bender1970.S2.Components
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.Walter.Bender1970.S2.TwoSubgroup
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.Blueprint

theorem excU1a_e6_twoLocalRank
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E6 n f).K →* X} {G₀ H : Subgroup X}
    (hrange : ψ.range = G₀) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    (hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 n 2 f) (hfe : Even f) (hGH : G₀ ≤ H) :
    5 ≤ CFSG.Assembly.LargeEvenTwoLocalRank 3 ↥H := by
  classical
  let K := GaloisField 2 f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : ChevalleyExceptionalModel
      (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 2 f :=
    hLie.chevalleyExceptionalModel (by decide)
  have hf : 1 ≤ f := hmodel.1.2.1
  have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hKcard]
    have h2f : 2 ∣ f := even_iff_two_dvd.mp hfe
    simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 2) (k := f) h2f
  have hperfU : commutator (ggU .E6 n f).K = ⊤ := by
    haveI : Group.IsPerfect (ggU .E6 n f).K :=
      CFSG.LieType.CurtisTits.isPerfect_e6 K
    exact Group.IsPerfect.commutator_eq_top
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hperfG₀ : commutator ↥G₀ = ⊤ := by
    have h := map_commutator_eq (ggU .E6 n f).K ψ.rangeRestrict
    rw [hperfU, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj, ← commutator_def] at h
    exact hrange ▸ h.symm
  have hperfX : commutator (G₀.subgroupOf H) = ⊤ := by
    haveI : Group.IsPerfect ↥G₀ := Group.isPerfect_def.mpr hperfG₀
    haveI : Group.IsPerfect ↥(G₀.subgroupOf H) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hGH).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hGH).symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  let eU : (ggU .E6 n f).K ⧸ Subgroup.center (ggU .E6 n f).K ≃*
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K)
        (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K))
  have hkerR : ψ.rangeRestrict.ker ≤ Subgroup.center (ggU .E6 n f).K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) ψ.rangeRestrict hsurj hkerR
  let e2 : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* ↥G₀ ⧸ Subgroup.center ↥G₀ :=
    QuotientGroup.congr (Subgroup.center ↥ψ.range) (Subgroup.center ↥G₀)
      (MulEquiv.subgroupCongr hrange) (Subgroup.map_center_eq (MulEquiv.subgroupCongr hrange))
  let θ : (G₀.subgroupOf H) ⧸ Subgroup.center (G₀.subgroupOf H) ≃*
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K) :=
    (CFSG.Walter.subgroupOfQuotientCenterEquiv hGH).trans
      (e2.symm.trans (e1.symm.trans eU))
  exact le_twoLocalRank_of_torusLift (G := ↥H) Nat.prime_three hperfX θ
    (CFSG.StandardType.TableBExc.ggTorusLift_adjoint_E6_three (K := K) h3)

end CFSG.StandardType.LieKnownR2.ExcPos
