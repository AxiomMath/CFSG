module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Glue
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGE6OutdiagPpdToral
import CFSG.LocalAnalysis.StandardType.GGE6OutdiagPpdKernel
import CFSG.LocalAnalysis.StandardType.GGE6OutdiagPpdComp
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6ModelUntw
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
import CFSG.CGT.Timmesfeld75.Forms
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.GF2n.Stroth80.Anisotropic
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec36
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.E6OutdiagPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem ggE6NontoralFixPpdInput_holds :
    GGE6NontoralFixPpdInput := by
  intro f hf h3 α hα hα3 hnt
  classical
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hα' : α ∈ (TableBExc.E6Three.hatAut Tag.E6 (GaloisField 2 f)).range := by
    rw [NoOffE6Three.hatAut_range_eq_sup]
    exact hα
  obtain ⟨x, rfl⟩ := hα'
  have hinj : Function.Injective (TableBExc.E6Three.hatAut Tag.E6 (GaloisField 2 f)) :=
    NoOffE6Three.hatAut_injective
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hα3, map_one])
  have hx1 : (x : ModGL Tag.E6 (GaloisField 2 f)) ≠ 1 := by
    intro h1
    apply hnt
    have hx : x = 1 := Subtype.ext h1
    refine ⟨1, fun β hβ => ?_⟩
    rw [hx, map_one, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hβ
    rw [hβ, mul_one, mul_inv_cancel]
    exact one_mem _
  have h3K : ¬ 3 ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have h5K : ¬ 5 ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    omega
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, -, hιinj, hrange, hda, hι, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T158.exists_langSetup_of_hatE6_conj_g0 Nat.prime_three h3K
      Nat.prime_five h5K (Or.inl le_rfl) hmon x.2 (by rw [← Subgroup.coe_pow, hx3]; rfl) hx1
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hw : w ∉ kernelReflectionGroup a := fun hw =>
    hnt (ggInndiagToral_of_twist_mem_kernelReflectionGroup S.D hFr hΦ hn x hda hw)
  haveI : CharP (AlgebraicClosure (GaloisField 2 f)) 2 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 2 f) _).injective 2
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have hq : S.D.q = 2 ^ f := hSq.trans hK
  have h3q : 3 ∣ S.D.q - 1 := by rw [hq]; exact h3
  have hcls : ∀ m, (kernelRoots (rootCharHom a)).ncard = m → m ≠ 0 →
      Nonempty (KernelComponent (rootCharHom a)) := by
    intro m hm hm0
    obtain ⟨γ, hγ⟩ := Set.nonempty_of_ncard_ne_zero (hm ▸ hm0)
    exact ⟨⟦⟨γ, hγ⟩⟧⟩
  have hex : ∃ r, (∃ e ∈ ggOutdiagExpsE6, IsTwoPowPpd f e r) ∧ ∃ i : KernelComponent (rootCharHom a),
      ∃ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, orderOf z = r := by
    rcases kernel_cases_of_twist_not_mem S hFr' hΦ h3q hn hT hap hw with ⟨h18, hall⟩ | ⟨h24, hall⟩
    · obtain ⟨i⟩ := hcls 18 h18 (by norm_num)
      obtain ⟨r, hr, -, hord⟩ :=
        CFSG.RankThree.GF2n.Stroth80.exists_prime_orderOf_two_eq (e := 9 * f) (by omega) (by omega)
      exact ⟨r, ⟨9, by simp [ggOutdiagExpsE6], hr, hord⟩, i,
        exists_orderOf_ppd_of_orbit_three S hFr' hΦ hq h3q hn hT hap h18 i (hall i) ⟨hr, hord⟩⟩
    · obtain ⟨i⟩ := hcls 24 h24 (by norm_num)
      obtain ⟨r, hr, -, hord⟩ :=
        CFSG.RankThree.GF2n.Stroth80.exists_prime_orderOf_two_eq (e := 12 * f) (by omega) (by omega)
      exact ⟨r, ⟨12, by simp [ggOutdiagExpsE6], hr, hord⟩, i,
        exists_orderOf_ppd_of_triality S hFr' hΦ hq h3q hT hap h24 i (hall i) ⟨hr, hord⟩⟩
  obtain ⟨r, hr, i, z', hz', hz'r⟩ := hex
  obtain ⟨hzΓ, hzC⟩ := (langSubnormal_of_mem_torus S hT i).1 hz'
  rw [← hrange] at hzΓ
  obtain ⟨z, rfl⟩ := hzΓ
  refine ⟨r, hr, z, by rw [← orderOf_injective ι hιinj z]; exact hz'r, hιinj ?_⟩
  have hcomm : rootDiagUnit Tag.E6 a * ι z = ι z * rootDiagUnit Tag.E6 a :=
    Subgroup.mem_centralizer_iff.1 hzC _ (Set.mem_singleton _)
  rw [hda, hι] at hcomm
  rw [hι, hι, TableBExc.E6Three.coe_hatAut_apply, map_mul, map_mul, map_inv]
  set B := baseChangeGL (algebraMap (GaloisField 2 f) (AlgebraicClosure (GaloisField 2 f)))
  calc S.D.g0⁻¹ * (B (x : ModGL Tag.E6 (GaloisField 2 f)) * B (z : ModGL Tag.E6 (GaloisField 2 f)) *
        (B (x : ModGL Tag.E6 (GaloisField 2 f)))⁻¹) * S.D.g0
      = (S.D.g0⁻¹ * B (x : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0) *
          (S.D.g0⁻¹ * B (z : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0) *
          (S.D.g0⁻¹ * B (x : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0)⁻¹ := by group
    _ = (S.D.g0⁻¹ * B (z : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0) *
          (S.D.g0⁻¹ * B (x : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0) *
          (S.D.g0⁻¹ * B (x : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0)⁻¹ := by rw [hcomm]
    _ = S.D.g0⁻¹ * B (z : ModGL Tag.E6 (GaloisField 2 f)) * S.D.g0 := by group

end CFSG.StandardType.E6OutdiagPpd

end
