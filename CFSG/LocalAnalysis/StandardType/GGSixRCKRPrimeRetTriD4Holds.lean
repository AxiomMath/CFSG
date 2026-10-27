module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedFrame
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4Model
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
import CFSG.LieType.CurtisTits.Perfect
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedExc
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4Setup
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTriD4Cover
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTriD4

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Steinberg.TwistedD4 (ng twistedDatum)

theorem rckTriD4Model_holds
    {h : ℕ} (hh : 1 ≤ h) : RCKTriD4Model h := by
  obtain ⟨F, hFld, hFin, σ, ι, hF, hι, hrange, hpos, hneg, -, -⟩ :=
    triD4_model_in_adjD4 hh (Or.inl rfl)
  have hl := CFSG.StandardType.LieKnownR2.TriD4.Bridge.ggLongRoot_twistedDatum_single_zero σ
  have hmem : Pi.single (ng 0) 1 ∈ (twistedDatum σ).roots := by
    obtain ⟨w, γ₀, hγ₀, -, hw⟩ := hl
    have hγ := CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w
    rw [← hw] at hγ
    exact hγ
  exact ⟨F, hFld, hFin, σ, hF, ι, Pi.single (ng 0) 1, hι, hrange, hmem, hl, hpos, hneg⟩

theorem rckRetTriD4E_holds :
    RCKRetTriD4E := by
  intro τ hτ S a haT p hp hp2 hap i h hq _ hshape
  obtain ⟨hs, hfr⟩ :=
    rckTriD4PinnedFrame_exc hτ S haT hp hp2 hap i hq hshape.1 hshape.2.1 hshape.2.2
  have hh : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr fun h0 => by
    have hlt : 1 < S.D.q := S.hqpow.1.one_lt
    rw [hq, h0, pow_zero] at hlt
    exact lt_irrefl 1 hlt
  obtain ⟨SK, hSKq, hSKΦ, hfr1⟩ := exists_retSetup_of_pinnedFrame hh hfr (rckTriD4Model_holds hh)
  exact rckReturnedCover_triD4_of_pinnedFrame S a i hs SK hSKq hSKΦ hfr1 (rckTriD4Model_holds hh)

theorem rckRetTriD4_holds :
    RCKRetTriD4 :=
  rckRetTriD4_of_pair_of_E rckPairTriD4_holds rckRetTriD4E_holds

end CFSG.StandardType.RCKRP

end
