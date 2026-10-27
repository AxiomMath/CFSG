module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Model
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Cover
import CFSG.HardMathSupport.Dickson.I271.SporGen
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoComp
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StepGen
import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Exceptional
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

section Certificates


theorem prime_eq_three_of_twistedE6_compConfig
    {X : Type} [Group X] [Finite X] (n : ℕ)
    (psi : (ggU .twistedE6 n 1).K →* X)
    (p : ℕ) (G0 A B1 D J L K : Subgroup X) (e : X)
    (hcfg : RCKRP.RCKCompConfig .twistedE6 n 1 psi p G0 A B1 D J L K e) : p = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hG0, hOddCent, hp, hp2, hA, hB1A, hDB1, hDcard, hAnormG0, hMarkG,
    hB1normJ, hB1cap, hB1card, hApow, hAcap, hAcapBot, hB1normL, hMarkL, hJcompD,
    hOddCenJ, hLG0, hExists, hNotCent, hCompL, hNoA6, heD, hene, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨⟨hAdm, hrankU⟩, ⟨hrange, hker⟩, hperfG0, hLM⟩ := hG0
  have hn0 : n = 0 := by
    simpa [StatedLieAdmissible] using hAdm.2.2
  subst n
  by_cases hp3 : p = 3
  · exact hp3
  · exfalso
    have hpgt2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hpgt3 : 3 < p :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hpgt2) (Ne.symm hp3)
    have hpne4 : p ≠ 4 := by
      intro h4
      rw [h4] at hp
      norm_num at hp
    have hpgt4 : 4 < p :=
      lt_of_le_of_ne (Nat.succ_le_of_lt hpgt3) (Ne.symm hpne4)
    have hp5 : 5 ≤ p := by omega
    have hrf : ¬ p ∣ 1 := by
      intro h
      have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h
      omega
    let σ : GaloisField 2 2 ≃+* GaloisField 2 2 :=
      iterateFrobeniusEquiv (GaloisField 2 2) 2 1
    have hσ : ∀ c, σ c = c ^ (2 ^ 1) :=
      fun c => iterateFrobeniusEquiv_def _ 2 1 c
    have hσθ : σ.toRingHom = frobQ 2 1 :=
      RingHom.ext fun c => by
        change σ c = frobQ 2 1 c
        rw [hσ, frobQ_apply]
    let C0 := ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1))
    have hcentC0 : Subgroup.center C0 = ⊥ := by
      change Subgroup.center
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1)) = ⊥
      rw [← hσθ]
      exact center_graphFixedRootGroup_eq_bot (σ := σ.toRingHom) σ.surjective
    let U := (ggU .twistedE6 0 1).K
    obtain ⟨π, hπsurj, hπker, hπodd, hπval⟩ :=
      LayerSixE.exists_model_twistedE6 (f := 1) (by norm_num)
    let πU : U →* C0 := by
      change twistedE6Group 2 1 →* C0
      exact π
    have hπUsurj : Function.Surjective πU := by
      change Function.Surjective π
      exact hπsurj
    have hπUker : πU.ker ≤ Subgroup.center U := by
      change π.ker ≤ Subgroup.center (twistedE6Group 2 1)
      exact hπker.le
    haveI hUperf : Group.IsPerfect U := by
      change Group.IsPerfect (twistedE6Group 2 1)
      exact Group.isPerfect_def.2
        (MpStdTwE6.commutator_twistedE6Group (f := 1) (by norm_num))
    let ψG : U →* ↥G0 := psi.codRestrict G0 (fun u => by
      rw [← hrange]
      exact ⟨u, rfl⟩)
    have hψGsurj : Function.Surjective ψG := by
      intro g
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact g.2)
      exact ⟨u, Subtype.ext hu⟩
    have hψGker : ψG.ker ≤ Subgroup.center U := by
      intro u hu
      have hu' : psi u = 1 := by
        simpa [ψG] using congrArg Subtype.val hu
      exact hker hu'
    let eψ : (U ⧸ Subgroup.center U) ≃*
        (↥G0 ⧸ Subgroup.center ↥G0) :=
      quotCenterEquivOfCentral ψG hψGsurj hψGker
    let eπ : (U ⧸ Subgroup.center U) ≃*
        (C0 ⧸ Subgroup.center C0) :=
      quotCenterEquivOfCentral πU hπUsurj hπUker
    let eC0 : (C0 ⧸ Subgroup.center C0) ≃* C0 :=
      (QuotientGroup.quotientMulEquivOfEq hcentC0).trans QuotientGroup.quotientBot
    let eC : (↥G0 ⧸ Subgroup.center ↥G0) ≃* C0 :=
      eψ.symm.trans (eπ.trans eC0)
    have hB1N : B1 ≤ Subgroup.normalizer (G0 : Set X) := hB1A.trans hAnormG0
    let incl : ↥B1 →* ↥(Subgroup.normalizer (G0 : Set X)) :=
      Subgroup.inclusion hB1N
    let φHom : ↥B1 →* MulAut ↥G0 :=
      (G0.normalizerMonoidHom).comp incl
    have hφker : ∀ b : ↥B1, φHom b = 1 → b = 1 := by
      intro b hb
      have hbC : (b : X) ∈ Subgroup.centralizer (G0 : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have hfix : (φHom b) ⟨g, hg⟩ = ⟨g, hg⟩ := by
          rw [hb, MulAut.one_apply]
        have hconj := congrArg Subtype.val hfix
        have hconj' : (b : X) * g * (b : X)⁻¹ = g := by
          simpa [φHom, incl, Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj
        show g * (b : X) = (b : X) * g
        calc
          g * (b : X) = ((b : X) * g * (b : X)⁻¹) * (b : X) := by rw [hconj']
          _ = (b : X) * g := by group
      have hmem : (b : X) ∈ A ⊓ Subgroup.centralizer (G0 : Set X) :=
        Subgroup.mem_inf.mpr ⟨hB1A b.2, hbC⟩
      have hbot : (b : X) ∈ (⊥ : Subgroup X) := by
        rw [← hAcapBot]
        exact hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    haveI hG0perf : Group.IsPerfect ↥G0 := Group.isPerfect_def.2 hperfG0
    have hφinj : Function.Injective φHom := by
      rw [injective_iff_map_eq_one]
      exact hφker
    have hquotInj : Function.Injective fun b : ↥B1 =>
        (centerQuotientHom ↥G0) (φHom b) :=
      (centerQuotientHom_injective ↥G0).comp hφinj
    let αHom : ↥B1 →* MulAut C0 :=
      (MulAut.congr eC).toMonoidHom.comp ((centerQuotientHom ↥G0).comp φHom)
    have hαHom_pow (b : ↥B1) : αHom b ^ p = 1 := by
      have hbpowX : (b : X) ^ p = 1 := hA.2 b (hB1A b.2)
      have hbpow : b ^ p = 1 := Subtype.ext (by simpa using hbpowX)
      have hφpow : φHom b ^ p = 1 := by
        rw [← map_pow, hbpow, map_one]
      have hqpow : ((centerQuotientHom ↥G0) (φHom b)) ^ p = 1 := by
        rw [← map_pow, hφpow, map_one]
      calc
        αHom b ^ p = (MulAut.congr eC)
            (((centerQuotientHom ↥G0) (φHom b)) ^ p) := by
          simp [αHom, map_pow]
        _ = 1 := by rw [hqpow, map_one]
    have hαinj : Function.Injective αHom := by
      intro b₁ b₂ h
      apply hquotInj
      exact (MulAut.congr eC).injective (by simpa [αHom] using h)
    have hinner : ∀ b : ↥B1,
        αHom b ∈ (MulAut.conj : C0 →* MulAut C0).range := by
      intro b
      exact OutdiagTwE6.mem_inner_of_pow_eq_one
        (f := 1) (r := p) (by norm_num) hp hp2 hp3 hrf (hαHom_pow b)
    let βHom : ↥B1 →* (MulAut.conj : C0 →* MulAut C0).range :=
      αHom.codRestrict _ hinner
    have hβinj : Function.Injective βHom := by
      intro b₁ b₂ h
      apply hαinj
      exact congrArg Subtype.val h
    let eInn : C0 ≃* (MulAut.conj : C0 →* MulAut C0).range :=
      MonoidHom.ofInjective (CFSG.mulAutConj_injective_of_center_eq_bot hcentC0)
    let eta : ↥B1 →* C0 := eInn.symm.toMonoidHom.comp βHom
    let Ap : Subgroup C0 := eta.range
    have hB1el : IsElemAbelian p B1 := hA.mono hB1A
    have hApel : IsElemAbelian p Ap := by
      dsimp [Ap]
      exact CFSG.StandardType.isElemAbelian_range_of_isElemAbelian hB1el eta
    have heta_inj : Function.Injective eta := by
      intro b₁ b₂ h
      apply hβinj
      apply eInn.symm.injective
      simpa [eta] using h
    have hApcard : p ^ 4 ≤ Nat.card Ap := by
      have hcard : Nat.card Ap = Nat.card ↥B1 :=
        (Nat.card_congr (MonoidHom.ofInjective heta_inj).toEquiv).symm
      rw [hcard]
      exact hB1card
    have hKcard : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hpq : ¬ p ∣ 2 ^ 1 := by
      intro h
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) (by simpa using h)
      omega
    have hpq1 : ¬ p ∣ 2 ^ 1 + 1 := by
      intro h
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using h)
      omega
    have horder := ExcFrames.orderOf_eq_one_of_four_le_card_graphFixed
      (ℓ := 2) (f := 1) Nat.prime_two (by norm_num)
      (GaloisField 2 2) hKcard σ hσ
      (θ := frobQ 2 1) hσθ hp hp5 hpq hpq1
      (A := Ap) hApel hApcard
    have h2eq1 : (2 : ZMod p) = (1 : ZMod p) := by
      simpa using (orderOf_eq_one_iff.mp horder)
    have h2eq1' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa only [Nat.cast_ofNat, Nat.cast_one] using h2eq1
    have hmod : 2 % p = 1 % p :=
      (ZMod.natCast_eq_natCast_iff' 2 1 p).mp h2eq1'
    have h2lt : 2 < p := hpgt2
    have h1lt : 1 < p := by omega
    rw [Nat.mod_eq_of_lt h2lt, Nat.mod_eq_of_lt h1lt] at hmod
    omega

end Certificates

end CFSG.StandardType.RCKC1
