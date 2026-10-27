module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagLift
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagOrth
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagSUFour
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedSLTwo
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.GroupTheory.PerfectImageRange
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly

theorem ggLieInnerDiag_of_suFour
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hInn : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (LargeEvenGUSet (Fin 4) K (2 ^ n)))) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I' := by
  have hodd : Odd (2 ^ n + 1) := by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hcop4 : Nat.Coprime 4 (2 ^ n + 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  have hcop : (2 ^ n + 1).Coprime 4 := hcop4.symm
  have hcenterSU : Subgroup.center ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hK hn (by norm_num)
      hcop4
  let SU := ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))
  letI : Group SU := inferInstance
  have hcenter : Subgroup.center SU = ⊥ := hcenterSU
  let e : SU ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      ⟨ggLieSU3Fixed_projMk_injective (K := K) (n := n) hK,
        QuotientGroup.mk'_surjective _⟩
  let ψ : X →* SU :=
    e.symm.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨z, hz⟩ := e.symm.surjective y
    obtain ⟨w, hw⟩ := θ.surjective z
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) w
    refine ⟨v, ?_⟩
    show e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) v)) = y
    rw [hv, hw, hz]
  have hkerψ : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) x)) = 1 := by
        simpa [ψ] using hx
      have h2 : θ ((QuotientGroup.mk' (Subgroup.center X)) x) = 1 :=
        e.symm.injective (by simpa using h1)
      have h3 : (QuotientGroup.mk' (Subgroup.center X)) x = 1 :=
        θ.injective (by simpa using h2)
      have h4 : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
        rw [MonoidHom.mem_ker]
        exact h3
      rwa [QuotientGroup.ker_mk'] at h4
    · intro hx
      have h1 : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
        rwa [QuotientGroup.ker_mk']
      rw [MonoidHom.mem_ker] at h1
      change e.symm (θ ((QuotientGroup.mk' (Subgroup.center X)) x)) = 1
      rw [h1, map_one, map_one]
  have hS1 : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
    have hcp := CFSG.StandardType.StdSubRestU.ggCenterPrime_unitary (K := K) (n := n)
      (d := 4) (p := 3) hK hn (by norm_num) (by norm_num) Nat.prime_three (by norm_num)
      (by norm_num)
    refine hcp X (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
      (θ.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ hX
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center X)) x = 1 := by
      apply θ.injective
      simpa using hx
    have hx'' : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
      rw [MonoidHom.mem_ker]
      exact hx'
    rwa [QuotientGroup.ker_mk'] at hx''
  have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenGUSet (Fin 4) K (2 ^ n)) ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
    CFSG.StandardType.TableB.matConjImage_gu_subset_inn (d := 4) (n := n) hK hcop
  have hS2 : ∀ a ∈ A, ∃ s : SU, ∀ x : X, ψ (a x) = s * ψ x * s⁻¹ := by
    intro a ha
    obtain ⟨s, hs⟩ := hI (hInn a ha)
    refine ⟨e.symm s, ?_⟩
    intro x
    have hstep : θ (((a x : X)) : X ⧸ Subgroup.center X) =
        s * θ ((x : X) : X ⧸ Subgroup.center X) * s⁻¹ := by
      rw [← ggInducedAut_apply θ a x, ← hs, MulAut.conj_apply]
    change e.symm (θ (((a x : X)) : X ⧸ Subgroup.center X)) =
      e.symm s * e.symm (θ ((x : X) : X ⧸ Subgroup.center X)) * (e.symm s)⁻¹
    rw [hstep, map_mul, map_mul, map_inv]
  exact ggLieInnerDiag_of_lift hraw hiso hX hl hcenter ψ hψsurj hkerψ hS1 hS2
    (ggInnerDiagOnComps_suFour hK hn)

theorem ggLieInnerDiag_of_omegaMinus (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
    (hInn : GGInducedInn A θ
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGAutsInduceOn A J θ' I' := by
  haveI : Group.IsPerfect X := ⟨hX⟩
  have hcenter : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot X
  have hinn : ∀ a ∈ A, ∃ s : X ⧸ Subgroup.center X, ∀ x : X,
      (QuotientGroup.mk' (Subgroup.center X)) (a x) =
        s * (QuotientGroup.mk' (Subgroup.center X)) x * s⁻¹ := by
    intro a ha
    obtain ⟨r, hr⟩ := hInn a ha
    refine ⟨θ.symm r, fun x => ?_⟩
    apply θ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h1 : θ ((QuotientGroup.mk' (Subgroup.center X)) (a x)) =
        ggInducedAut θ a (θ ((QuotientGroup.mk' (Subgroup.center X)) x)) :=
      (ggInducedAut_apply θ a x).symm
    rw [h1, ← hr, MulAut.conj_apply]
  exact ggLieInnerDiag_of_lift hraw hiso hX hl hcenter
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) h3 hinn
    (ggInnerDiagOnComps_of_mulEquiv θ.symm (ggInnerDiagOnComps_omegaMinus hK hm hbc))

theorem ggLieInnerDiagInput_of_known
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGLieInnerDiagInput := by
  intro X _ _ hX A δ J hl hm
  obtain ⟨-, lab, hlab, hrawD⟩ := hm
  have hTw : GGLabelTwClassical lab := by
    have hrawc := hrawD
    obtain ⟨R, _instR, I, F, hQ⟩ := largeEvenRawDatum_exists hrawc
    obtain ⟨-, -, θ, hP⟩ := hQ
    exact hP.1
  obtain ⟨tag, rank, nn⟩ := lab
  rcases hTw with htag | ⟨htag, hrank⟩
  ·
    subst htag
    have hr2 : 2 ≤ rank := hlab.2
    by_cases hr : rank = 3
    · subst hr
      simp only [LargeEvenRawDatum] at hrawD
      obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hrawD
      obtain ⟨-, -, θ, hP⟩ := hQK
      exact ggLieInnerDiag_of_suFour hraw hiso hX hl hK hlab.1 θ hP.2
    · by_cases hr2' : rank = 2
      · subst hr2'
        simp only [LargeEvenRawDatum] at hrawD
        obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hrawD
        obtain ⟨-, -, θ, hP⟩ := hQK
        exact (ggLieSU3Fixed_false_of_slTwo hX hl hK θ hP.2).elim
      · obtain ⟨r, rfl⟩ : ∃ r, rank = r + 4 := ⟨rank - 4, by omega⟩
        simp only [LargeEvenRawDatum] at hrawD
        obtain ⟨K, _instK, _instFinK, hK, b, c, hbc, hQK⟩ := hrawD
        obtain ⟨-, -, θ, hP⟩ := hQK
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fintype K := Fintype.ofFinite K
        haveI : CharP K 2 :=
          charP_of_card_eq_prime_pow (p := 2) (f := nn)
            (by rw [← Nat.card_eq_fintype_card, hK])
        have hker : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker =
            Subgroup.center X := by
          rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X))
            θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']
        have hcp : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
          CorFourTwoOpen.ggCenterPrime_omegaMinus (K := K) Nat.prime_three (by norm_num)
            (m := r + 3) (by omega) hbc X (θ.toMonoidHom.comp (QuotientGroup.mk' _))
            (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le hX
        exact ggLieInnerDiag_of_omegaMinus hraw hiso hX hl hcp hK (m := r + 3) (by omega)
          hbc θ hP.2
  ·
    subst htag
    subst hrank
    simp only [LargeEvenRawDatum] at hrawD
    obtain ⟨K, _instK, _instFinK, hK, hQK⟩ := hrawD
    obtain ⟨-, -, θ, hP⟩ := hQK
    exact ggLieInnerDiag_of_suFour hraw hiso hX hl hK hlab.1 θ hP.2

theorem ggLieInnerDiagInput_holds :
    GGLieInnerDiagInput :=
  ggLieInnerDiagInput_of_known ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))

end CFSG.StandardType.SCFourCover

end
