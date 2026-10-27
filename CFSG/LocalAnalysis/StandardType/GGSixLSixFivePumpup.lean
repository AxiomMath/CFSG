module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompKd
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallOdd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Proof

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.kd_cases (hPU : GGPumpupInput) (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hpJ : p ∣ Nat.card J) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}) ∨
      ∃ A : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer {d}) A ∧ J ≤ A ∧
        A = J ⊔ LargeEvenPPrimeCoreOf p A ∧
        ∀ K : Subgroup G, CFSG.Assembly.IsQuasisimple ↥K → J ≤ K →
          K ≤ Subgroup.centralizer {d} → K = J := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hS := h.sstar
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := h.j_comp.2.2
  have hcomp : ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      K ≤ ggG0 p B x L D J → J ≤ K →
        IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}) := by
    intro K hK hKG hJK
    have hKH : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK (le_inf hKG hK.1) inf_le_right
    rw [ggKd_eq_of_le_component hKH hJq hJK]
    exact hK
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    left
    have hzd : Subgroup.zpowers d = Subgroup.zpowers x :=
      le_antisymm (Subgroup.zpowers_le.mpr hdx)
        (Subgroup.zpowers_le.mpr (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hdx hd1))
    have hL : IsComponentOf L (Subgroup.centralizer {d}) := by
      rw [centralizer_singleton_eq_of_zpowers_eq hzd]
      exact hS.2.2.2.1
    exact hcomp L hL le_sup_left (h.j_le_inf.trans inf_le_left)
  · have hI := h.thmI
    have hDJ := h.stdSub
    have hD := eq_closure_pair_of_mem hI hDJ hd hdx
    obtain ⟨hA, hJA, hxA, hcase⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
    rcases hcase with hnbr | hxc
    ·
      left
      obtain ⟨hAc, -⟩ := isComponentOf_of_isNeighborOf h.stdType (isNeighborOf_of_ggNbr hDJ hnbr)
      exact hcomp _ hAc (le_ggG0_of_neighbor hnbr) hJA
    ·
      right
      have hJc := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hD
      have hAeq := ggEq_sup_pPrimeCoreOf_of_centralizes hA hJA hJc hpJ hxA hxp hxc
      exact ⟨_, hA, hJA, hAeq, fun K hK hJK hKY =>
        ggEq_of_le_of_eq_sup_pPrimeCoreOf hA.2.1 hJA hAeq hJq hpJ hK hJK hKY⟩

theorem ggOdd_card_pPrimeCoreOf_of_isQuasisimple [Fact p.Prime] {K : Subgroup G}
    (hK : CFSG.Assembly.IsQuasisimple ↥K) (hpK : p ∣ Nat.card K)
    (hZ : Odd (Nat.card (Subgroup.center ↥K))) : Odd (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
  set O := LargeEvenPPrimeCoreOf p K with hO
  have hOK : O ≤ K := Subgroup.map_subtype_le _
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := fun k hk =>
    ggNormalizer_le_normalizer_pPrimeCoreOf p K (Subgroup.le_normalizer hk)
  rcases ggLe_center_or_eq_of_normalized hK hOK hKO with hc | heq
  · have hle : O ≤ ggCenterOf K := by
      intro o ho
      refine ⟨⟨o, hOK ho⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ho) w w.2)
    have hcard := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective] at hcard
    exact Odd.of_dvd_nat hZ hcard
  · exfalso
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
      ((ggPPrimeCoreOf_coprime K).coprime_dvd_right (Subgroup.card_dvd_of_le heq.ge)) hpK

theorem GGSixCtxV2.exists_pComponent_odd (hPU : GGPumpupInput)
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hpJ : p ∣ Nat.card J)
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZK : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    {e : G} (he : e ∈ D) (he1 : e ≠ 1) :
    ∃ A : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer {e}) A ∧ J ≤ A ∧
      Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  rcases h.kd_cases hPU hpJ he he1 with hK | ⟨A, hA, hJA, hAeq, -⟩
  · have hJK : J ≤ ggKd p B x L D J e := le_ggKd p B x L D J e
    have hpK : p ∣ Nat.card (ggKd p B x L D J e) := hpJ.trans (Subgroup.card_dvd_of_le hJK)
    have hKp : LargeEvenPComponent p (Subgroup.centralizer {e}) (ggKd p B x L D J e) :=
      (largeEvenPComponent_iff_lBalance p _ _).2 ⟨hK.1,
        lBalanceIsPComponent_of_isComponentOf hK (not_le_lBalancePrimeCore_of_dvd hpK)⟩
    exact ⟨_, hKp, hJK, ggOdd_card_pPrimeCoreOf_of_isQuasisimple hK.2.2 hpK (hZK e he he1)⟩
  · have hY : Odd (Nat.card (⁅J, LargeEvenPPrimeCoreOf p (Subgroup.centralizer {e})⁆ :
        Subgroup G)) := (h.stdType.2.2.2 D J h.stdSub).2 e he he1
    exact ⟨A, hA, hJA, ggOdd_card_pPrimeCoreOf hp hA h.j_comp.2.2 hJA hAeq hZJ hY⟩

end Proof

section Inputs

theorem ggSixKdPumpupInput_holds (hPU : GGPumpupInput) (hP : GGStdSubPrimeInput) :
    GGSixKdPumpupInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx _ _ _ d hd hd1 hKc hsn
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hctx.thmI hctx.stdSub
  rcases hctx.kd_cases hPU hpJ hd hd1 with hK | ⟨A, hA, hJA, hAeq, hKJ⟩
  · exact absurd hK.2.1 hsn
  · exact ⟨hKJ _ hKc.2.2 (le_ggKd p B x L D J d) (hKc.1.trans inf_le_right), A, hA, hJA, hAeq⟩

theorem ggSixKdComponentInput_of_pComp (hPU : GGPumpupInput) (hP : GGStdSubPrimeInput)
    (hpc : GGSixPCompCentralizeInput) : GGSixKdComponentInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hctx.thmI hctx.stdSub
  rcases hctx.kd_cases hPU hpJ hd hd1 with hK | ⟨A, hA, hJA, hAeq, -⟩
  · exact hK
  · have hY : Odd (Nat.card (⁅J, LargeEvenPPrimeCoreOf p (Subgroup.centralizer {d})⁆ :
        Subgroup G)) := (hctx.stdType.2.2.2 D J hctx.stdSub).2 d hd hd1
    have hEodd := ggOdd_card_pPrimeCoreOf hctx.prime hA hctx.j_comp.2.2 hJA hAeq hZJ hY
    have hc := hpc G p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1 A hA hJA hAeq hEodd
    have hJs : IsSubnormal J (Subgroup.centralizer {d}) :=
      isSubnormal_of_eq_sup_pPrimeCore hA.2.1 hJA hAeq hc
    have hJc : IsComponentOf J (Subgroup.centralizer {d}) :=
      ⟨isSubnormal_le_of_assembly hJs, hJs, hctx.j_comp.2.2⟩
    have hJH : IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJc
        (le_inf hctx.le_ggG0 hJc.1) inf_le_right
    rw [ggKd_eq_of_le_component hJH hctx.j_comp.2.2 le_rfl]
    exact hJc

theorem ggSixJComponentInput_of_pComp (hPU : GGPumpupInput) (hP : GGStdSubPrimeInput)
    (h64 : GGSixCentreOddInput) (hpc : GGSixPCompCentralizeInput) : GGSixJComponentInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx d hd hd1
  have hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) :=
    ggSixCentralizerOddInput_of_pumpup hPU hP G p B Bs x L D J t n f ψ hctx
      (not_dvd_card_centralizer_ggG0_of_stdSub hctx.prime hctx.sstar hctx.stdType hctx.stdSub)
  obtain ⟨hZJ, hZK⟩ := h64 G p B Bs x L D J t n f ψ hctx hodd
  have hK := ggSixKdComponentInput_of_pComp hPU hP hpc G p B Bs x L D J t n f ψ hctx hodd hZJ
    hZK d hd hd1
  exact ⟨ggKd p B x L D J d, CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK
    (ggKd_le (hctx.le_ggG0_inf hd)) inf_le_right, le_ggKd p B x L D J d⟩

end Inputs

end CFSG.StandardType
