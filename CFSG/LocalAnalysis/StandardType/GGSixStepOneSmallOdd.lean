module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallImage
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Proof

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.commutator_inf_centralizer_eq_bot (hPU : GGPumpupInput)
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hpJ : p ∣ Nat.card J) {T : Subgroup G}
    (hG₀T : ggG0 p B x L D J ≤ Subgroup.normalizer (T : Set G)) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) :
    ⁅J, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer {d}⁆ = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : pCoreOf 2 (Subgroup.normalizer (T : Set G)) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.map_subtype_le _
  have hV2 : IsPGroup 2
      ↥(pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer {d}) :=
    ((Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _).map
      (Subgroup.normalizer (T : Set G)).subtype).to_le inf_le_left
  have hHV : Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer {d} ≤
      Subgroup.normalizer ((pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓
        Subgroup.centralizer {d} : Subgroup G) : Set G) := fun g hg =>
    ggMem_normalizer_inf_of (mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hg).1)
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).2)
  have hVH : pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer {d} ≤
      Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer {d} := inf_le_inf_right _ hQN
  have hJN : J ≤ Subgroup.normalizer (T : Set G) := h.le_ggG0.trans hG₀T
  have hJY : J ≤ Subgroup.centralizer {d} := (h.le_ggG0_inf hd).trans inf_le_right
  have hcomp : ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      K ≤ Subgroup.normalizer (T : Set G) → J ≤ K →
        ⁅J, pCoreOf 2 (Subgroup.normalizer (T : Set G)) ⊓ Subgroup.centralizer {d}⁆ = ⊥ := by
    intro K hK hKN hJK
    have hKH : K ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer {d} := le_inf hKN hK.1
    have hc := ggCommutator_eq_bot_of_isComponentOf
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK hKH inf_le_right) hVH
      (hKH.trans hHV) hV2
    exact le_bot_iff.mp (hc ▸ Subgroup.commutator_mono hJK le_rfl)
  have hS := h.sstar
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    have hzd : Subgroup.zpowers d = Subgroup.zpowers x :=
      le_antisymm (Subgroup.zpowers_le.mpr hdx)
        (Subgroup.zpowers_le.mpr (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hdx hd1))
    have hL : IsComponentOf L (Subgroup.centralizer {d}) := by
      rw [centralizer_singleton_eq_of_zpowers_eq hzd]
      exact hS.2.2.2.1
    exact hcomp L hL ((le_sup_left : L ≤ ggG0 p B x L D J).trans hG₀T)
      (h.j_le_inf.trans inf_le_left)
  · have hI := h.thmI
    have hDJ := h.stdSub
    have hD := eq_closure_pair_of_mem hI hDJ hd hdx
    obtain ⟨hA, hJA, hxA, hcase⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
    rcases hcase with hnbr | hxc
    ·
      obtain ⟨hAc, -⟩ := isComponentOf_of_isNeighborOf h.stdType (isNeighborOf_of_ggNbr hDJ hnbr)
      exact hcomp _ hAc ((le_ggG0_of_neighbor hnbr).trans hG₀T) hJA
    ·
      have hJc := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hD
      have hJV := (le_inf hJN hJY).trans hHV
      have hle := ggCommutator_le_pPrimeCoreOf (q := 2) hA hJA hJc hpJ hxA hxp hxc inf_le_right
        hJV hV2
      have hJW : J ≤ Subgroup.normalizer
          (LargeEvenPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) : Set G) :=
        hJY.trans (Subgroup.le_normalizer.trans (ggNormalizer_le_normalizer_pPrimeCoreOf p _))
      exact ggCommutator_eq_bot_of_odd (commutator_self_eq_of_isQuasisimple hJc.2.2) hJV hJW hV2
        ((h.stdType.2.2.2 D J hDJ).2 d hd hd1) hle

end Proof

section Input

theorem ggSixCentralizerOddInput_of_pumpup (hPU : GGPumpupInput) (hP : GGStdSubPrimeInput) :
    GGSixCentralizerOddInput := by
  intro G _ _ p B Bs x L D J t n f ψ h hpX
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpJ : p ∣ Nat.card J := hP G p B x L D J h.thmI h.stdSub
  by_contra hodd
  have h2X : 2 ∣ Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hDX : D ≤ Subgroup.normalizer
      (Subgroup.centralizer (ggG0 p B x L D J : Set G) : Set G) :=
    fun d hd => mem_normalizer_centralizer (h.bstar_le_normalizer (h.d_le_bstar hd))
  obtain ⟨T, hTX, hT1, hT2, hDT⟩ := ggExists_invariant_two_subgroup h.d_elem hDX hpX h2X
  have hchar := h.charTwo (Subgroup.normalizer (T : Set G)) ⟨T, hT1, hT2, rfl⟩
  have hG₀T : ggG0 p B x L D J ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer (T : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hTX hs)) g hg).symm
  have hJN : J ≤ Subgroup.normalizer (T : Set G) := h.le_ggG0.trans hG₀T
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.normalizer (T : Set G))) :=
    (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _).map
      (Subgroup.normalizer (T : Set G)).subtype
  have hQp : ¬ p ∣ Nat.card (pCoreOf 2 (Subgroup.normalizer (T : Set G))) := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    intro hdvd
    exact h.ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hDQ : D ≤ Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (T : Set G)) : Set G) :=
    fun d hd => mem_normalizer_pCoreOf (hDT hd)
  have hJQ : J ≤ Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (T : Set G)) : Set G) :=
    ggLe_centralizer_of_generation h.d_elem h.card_d hQp hDQ fun d hd hd1 =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (h.commutator_inf_centralizer_eq_bot hPU hpJ hG₀T hd hd1)
  have hJQ' : J ≤ pCoreOf 2 (Subgroup.normalizer (T : Set G)) := fun j hj =>
    hchar (Subgroup.mem_inf.mpr ⟨hJN hj, hJQ hj⟩)
  exact ggNot_isPGroup_of_isQuasisimple h.j_isComponentOf_centralizer.2.2 (hQ2.to_le hJQ')

end Input

end CFSG.StandardType
