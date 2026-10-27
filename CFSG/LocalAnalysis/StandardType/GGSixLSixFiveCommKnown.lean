module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveComm
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFivePumpup
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLieKnown
import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.kd_cases' (hPU : GGPumpupInput) (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hpJ : p ∣ Nat.card J) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    (IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}) ∧
      LargeEvenMarking ↥(ggKd p B x L D J d) (fun _ _ _ _ _ _ => True)) ∨
      ∃ A : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer {d}) A ∧ J ≤ A ∧
        A = J ⊔ LargeEvenPPrimeCoreOf p A := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hS := h.sstar
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := h.j_comp.2.2
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    left
    rw [h.ggKd_eq_of_mem_zpowers hdx hd1]
    have hzd : Subgroup.zpowers d = Subgroup.zpowers x :=
      le_antisymm (Subgroup.zpowers_le.mpr hdx)
        (Subgroup.zpowers_le.mpr (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hdx hd1))
    refine ⟨?_, largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) h.stdType.1⟩
    rw [centralizer_singleton_eq_of_zpowers_eq hzd]
    exact hS.2.2.2.1
  · have hI := h.thmI
    have hDJ := h.stdSub
    have hD := eq_closure_pair_of_mem hI hDJ hd hdx
    obtain ⟨hA, hJA, hxA, hcase⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
    rcases hcase with hnbr | hxc
    ·
      left
      have hnb := isNeighborOf_of_ggNbr hDJ hnbr
      obtain ⟨hAc, -⟩ := isComponentOf_of_isNeighborOf h.stdType hnb
      have hKH : IsComponentOf _ (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :=
        CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hAc
          (le_inf (le_ggG0_of_neighbor hnbr) hAc.1) inf_le_right
      rw [ggKd_eq_of_le_component hKH hJq hJA]
      exact ⟨hAc, largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
        (h.stdType.2.2.1 d _ hnb).2⟩
    ·
      right
      have hJc := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hD
      exact ⟨_, hA, hJA, ggEq_sup_pPrimeCoreOf_of_centralizes hA hJA hJc hpJ hxA hxp hxc⟩

theorem GGSixCtxV2.ggCommutator_le_of_known (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hK3 : GGOutTwoCommInner) (hPU : GGPumpupInput) (hJp : GGStdSubPrimeInput)
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZK : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    {V : Subgroup G} {r : G} (hrV : r ∈ V) (hVJ : V ≤ J) (hV2 : IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (hrZ : r ∉ Subgroup.centralizer (J : Set G))
    (hK1 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (L : Set G) →
      Y ≤ Subgroup.normalizer (J : Set G) → Y ≤ Subgroup.centralizer (D : Set G) →
      Y ≤ Subgroup.centralizer {r} →
      (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set G)) →
      ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set G),
        v * y * v⁻¹ * y⁻¹ = r ^ k * z)
    (hK2 : ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup G,
      IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) → J ≤ K →
      Odd (Nat.card (Subgroup.center ↥K)) →
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set G)) ≤ Subgroup.normalizer (V : Set G))
    {e : G} (he : e ∈ D) (he1 : e ≠ 1) :
    ⁅V, pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤
      Subgroup.zpowers r := by
  have hp : p.Prime := hctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hr1 : r ≠ 1 := fun h => hrZ (h ▸ Subgroup.one_mem _)
  have hr2 : r ^ 2 = 1 := hV2.2 r hrV
  have hrJ : r ∈ J := hVJ hrV
  have hpJ : p ∣ Nat.card J := hJp G p B x L D J hctx.thmI hctx.stdSub
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hctx.j_comp.2.2
  have hJL : J ≤ L := hctx.j_le_inf.trans inf_le_left
  have hrC : ∀ K : Subgroup G, J ≤ K → r ∉ Subgroup.centralizer (K : Set G) := fun K hJK hrK =>
    hrZ (Subgroup.centralizer_le hJK hrK)
  set P := pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) with hPdef
  have hP2 : IsPGroup 2 P := ggPCoreOf_two_isPGroup _
  have hPr : P ≤ Subgroup.centralizer ({r} : Set G) := Subgroup.map_subtype_le _
  have hDcomm : ∀ a ∈ D, ∀ c ∈ D, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hctx.d_elem.1.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨c, hc⟩)
  have hDC : ∀ b ∈ D, b * r = r * b := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp (hctx.le_centralizer_J hb) r hrJ).symm
  have hDr : D ≤ Subgroup.centralizer ({r} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDC b hb)
  have hDe : D ≤ Subgroup.centralizer ({e} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm b hb e he)
  have hDP : ∀ b ∈ D, b ∈ Subgroup.normalizer (P : Set G) := fun b hb =>
    mem_normalizer_pCoreOf (hDr hb)
  have hVr : ∀ v ∈ V, v * r = r * v := fun v hv =>
    congrArg Subtype.val (hV2.1.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨r, hrV⟩)
  have hVP : ∀ v ∈ V, v ∈ Subgroup.normalizer (P : Set G) := fun v hv =>
    mem_normalizer_pCoreOf (Subgroup.mem_centralizer_singleton_iff.mpr (hVr v hv))
  set Ye := P ⊓ Subgroup.centralizer ({e} : Set G) with hYe
  have hYe2 : IsPGroup 2 Ye := hP2.to_le inf_le_left
  have hYer : Ye ≤ Subgroup.centralizer ({r} : Set G) := inf_le_left.trans hPr
  have hDYe : D ≤ Subgroup.normalizer (Ye : Set G) := fun b hb =>
    ggMemNormalizerInf (hDP b hb) (Subgroup.le_normalizer (hDe hb))
  have hfix : ∀ y ∈ Ye, (∀ b ∈ D, b * y * b⁻¹ = y) → ∀ v ∈ V,
      v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers r := by
    intro y hy hfx
    set Y₁ := P ⊓ Subgroup.centralizer (D : Set G) with hY₁
    have hJD : J ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.le_centralizer_iff.mp hctx.le_centralizer_J
    have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hctx.sstar.2.2.2.1
    have hJc : IsComponentOf J (Subgroup.centralizer (D : Set G)) :=
      hctx.j_isComponentOf_centralizer
    have hzr : ∀ z ∈ Y₁, z * r = r * z := fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPr (Subgroup.mem_inf.mp hz).1)
    have hY₁2 : IsPGroup 2 Y₁ := hP2.to_le inf_le_left
    have hY₁L : Y₁ ≤ Subgroup.normalizer (L : Set G) := by
      intro z hz
      have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hctx.x_mem_d)
          (Subgroup.mem_inf.mp hz).2
      exact ggMem_normalizer_of_component hL (hJL hrJ) (hrC L hJL) (Subgroup.le_normalizer hzx)
        (hzr z hz)
    have hY₁J : Y₁ ≤ Subgroup.normalizer (J : Set G) := fun z hz =>
      ggMem_normalizer_of_component hJc hrJ (hrC J le_rfl)
        (Subgroup.le_normalizer (Subgroup.mem_inf.mp hz).2) (hzr z hz)
    have hY₁c : ∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y₁ : Set G) := fun c hc hcr =>
      ggMemNormalizerInf (mem_normalizer_pCoreOf (Subgroup.mem_centralizer_singleton_iff.mpr hcr))
        (Subgroup.le_normalizer (hJD hc))
    have hY₁r : Y₁ ≤ Subgroup.centralizer ({r} : Set G) := inf_le_left.trans hPr
    have hT := ggFixed_mem_commModR hr2 hrJ hP2 hZJ hVJ hVP inf_le_left hY₁J hY₁r
      (hK1 Y₁ hY₁2 hY₁L hY₁J inf_le_right hY₁r hY₁c)
    have hyY₁ : y ∈ Y₁ := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      calc b * y = (b * y * b⁻¹) * b := by group
        _ = y * b := by rw [hfx b hb]
    exact (hT hyY₁).2
  have hcom : ∀ b ∈ D, ∀ y ∈ Ye, ∀ v ∈ V,
      v * (y⁻¹ * (b * y * b⁻¹)) * v⁻¹ * (y⁻¹ * (b * y * b⁻¹))⁻¹ ∈ Subgroup.zpowers r := by
    intro b hb y hy v hv
    have hye : y ∈ Subgroup.centralizer ({e} : Set G) := (Subgroup.mem_inf.mp hy).2
    have hyr : y * r = r * y := Subgroup.mem_centralizer_singleton_iff.mp (hYer hy)
    have hbyb : b * y * b⁻¹ ∈ Ye := (Subgroup.mem_normalizer_iff.mp (hDYe hb) y).mp hy
    rcases hctx.kd_cases' hPU hpJ he he1 with ⟨hKc, hmk⟩ | ⟨A, hA, hJA, hAeq⟩
    ·
      have hJK : J ≤ ggKd p B x L D J e := le_ggKd p B x L D J e
      have hKe : IsComponentOf (ggKd p B x L D J e) (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) :=
        CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKc
          (le_inf (hctx.ggKd_le_ggG0 he) hKc.1) inf_le_right
      have hYeK : Ye ≤ Subgroup.normalizer (ggKd p B x L D J e : Set G) := fun z hz =>
        ggMem_normalizer_of_component hKc (hJK hrJ) (hrC _ hJK)
          (Subgroup.le_normalizer (Subgroup.mem_inf.mp hz).2)
          (Subgroup.mem_centralizer_singleton_iff.mp (hYer hz))
      have hbK : b ∈ Subgroup.normalizer (ggKd p B x L D J e : Set G) :=
        ggMem_normalizer_of_component hKc (hJK hrJ) (hrC _ hJK)
          (Subgroup.le_normalizer (hDe hb)) (hDC b hb)
      have hKY : ggKd p B x L D J e ⊓ Subgroup.centralizer ({r} : Set G) ≤
          Subgroup.normalizer (Ye : Set G) := fun n hn =>
        ggMemNormalizerInf (mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hn).2)
          (Subgroup.le_normalizer (hctx.ggKd_le_centralizer he (Subgroup.mem_inf.mp hn).1))
      have hbodd : Odd (orderOf b) := by
        have hdvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one (hctx.d_elem.2 b hb)
        exact Odd.of_dvd_nat (hp.odd_of_ne_two hctx.ne_two) hdvd
      exact ggComm_of_component hK3 hmk (hZK e he he1) (hJK hrJ) hr2 hr1 hV4 hrV
        (hVJ.trans hJK) (hK2 e he he1 _ hKe hJK (hZK e he he1)) hYe2 hYeK hYer hKY hbK hbodd
        (hDYe hb) hy hv
    ·
      have hY : Odd (Nat.card (⁅J, LargeEvenPPrimeCoreOf p (Subgroup.centralizer {e})⁆ :
          Subgroup G)) := (hctx.stdType.2.2.2 D J hctx.stdSub).2 e he he1
      have hEodd : Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) :=
        ggOdd_card_pPrimeCoreOf hp hA hJq hJA hAeq hZJ hY
      have hAE : A ≤ Subgroup.normalizer (LargeEvenPPrimeCoreOf p A : Set G) := fun a ha =>
        ggNormalizer_le_normalizer_pPrimeCoreOf p A (Subgroup.le_normalizer ha)
      have hyA : y ∈ Subgroup.normalizer (A : Set G) :=
        ggMem_normalizer_of_pComponent hA hJA hJq hpJ hrJ (hrC J le_rfl) hye hyr
      have hbA : b ∈ Subgroup.normalizer (A : Set G) :=
        ggMem_normalizer_of_pComponent hA hJA hJq hpJ hrJ (hrC J le_rfl) (hDe hb) (hDC b hb)
      have hbJ : ∀ j ∈ J, b * j = j * b := fun j hj =>
        (Subgroup.mem_centralizer_iff.mp (hctx.le_centralizer_J hb) j hj).symm
      have h1 := ggComm_of_pComponent_aux hAeq hAE hEodd hP2 hyA
        (ggNormalizer_le_normalizer_pPrimeCoreOf p A hyA) hbA
        (ggNormalizer_le_normalizer_pPrimeCoreOf p A hbA) hbJ (Subgroup.mem_inf.mp hy).1
        (Subgroup.mem_inf.mp hbyb).1 (hVJ hv) (hVP v hv)
      rw [h1]
      exact Subgroup.one_mem _
  exact ggCommutator_le_zpowers_of_pieces hctx.ne_two (IsPGroup.of_card hctx.card_d) hYe2 hDYe
    hDr hYer hfix hcom

end Ctx

section Final

theorem ggSixPCompRootCommInput_of_known (hK : GGSixRootCommKnown) (hK3 : GGOutTwoCommInner)
    (hA6 : GGSixJNotA6Input) (hMk : GGInnerDiagMarkingInput) (hPU : GGPumpupInput)
    (hJp : GGStdSubPrimeInput) (hnc : GGLNoncyclicInput) : GGSixPCompRootCommInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd hZJ hZK
  have hp := hctx.prime
  have hJA6 := hA6 G p B Bs x L D J t n f ψ hctx
  obtain ⟨hBBs, hBsE, hBsN, hVI, hBsCG, hBsC, hBsRk⟩ := ggSixCtx_bstar_rank_facts hctx
  have hHL := ggSixCtx_normalizer_and_innerDiag_on_L hctx
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, -, -, -⟩ := hctx.2
  have hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
    ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf0, hmodel⟩
  have hmark : LargeEvenMarking ↥(ggG0 p B x L D J) (fun _ _ _ I _ θ => ∀ a ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2)
      (ggInnerDiagOn_of_presents_mk hMk hpres hBsN hVI)
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hBBs.trans (hctx.bstar_le_normalizer_j hnc)
  have hBD : B ⊓ Subgroup.centralizer (J : Set G) = D := hctx.stdSub.1.2.2.2.2.2.2.symm
  have hJinf : IsComponentOf J (Subgroup.centralizer (D : Set G) ⊓ ggG0 p B x L D J) := by
    rw [inf_comm]
    exact hctx.j_isComponentOf_inf
  have hLG₀ : L ≤ ggG0 p B x L D J := le_ggG0_left p B x L D J
  have hLx : ∃ x' ∈ D, x' ≠ 1 ∧
      IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x'}) :=
    ⟨x, hctx.x_mem_d, hctx.sstar.2.2.1,
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hctx.sstar.2.2.2.1
        (le_inf hLG₀ hctx.sstar.2.2.2.1.1) inf_le_right⟩
  obtain ⟨V, r, hrV, hVJ, hV2, hV4, hrZ, hconj, hK1, hK2⟩ :=
    hK G t n f ψ p (ggG0 p B x L D J) Bs B D J L hpres hodd hp hctx.ne_two hBsE hBBs
      hctx.stdSub.1.1 hctx.card_d hBsN hmark hBJ hBD hctx.pow_four_le_card_b hBsC hBsRk hBsCG hHL.1
      hHL.2 hJinf hZJ hLG₀ hLx hctx.not_le_centralizer_L hctx.j_comp hJA6
  refine Or.inr (Or.inr (Or.inl ⟨V, r, hrV, hVJ, hV2, hV4.ge, hrZ, hconj, fun e he he1 => ?_⟩))
  exact hctx.ggCommutator_le_of_known hK3 hPU hJp hZJ hZK hrV hVJ hV2 hV4 hrZ hK1 hK2 he he1

theorem ggSixPCompRootCommInput_of_knownInputs (h : GGSixRootCommKnown ∧ GGOutTwoCommInner ∧
    GGSixJNotA6Input)
    (hMk : GGInnerDiagMarkingInput) (hPU : GGPumpupInput) (hJp : GGStdSubPrimeInput)
    (hnc : GGLNoncyclicInput) : GGSixPCompRootCommInput :=
  ggSixPCompRootCommInput_of_known h.1 h.2.1 h.2.2 hMk hPU hJp hnc

end Final

end CFSG.StandardType
