module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowInput
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowTriangle
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Rigid
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (SwapComponentData centralizerPerfectCore)

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {M : Type*} [Group M] {C : Subgroup M}
  (e : L ≃* C)

theorem perfectCore_subgroupOf_of_le [Finite M] {H : Subgroup M} (hH : H ≤ C) :
    (perfectCore H).subgroupOf C = perfectCore (H.subgroupOf C) := by
  apply Subgroup.map_injective C.subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left hH, inf_of_le_left ((perfectCore_le H).trans hH)]

theorem modelToG_perfectCore_inf_centralizer [Finite G] [Finite M] {D Y : Subgroup M}
    (hD : D ≤ C) (hY : Y ≤ C) :
    modelToG e (perfectCore (D ⊓ centralizer (Y : Set M))) =
      perfectCore (modelToG e D ⊓ centralizer (modelToG e Y : Set G)) := by
  have h1 : (D ⊓ centralizer (Y : Set M)).subgroupOf C =
      D.subgroupOf C ⊓ centralizer (Y.subgroupOf C : Set C) := by
    rw [centralizer_subgroupOf hY]
    exact Subgroup.comap_inf _ _ _
  have h2 : UnitaryPilot.modelToG e (D.subgroupOf C ⊓ centralizer (Y.subgroupOf C : Set C)) =
      modelToG e D ⊓ centralizer (modelToG e Y : Set G) := by
    rw [UnitaryPilot.modelToG, Subgroup.map_inf_eq _ _ _ e.symm.injective,
      Subgroup.map_inf_eq _ _ _ L.subtype_injective]
    change modelToG e D ⊓ UnitaryPilot.modelToG e (centralizer (Y.subgroupOf C : Set C)) = _
    rw [← UnitaryPilot.inf_centralizer_modelToG, ← inf_assoc,
      inf_of_le_left (modelToG_le e D)]
    rfl
  rw [modelToG, perfectCore_subgroupOf_of_le (inf_le_left.trans hD), h1, UnitaryPilot.modelToG,
    CFSG.Quasithin.map_perfectCore, CFSG.Quasithin.map_perfectCore, ← UnitaryPilot.modelToG,
    h2]

theorem modelToG_sup_of_le {H₁ H₂ : Subgroup M} (h₁ : H₁ ≤ C) (h₂ : H₂ ≤ C) :
    modelToG e (H₁ ⊔ H₂) = modelToG e H₁ ⊔ modelToG e H₂ := by
  rw [modelToG, modelToG, modelToG, subgroupOf_sup h₁ h₂, UnitaryPilot.modelToG_sup]

theorem modelToG_eq_of_le {H : Subgroup M} (hH : C ≤ H) : modelToG e H = L := by
  rw [modelToG, (subgroupOf_eq_top).2 hH, UnitaryPilot.modelToG_top]

noncomputable def modelToGEquivOfLe {H : Subgroup M} (hH : H ≤ C) : H ≃* modelToG e H :=
  (subgroupOfEquivOfLe hH).symm.trans (UnitaryPilot.modelToGEquiv e (H.subgroupOf C))

theorem symm_mem_modelToG_of_mem {H : Subgroup M} {x : M} (hx : x ∈ H) (hxC : x ∈ C) :
    ((e.symm ⟨x, hxC⟩ : L) : G) ∈ modelToG e H :=
  symm_mem_modelToG e hx

end Transport

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem nonempty_swapCover_2E6_nonsplit_two (hset : SeitzSetting G L)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A)
    (htX : t ∈ centralizer (modelToG e A : Set G))
    {Kc : Subgroup (centralizer (modelToG e A : Set G) ⧸
      oddCore (centralizer (modelToG e A : Set G)))} (hKc : IsComponent Kc)
    (hDKK : ((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk'
        (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk'
      (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk'
      (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hφ : Nonempty (Kc ≃* ((modelToG e (su6Levi σ)).subgroupOf
      (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))))) :
    Nonempty (SwapCover t (modelToG e A) (modelToG e (su6Levi σ))
      (centralizerPerfectCore (modelToG e A))) := by
  have hf : 1 ≤ 1 := le_rfl
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc rfl htX rfl
  obtain ⟨-, -, hDX, -, -, -⟩ := neighbour_data_2E6_nonsplit_two hset hk hK hσ e hAJ hA hcyc
  have hDL : modelToG e (su6Levi σ) ≤ L := modelToG_le e _
  have hDt : modelToG e (su6Levi σ) ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hss : QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : centralizer (modelToG e A : Set G)) * ⟨t, htX⟩ = 1 from
      Subtype.ext htt, map_one]
  have hτD : QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))) ⟨t, htX⟩ ∈
      centralizer ((((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) : Subgroup _) :
        Set (centralizer (modelToG e A : Set G) ⧸
          oddCore (centralizer (modelToG e A : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))
      ⟨t, htX⟩) Kc (((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))) :=
    ⟨hss, hKc, hne, hcomm, hDKK, hτD, hsyl⟩
  have hKp : ⁅Kc, Kc⁆ = Kc := isPerfect_iff.mp hKc.1.1
  obtain ⟨hBsup, hBK⟩ := hasBLift_sup_conj_2E6_nonsplit_two twistedE6TwoDiagonalRigidity_holds
    hset hk hK hσ e htC ht hAJ hA hcyc rfl htX rfl hKp hcomm
  obtain ⟨hDs, hDperf, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  have eD := mapSymmEquiv (G := G) e ((su6Levi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  change _ ≃* modelToG e (su6Levi σ) at eD
  have hDp : ⁅modelToG e (su6Levi σ), modelToG e (su6Levi σ)⁆ = modelToG e (su6Levi σ) :=
    isPerfect_iff.mp (Group.IsPerfect.ofSurjective
    (f := eD.toMonoidHom) eD.surjective)
  have hsimple : IsSimpleGroup ((modelToG e (su6Levi σ)).subgroupOf
      (centralizer (modelToG e A : Set G))) :=
    ((subgroupOfEquivOfLe hDX).trans eD.symm).isSimpleGroup
  obtain ⟨eDb⟩ := F4Pilot.nonempty_mulEquiv_map_of_isSimpleGroup
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G)))) hsimple
    (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨eK⟩ := hφ
  have hOut : Group.IsSolvable (Outer Kc) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (eK.trans (eDb.symm.trans ((subgroupOfEquivOfLe hDX).trans eD.symm)))).2.2 hDo
  obtain ⟨Kc', hperf, hc, hsup, hnorm⟩ :=
    exists_swapFactor_of_swapComponentData htX hdata hOut hBK hBsup
  have hDE : modelToG e (su6Levi σ) ≤ centralizerPerfectCore (modelToG e A) :=
    F4Pilot.le_centralizerPerfectCore hDp hDX
  obtain ⟨-, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc
  have hAA : A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer (A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨m, hm⟩ := hg ⟨(x : ModGL TwistTag.E6.tag K), mem_subgroupOf.1 hx⟩
    obtain ⟨n, hn⟩ := hg ⟨(y : ModGL TwistTag.E6.tag K), mem_subgroupOf.1 hy⟩
    have h2 : (y : ModGL TwistTag.E6.tag K) * x = x * y := by
      have hx' := congrArg Subtype.val hm
      have hy' := congrArg Subtype.val hn
      simp only [SubgroupClass.coe_zpow] at hx' hy'
      rw [← hx', ← hy', ← zpow_add, ← zpow_add, add_comm]
    exact Subtype.ext h2
  have hPD : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer ({t} : Set G) →
      P ≤ centralizer (modelToG e A : Set G) → P ≤ modelToG e (su6Levi σ) := by
    intro P hPp hPt hPX
    have hOutL := (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1
    have hPL := std_perfect_le hset.standardSetting hOutL htC ht hPp hPt
    exact perfect_le_map_symm_of_centralizer_eq e
      (subgroupOf_le_centralizer_subgroupOf hXD) hAA
      (centralizer_nonsplit_subgroupOf hf hk hK hσ hAJ hA hcyc) hPL hPX hPp
  exact nonempty_swapCover_of_decomposition htt hperf hc hsup hnorm hDp hDt hDE hPD

theorem odd_orderOf_of_card_eq_three {G' : Type*} [Group G'] {H : Subgroup G'}
    (hH : Nat.card H = 3) : ∀ x ∈ H, Odd (orderOf x) := by
  intro x hx
  have h1 : orderOf (⟨x, hx⟩ : H) ∣ 3 := hH ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (show Odd 3 by decide).of_dvd_nat h1

theorem twistedE6TwoSwapRowInput_of_triangle (hT : TwistedE6TwoTriangleInput) :
    TwistedE6TwoSwapRowInput := by
  intro G _ _ L k K _ _ _ hset hk hK σ hσ e t htC ht A hAJ hA hcyc htX Kc hKc hDKK hne hcomm _hZ
    hφ
  have hf : 1 ≤ 1 := le_rfl
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨h₁⟩ := nonempty_swapCover_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc htX hKc
    hDKK hne hcomm hφ
  obtain ⟨n₂, n₃, q, q', h21, h31, h12, h32, h13, h23, hS12, hS13, hS23, hq12, hq13, hq23, hq'12,
    hq'13, hq'23, hqq', hgen⟩ := hT k K hk hK σ hσ A hAJ hA hcyc
  have hDC : su6Levi σ ≤ graphFixedRootGroup TwistTag.E6 K σ := su6Levi_le_graphFixedRootGroup σ
  have hAC : A ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    (centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc).2.2.2
  have hconjC : ∀ (n : graphFixedRootGroup TwistTag.E6 K σ)
      {H : Subgroup (ModGL TwistTag.E6.tag K)},
      H ≤ graphFixedRootGroup TwistTag.E6 K σ →
        H.map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
          graphFixedRootGroup TwistTag.E6 K σ := by
    rintro n H hH _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem n.2 (hH hx)) (inv_mem n.2)
  have hA3 : Nat.card A = 3 := by rw [hA]; norm_num
  have hcardconj : ∀ (n : graphFixedRootGroup TwistTag.E6 K σ),
      Nat.card (modelToG e (A.map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom)) =
        3 := by
    intro n
    rw [Nat.card_congr (modelToGEquivOfLe e (hconjC n hAC)).toEquiv.symm,
      card_map_of_injective (MulAut.conj (n : ModGL TwistTag.E6.tag K)).injective, hA3]
  have hcard1 : Nat.card (modelToG e A) = 3 := by
    rw [Nat.card_congr (modelToGEquivOfLe e hAC).toEquiv.symm, hA3]
  have hνt : ∀ n : graphFixedRootGroup TwistTag.E6 K σ,
      ((e.symm n : L) : G) * t = t * ((e.symm n : L) : G) := fun n =>
    mem_centralizer_iff.1 htC _ (e.symm n).2
  have hcov : ∀ n : graphFixedRootGroup TwistTag.E6 K σ,
      Nonempty (SwapCover t
        (modelToG e (A.map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom))
        (modelToG e ((su6Levi σ).map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom))
        (centralizerPerfectCore
          (modelToG e (A.map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom)))) := by
    intro n
    have hX := modelToG_map_conj e A n
    have hD := modelToG_map_conj e (su6Levi σ) n
    refine ⟨(h₁.conj _ (hνt n)).cast hX.symm hD.symm ?_⟩
    rw [hX]
    exact F4Pilot.map_centralizerPerfectCore (MulAut.conj ((e.symm n : L) : G)) _
  obtain ⟨h₂⟩ := hcov n₂
  obtain ⟨h₃⟩ := hcov n₃
  have hO : ∀ {D' Y : Subgroup (ModGL TwistTag.E6.tag K)},
      D' ≤ graphFixedRootGroup TwistTag.E6 K σ → Y ≤ graphFixedRootGroup TwistTag.E6 K σ →
      modelToG e (perfectCore (D' ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))) =
        perfectCore (modelToG e D' ⊓ centralizer (modelToG e Y : Set G)) :=
    fun hD' hY => modelToG_perfectCore_inf_centralizer e hD' hY
  have hOC : ∀ {D' Y : Subgroup (ModGL TwistTag.E6.tag K)},
      D' ≤ graphFixedRootGroup TwistTag.E6 K σ →
        perfectCore (D' ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K))) ≤
          graphFixedRootGroup TwistTag.E6 K σ :=
    fun hD' => (perfectCore_le _).trans (inf_le_left.trans hD')
  have hS : ∀ {D' Y : Subgroup (ModGL TwistTag.E6.tag K)},
      D' ≤ graphFixedRootGroup TwistTag.E6 K σ → Y ≤ graphFixedRootGroup TwistTag.E6 K σ →
      IsSimpleGroup (perfectCore (D' ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))) →
      IsSimpleGroup (perfectCore (modelToG e D' ⊓ centralizer (modelToG e Y : Set G))) := by
    intro D' Y hD' hY hsimp
    rw [← hO hD' hY]
    exact (modelToGEquivOfLe e (hOC hD')).symm.isSimpleGroup
  have hmem : ∀ {D' Y : Subgroup (ModGL TwistTag.E6.tag K)} {x : ModGL TwistTag.E6.tag K}
      (hD' : D' ≤ graphFixedRootGroup TwistTag.E6 K σ)
      (hY : Y ≤ graphFixedRootGroup TwistTag.E6 K σ)
      (hx : x ∈ perfectCore (D' ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))),
      ((e.symm ⟨x, hOC hD' hx⟩ : L) : G) ∈
        perfectCore (modelToG e D' ⊓ centralizer (modelToG e Y : Set G)) := by
    intro D' Y x hD' hY hx
    rw [← hO hD' hY]
    exact symm_mem_modelToG_of_mem e hx _
  have hD₂C := hconjC n₂ hDC
  have hX₂C := hconjC n₂ hAC
  have hX₃C := hconjC n₃ hAC
  have hqC : q ∈ graphFixedRootGroup TwistTag.E6 K σ := hOC hDC hq12
  have hq'C : q' ∈ graphFixedRootGroup TwistTag.E6 K σ := hOC hDC hq'12
  have hqq'G : ((e.symm ⟨q, hqC⟩ : L) : G) * ((e.symm ⟨q', hq'C⟩ : L) : G) ≠
      ((e.symm ⟨q', hq'C⟩ : L) : G) * ((e.symm ⟨q, hqC⟩ : L) : G) := by
    intro h
    apply hqq'
    have h1 : e.symm (⟨q, hqC⟩ * ⟨q', hq'C⟩) = e.symm (⟨q', hq'C⟩ * ⟨q, hqC⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h2 := congrArg Subtype.val (e.symm.injective h1)
    exact h2
  have hgenG : perfectCore (modelToG e (su6Levi σ) ⊓ centralizer
        (modelToG e (A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) ⊔
      perfectCore (modelToG e (su6Levi σ) ⊓ centralizer
        (modelToG e (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) ⊔
      perfectCore (modelToG e
          ((su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom) ⊓
        centralizer
        (modelToG e (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) =
      L := by
    rw [← hO hDC hX₂C, ← hO hDC hX₃C, ← hO hD₂C hX₃C,
      ← modelToG_sup_of_le e (hOC hDC) (hOC hDC),
      ← modelToG_sup_of_le e (sup_le (hOC hDC) (hOC hDC)) (hOC hD₂C)]
    exact modelToG_eq_of_le e hgen
  have hZD := (neighbour_data_2E6_nonsplit_two hset hk hK hσ e hAJ hA hcyc).2.2.2.2.1
  exact false_of_swapCover_triangle hset (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1 e
    (swapPairExclusion_twistedE6_two (k := k) (by rw [hk]; norm_num) (by rw [hK]; norm_num)
      (fun c => by rw [hσ c]; norm_num))
    ht (inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht) h₁ h₂ h₃
    (modelToG_le e _) (modelToG_le e _) (modelToG_le e _) (modelToG_le e _) (modelToG_le e _)
    (modelToG_le e _) (odd_orderOf_of_card_eq_three hcard1)
    (odd_orderOf_of_card_eq_three (hcardconj n₂)) (odd_orderOf_of_card_eq_three (hcardconj n₃))
    (modelToG_mono e h21) (modelToG_mono e h31) (modelToG_mono e h12) (modelToG_mono e h32)
    (modelToG_mono e h13) (modelToG_mono e h23) hZD
    (hS hDC hX₂C hS12) (hS hDC hX₃C hS13) (hS hD₂C hX₃C hS23)
    (hmem hDC hX₂C hq12) (hmem hDC hX₃C hq13) (hmem hD₂C hX₃C hq23)
    (hmem hDC hX₂C hq'12) (hmem hDC hX₃C hq'13) (hmem hD₂C hX₃C hq'23) hqq'G hgenG

end Cover

end CFSG.SeitzReduction.TwistedE6Pilot
