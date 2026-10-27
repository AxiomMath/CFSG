module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}
open CFSG.ComponentClassification.FixedCommutingProduct
variable {S : Type} [Group S] [Finite S] {f : ℕ}

theorem suzuki_twoAut_le_inner (hSzO : Sz.SzOutOdd)
    (hSz : CFSG.Blueprint.SuzukiModel S 2 f)
    {W : Subgroup (MulAut S)} (hW2 : IsPGroup 2 W) :
    W ≤ (MulAut.conj : S →* MulAut S).range :=
  CFSG.RankThree.PartOne.isPGroup_two_le_inner_of_odd_outer (hSzO hSz) W hW2

theorem suzuki_borel_bridge (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd)
    (hSz : CFSG.Blueprint.SuzukiModel S 2 f)
    (hcenter : Subgroup.center S = ⊥)
    {σ : MulAut S} (hperf : Group.IsPerfect ↥(fixedSubgroup σ))
    (hne : fixedSubgroup σ ≠ ⊥)
    {W : Subgroup (MulAut S)} (hW2 : IsPGroup 2 W)
    (hCW : ∀ c ∈ fixedSubgroup σ, ∀ w ∈ W,
      MulAut.conj c * w * (MulAut.conj c)⁻¹ ∈ W) :
    W = ⊥ := by
  classical
  let conj : S →* MulAut S := MulAut.conj
  have hconj_inj : Function.Injective conj := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut S => f x) hab
      rw [MulAut.conj_apply, MulAut.conj_apply] at hx
      have hx' : (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = x := by
        calc (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹
            = b⁻¹ * (a * x * a⁻¹) * b := by group
          _ = b⁻¹ * (b * x * b⁻¹) * b := by rw [hx]
          _ = x := by group
      have hzx : (b⁻¹ * a) * x = x * (b⁻¹ * a) := by
        calc (b⁻¹ * a) * x = ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by group
          _ = x * (b⁻¹ * a) := by rw [hx']
      exact hzx.symm
    have h1 : b⁻¹ * a = 1 := by simpa [hcenter] using hc
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  have hWin : W ≤ conj.range := suzuki_twoAut_le_inner hSzO hSz hW2
  have hWle : W ≤ (MulAut.conj : S →* MulAut S).range := hWin
  by_contra hWne
  let R : Subgroup S := W.comap conj
  have hRmap : R.map conj = W := Subgroup.map_comap_eq_self hWle
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hWne
    calc W = R.map conj := hRmap.symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  have hR2 : IsPGroup 2 R := by
    have hcard : Nat.card R = Nat.card W := by
      rw [← hRmap]
      exact (Subgroup.card_map_of_injective (K := R) hconj_inj).symm
    obtain ⟨n, hn⟩ := hW2.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [hcard, hn])
  have hCNR : fixedSubgroup σ ≤ Subgroup.normalizer (R : Set S) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      have hconj : conj (c * x * c⁻¹) = conj c * conj x * (conj c)⁻¹ := by
        simp only [conj, map_mul, map_inv]
      rw [hconj]
      exact hCW c hc (conj x) hx
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      have h := hCW c⁻¹ ((fixedSubgroup σ).inv_mem hc) (conj (c * x * c⁻¹)) hx
      have h' : (conj c)⁻¹ * conj (c * x * c⁻¹) * conj c ∈ W := by
        simpa [conj] using h
      have hconj : (conj c)⁻¹ * conj (c * x * c⁻¹) * conj c = conj x := by
        simp only [conj, map_mul, map_inv]
        group
      rwa [hconj] at h' 
  rcases (hSzB hSz R hR2 hRne) with ⟨T, hNT, hsol⟩
  have hCNT : fixedSubgroup σ ≤ Subgroup.normalizer ((T : Subgroup S) : Set S) :=
    hCNR.trans hNT
  haveI : Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup S) : Set S)) := hsol
  haveI : Group.IsSolvable ↥(fixedSubgroup σ) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hCNT) (Subgroup.inclusion_injective hCNT)
  haveI : Group.IsPerfect ↥(fixedSubgroup σ) := hperf
  haveI : Nontrivial ↥(fixedSubgroup σ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥(fixedSubgroup σ) inferInstance

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem componentsImage_isPGroup (e : G) :
    IsPGroup 2 (componentsImage (D := D) e) := by
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let W : Subgroup G := H ⊓ Q
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hWQ : W ≤ Q := inf_le_right
  have hWQ2 : IsPGroup 2 (W.subgroupOf Q) := hQ2.to_subgroup _
  have hW2G : IsPGroup 2 W := hWQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hWQ)
  have hW2H : IsPGroup 2 (W.subgroupOf H) :=
    hW2G.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ H)).symm
  let π : H →* componentsQuot e :=
    QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H)
  simpa [componentsImage, H, Q, W, π] using IsPGroup.map hW2H π

theorem exists_thetaComponent_map_eq_and_dvd (e : G) {J : Subgroup (componentsQuot e)}
    (hJ : CFSG.IsComponent J) (h3J : 3 ∣ Nat.card J) :
    ∃ L ∈ thetaComponentsAt 3 e,
      (L.subgroupOf (Subgroup.centralizer ({e} : Set G))).map
          (QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
            ↥(Subgroup.centralizer ({e} : Set G)))) = J ∧
        3 ∣ Nat.card L := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let π : H →* componentsQuot e :=
    QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H)
  let P : Subgroup H :=
    inSubgroup perfectResidual (Subgroup.comap π J)
  obtain ⟨hPtheta, hPmap⟩ :=
    perfectResidual_comap_mem_thetaComponents (p := 3) Nat.prime_three hJ
  let L : Subgroup G := P.map H.subtype
  have hLH : L ≤ H := Subgroup.map_subtype_le P
  have hLmem : L ∈ thetaComponentsAt 3 e := ⟨P, hPtheta, rfl⟩
  have hLsub : L.subgroupOf H = P := by
    rw [show L = P.map H.subtype from rfl, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hLmap : (L.subgroupOf H).map π = J := by
    rw [hLsub]
    exact hPmap
  have hcardL : Nat.card L = Nat.card P :=
    Subgroup.card_map_of_injective (K := P) H.subtype_injective
  have hdvd : 3 ∣ Nat.card P := by
    have h1 : 3 ∣ Nat.card J := h3J
    rw [← hLmap] at h1
    have hcardSub : Nat.card (L.subgroupOf H) = Nat.card P := by rw [hLsub]
    exact h1.trans (hcardSub ▸ Subgroup.card_map_dvd (L.subgroupOf H) π)
  exact ⟨L, hLmem, hLmap, by rwa [hcardL]⟩

theorem not_three_dvd_card_of_nontrivial
    (e : G) (c : Ctx82E3 D) (P : Subgroup G)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J) :
    ¬ 3 ∣ Nat.card J := by
  intro h3
  obtain ⟨L, hL, hLmap, h3L⟩ := exists_thetaComponent_map_eq_and_dvd e hJ h3
  exact hntriv ⟨L, hL, hLmap, hZ3 L hL h3L⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub)
variable {X : Type} [Group X] [Finite X]

theorem fixedSubgroup_centerQuotient_le_map {J : Type} [Group J] [Finite J]
    (α : MulAut J) (hα3 : α ^ 3 = 1)
    (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center J)) :
    fixedSubgroup (onCenterQuotient α) ≤
      (fixedSubgroup α).map (QuotientGroup.mk' (Subgroup.center J)) := by
  have h := CFSG.GH74.GLS.Stage2.Bender.Thm1.fixSub_onCenterQuotient_le_map
    (Q := J) α Nat.prime_three hα3 h3Z
  simpa [fixedSubgroup, fixSub, onCenterQuotient] using h

theorem fixedSubgroup_normalizes_action_image
    {X : Type} [Group X] [Finite X] {J W : Subgroup X}
    (hWN : W ≤ Subgroup.normalizer (J : Set X))
    {z : X} (hzN : z ∈ Subgroup.normalizer (J : Set X))
    (hα3 : Subgroup.normalizerMonoidHom J ⟨z, hzN⟩ ^ 3 = 1)
    (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (hCWN : fixedSubgroup (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≤
      (Subgroup.normalizer (W : Set X)).comap J.subtype) :
    ∀ c ∈ fixedSubgroup (centerQuotientHom J (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩)),
      ∀ w ∈ (W.subgroupOf (Subgroup.normalizer (J : Set X))).map
        ((centerQuotientHom J).comp (Subgroup.normalizerMonoidHom J)),
        MulAut.conj c * w * (MulAut.conj c)⁻¹ ∈
          (W.subgroupOf (Subgroup.normalizer (J : Set X))).map
            ((centerQuotientHom J).comp (Subgroup.normalizerMonoidHom J)) := by
  classical
  let N : Subgroup X := Subgroup.normalizer (J : Set X)
  let α : MulAut J := Subgroup.normalizerMonoidHom J ⟨z, hzN⟩
  let Ψ : N →* MulAut (J ⧸ Subgroup.center J) :=
    (centerQuotientHom J).comp (Subgroup.normalizerMonoidHom J)
  intro c hc w hw
  have hc' : c ∈ fixedSubgroup (onCenterQuotient α) := by
    simpa [centerQuotientHom, α] using hc
  obtain ⟨j, hjfix, hjc⟩ := fixedSubgroup_centerQuotient_le_map α hα3 h3Z hc' 
  have hjW : (j : X) ∈ Subgroup.normalizer (W : Set X) := hCWN hjfix
  obtain ⟨wN, hwN, rfl⟩ := Subgroup.mem_map.mp hw
  have hwW : (wN : X) ∈ W := Subgroup.mem_subgroupOf.mp hwN
  let jN : N := ⟨j, Subgroup.le_normalizer j.2⟩
  have hΨj : Ψ jN = MulAut.conj c := by
    rw [← hjc]
    have hnm : Subgroup.normalizerMonoidHom J jN = MulAut.conj j := by
      ext k
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp [jN, MulAut.conj_apply]
    change centerQuotientHom J (Subgroup.normalizerMonoidHom J jN) = _
    rw [hnm, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
  let jwj : N := jN * wN * jN⁻¹
  have hjwjW : (jwj : X) ∈ W := by
    change (j : X) * (wN : X) * (j : X)⁻¹ ∈ W
    exact (Subgroup.mem_normalizer_iff.mp hjW (wN : X)).mp hwW
  have hmem : Ψ jwj ∈ (W.subgroupOf N).map Ψ :=
    Subgroup.mem_map_of_mem Ψ (Subgroup.mem_subgroupOf.mpr hjwjW)
  have heq : MulAut.conj c * Ψ wN * (MulAut.conj c)⁻¹ = Ψ jwj := by
    calc MulAut.conj c * Ψ wN * (MulAut.conj c)⁻¹
        = Ψ jN * Ψ wN * (Ψ jN)⁻¹ := by rw [← hΨj]
      _ = Ψ (jN * wN * jN⁻¹) := by simp only [map_mul, map_inv]
      _ = Ψ jwj := rfl
  rw [heq]
  exact hmem

theorem suzuki_component_centralizer_of_action
    {X : Type} [Group X] [Finite X]
    {J W : Subgroup X} (hJ : CFSG.IsComponent J) (hJ3 : ¬ 3 ∣ Nat.card J)
    (hW2 : IsPGroup 2 W) (hWN : W ≤ Subgroup.normalizer (J : Set X))
    {z : X} (hzN : z ∈ Subgroup.normalizer (J : Set X)) (hz3 : z ^ 3 = 1)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) {f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f) (hf : 3 < f)
    (hntriv : centerQuotientHom J (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≠ 1)
    (hCWN : fixedSubgroup (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≤
      (Subgroup.normalizer (W : Set X)).comap J.subtype) :
    W ≤ Subgroup.centralizer (J : Set X) := by
  classical
  let N : Subgroup X := Subgroup.normalizer (J : Set X)
  let Ψ : N →* MulAut (J ⧸ Subgroup.center J) :=
    (centerQuotientHom J).comp (Subgroup.normalizerMonoidHom J)
  let α : MulAut J := Subgroup.normalizerMonoidHom J ⟨z, hzN⟩
  let σ : MulAut (J ⧸ Subgroup.center J) := Ψ ⟨z, hzN⟩
  have hα3 : α ^ 3 = 1 := by
    rw [show α = Subgroup.normalizerMonoidHom J ⟨z, hzN⟩ from rfl, ← map_pow]
    have hzN3 : (⟨z, hzN⟩ : N) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hz3
    rw [hzN3, map_one]
  have hσ3 : σ ^ 3 = 1 := by
    change (centerQuotientHom J α) ^ 3 = 1
    rw [← map_pow, hα3, map_one]
  have hσne : σ ≠ 1 := hntriv
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσne
  obtain ⟨hperf, h2fix, -⟩ := hSzF hSz hf σ hσord
  have hne : fixedSubgroup σ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2fix
    omega
  haveI : Group.IsPerfect ↥J := hJ.1.1
  have hcenterS : Subgroup.center (J ⧸ Subgroup.center J) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot ↥J
  let WN : Subgroup N := W.subgroupOf N
  have hWN2 : IsPGroup 2 WN :=
    hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWN).symm
  let W' : Subgroup (MulAut (J ⧸ Subgroup.center J)) := WN.map Ψ
  have hW'2 : IsPGroup 2 W' := hWN2.map Ψ
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center J) := by
    intro h3c
    have hdvd : Nat.card (Subgroup.center J) ∣ Nat.card ↥J := by
      have h := Subgroup.card_dvd_of_le (H := Subgroup.center J) (K := ⊤) le_top
      rwa [Subgroup.card_top] at h
    exact hJ3 (h3c.trans hdvd)
  have hCW' : ∀ c ∈ fixedSubgroup σ, ∀ w ∈ W',
      MulAut.conj c * w * (MulAut.conj c)⁻¹ ∈ W' := by
    intro c hc w hw
    exact fixedSubgroup_normalizes_action_image hWN hzN hα3 h3Z hCWN c hc w hw
  have hW'bot : W' = ⊥ :=
    suzuki_borel_bridge hSzB hSzO hSz hcenterS hperf hne hW'2 hCW'
  have hΨtriv : ∀ w : WN, Ψ w = 1 := by
    intro w
    have hmem : Ψ w ∈ W' := Subgroup.mem_map_of_mem Ψ w.2
    rw [hW'bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  let wN : N := ⟨w, hWN hw⟩
  have hαw : Subgroup.normalizerMonoidHom J wN = 1 := by
    apply centerQuotientHom_injective J
    have h := hΨtriv (⟨wN, Subgroup.mem_subgroupOf.mpr hw⟩ : WN)
    simpa [Ψ] using h
  have hval : w * j * w⁻¹ = j := by
    have h := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : X)) hαw
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    simpa using h
  calc j * w = (w * j * w⁻¹) * w := by rw [hval]
    _ = w * j := by group

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def SuzukiComponentBridgeData (c : Ctx82E3 D) (P : Subgroup G) (e : G)
    (J : Subgroup (componentsQuot e)) : Prop :=
  ∃ f : ℕ, 3 < f ∧
  ∃ _hSz : CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f,
  ∃ (z : componentsQuot e) (hzN : z ∈ Subgroup.normalizer (J : Set _)),
    z ^ 3 = 1 ∧
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J
        (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≠ 1 ∧
    componentsImage (D := D) e ≤ Subgroup.normalizer (J : Set _) ∧
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
        (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≤
      (Subgroup.normalizer
        ((componentsImage (D := D) e : Subgroup (componentsQuot e)) : Set _)).comap
        J.subtype

@[expose] def SuzukiComponentStepInput (c : Ctx82E3 D) (P : Subgroup G) (e : G) : Prop :=
  ∀ J : Subgroup (componentsQuot e), CFSG.IsComponent J →
    ¬ TrivialZComponentAction (D := D) c P e J →
      SuzukiComponentBridgeData (D := D) c P e J ∨
        componentsImage (D := D) e ≤ Subgroup.centralizer (J : Set _)

theorem suzukiComponentStep_holds_conditional
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hInput : SuzukiComponentStepInput (D := D) c P e) :
    SuzukiComponentStep hPSz hSzB hSzO hSzF c hON h7 P hNZ e hP3 hZ3 he he3 heZ := by
  intro J hJ hntriv
  rcases hInput J hJ hntriv with ⟨f, hf, hSz, z, hzN, hz3, hntriv', hWnorm, hCWN⟩ | h
  · have hJ3 : ¬ 3 ∣ Nat.card J :=
      not_three_dvd_card_of_nontrivial e c P hZ3 hJ hntriv
    exact suzuki_component_centralizer_of_action hJ hJ3 (componentsImage_isPGroup e) hWnorm
      hzN hz3 hSzB hSzO hSzF hSz hf hntriv' hCWN
  · exact h

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
