module

public import CFSG.Quasithin.Background.MS09.D125
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import CFSG.Quasithin.Background.SimsD1Three
public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.EmptyFaithful.S152FinChief

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem conjClosure_le_T (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂) :
    conjClosure V G₂ ≤ T :=
  (conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) v).mp (hVR₂ hv)).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂)

theorem inputD15_holds : EmptyFaithfulMultiple.InputD15 := by
  intro G _ _ G₁ G₂ T V M₂ h
  by_cases hVR₂ : V ≤ pCoreOf 2 G₂
  · by_cases hff : IsFFInt G₁ V h.reduced.2.2.1
    · exact Or.inr (Or.inl ⟨(isFFInt_iff_qInt_le_one _ _ _).mp hff, hff⟩)
    · exact EmptyFaithfulMultiple.d15ConclAS_of_d125' h fun hUe =>
        d125_general (h.minParabolic hff) (conjClosure_le_T h hVR₂) hUe
  · exact Or.inl hVR₂

theorem d125NonsolvableSQTK_holds : D125NonsolvableSQTK := by
  intro G _ _ G₁ G₂ T V M₂ h _ _ hq hVR₂ hUe
  have hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1 := by
    rwa [isFFInt_iff_qInt_le_one]
  exact d125_general (h.minParabolic hnff) (conjClosure_le_T h hVR₂) hUe

theorem d13_one_three_finite (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    qInt G₁ V h.reduced.2.2.1 ≤ 2 ∧
    (qInt G₁ V h.reduced.2.2.1 = 2 →
      c = 2 ∧
      ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A →
        (⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ ∧ ⁅conjClosure V G₂, A⁆ ≠ ⊥) →
        2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
            padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) ∧
          padicValNat 2 ((conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)).relIndex
              (conjClosure V G₂)) =
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
              Subgroup.centralizer (conjClosure V G₂ : Set G)).relIndex (A ⊓ pCoreOf 2 G₂)) ∧
          (∀ g ∈ G₂, ⁅V.map (MulAut.conj g⁻¹).toMonoidHom, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
            2 * padicValNat 2 ((A ⊓ pCoreOf 2 G₂ ⊓
                Subgroup.centralizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
                  (A ⊓ pCoreOf 2 G₂)) =
              padicValNat 2 ((V.map (MulAut.conj g⁻¹).toMonoidHom ⊓
                Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)).relIndex
                  (V.map (MulAut.conj g⁻¹).toMonoidHom))) ∧
          (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
            padicValNat 2 ((A ⊓ pCoreOf 2 G₂).relIndex A) =
              padicValNat 2 ((SimsD1.Three.secFix A N L).relIndex N)) ∧
          conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
            conjClosure V G₂ ⊓
              Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) := by
  have hD125 : D15Proof.D125 G₂ T (conjClosure V G₂) :=
    d125_general (h.minParabolic hnff) (conjClosure_le_T h hVR₂)
      (D15Proof.isElemAbelian_conjClosure h hnff hVR₂)
  refine ⟨D15Proof.qInt_le_two h hnff hVR₂ hD125 hc hser, fun hq2 => ?_⟩
  have hq2' : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1 := hq2 ▸ le_rfl
  refine ⟨Ch3y.c_eq_two h hnff hVR₂ hD125 hq2' hc hser, fun A hA hAq => ?_⟩
  exact (SimsD1.Three.three_eq h hnff hVR₂ hD125 hq2 hc hser hA hAq.1 hAq.2).2

theorem inf_centralizerMod_le {H T M U L N P : Subgroup G} (hmp : MinParabolic H T M)
    (hUT : U ≤ T) (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) (hPH : P ≤ H)
    (hP2 : IsPGroup 2 P) : P ⊓ centralizerMod L H N ≤ pCoreOf 2 H := by
  obtain ⟨T', hT', hPT'⟩ := B6.exists_isSylowTwoOf_ge hP2 hPH
  obtain ⟨g, hg, rfl⟩ := B6.isSylowTwoOf_exists_conj hmp.isSylow hT'
  have hM := (MinParabolic.isUniqueMaxSub hmp).conjSub g
  rw [B6.conjSub_eq_self (Subgroup.le_normalizer hg)] at hM
  have hC : centralizerMod L H N ≤ kerIn (B6.conjSub g M) H := by
    intro x hx b hb
    have hk := centralizerMod_le_kerIn hmp hUT hstep hnc hx (g⁻¹ * b) (H.mul_mem (H.inv_mem hg) hb)
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hk
  intro x hx
  exact hM.inf_kerIn_le hT' le_rfl ⟨hPT' hx.1, hC hx.2⟩

theorem relIndex_mul_card_le_of_minParabolic {H T M W P : Subgroup G} (hmp : MinParabolic H T M)
    (hWE : IsElemAbelian 2 W) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hWR : W ≤ pCoreOf 2 H) (hRW : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G))
    (hCM : H ⊓ Subgroup.centralizer (W : Set G) ≤ M) (hPH : P ≤ H) (hP2 : IsPGroup 2 P)
    (hquad : ⁅⁅W, P⁆, P⁆ = ⊥) :
    (P ⊓ Subgroup.centralizer (W : Set G)).relIndex P *
      Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) ≤ Nat.card W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWT : W ≤ T := hWR.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow)
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := W) W
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHW hg) x).mp hx⟩
  have hc : 1 ≤ c := by
    by_contra hc0
    have hW2 : IsPGroup 2 W := (pCoreOf_isPGroup 2 H).to_le hWR
    have hcomm := D14.commutator_eq_bot_of_zero hW2 hser (by omega)
    have hres : twoResidual H ≤ H ⊓ Subgroup.centralizer (W : Set G) := by
      refine le_inf (twoResidual_le H) ?_
      rw [F6.twoResidual_eq_oTwoUpper H]
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact Subgroup.le_centralizer_iff.mp hcomm
    apply not_le_of_gt hmp.maximal.1
    rw [← sup_twoResidual_eq hmp.isSylow]
    exact sup_le hmp.le (hres.trans hCM)
  obtain ⟨L, N, hstep, hnc, -⟩ := S152Fin.exists_noncentral_of_series hser hc
  have hNW : N ≤ W := hstep.1.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hWH : W ≤ H := hWT.trans hmp.isSylow.1
  have hquadN : ⁅⁅N, P⁆, P⁆ ≤ L := by
    have : ⁅⁅N, P⁆, P⁆ ≤ ⁅⁅W, P⁆, P⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hNW le_rfl) le_rfl
    rw [hquad] at this
    exact this.trans bot_le
  have h1 := relIndex_le_of_minParabolic hmp hWT hWE hstep hnc hPH hP2 hquadN
  have hcP : centralizerMod L P N = P ⊓ Subgroup.centralizer (W : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.1, hRW (inf_centralizerMod_le hmp hWT hstep hnc hPH hP2
      ⟨hx.1, hPH hx.1, hx.2.1, hx.2.2⟩)⟩) (fun x hx => ⟨hx.1, hHL (hPH hx.1), fun n hn => ?_⟩)
    have hxn : x * n = n * x := (Subgroup.mem_centralizer_iff.mp hx.2 n (hNW hn)).symm
    rw [hxn, mul_inv_cancel_right, mul_inv_cancel]
    exact L.one_mem
  have hle : N ⊓ Subgroup.centralizer (P : Set G) ≤ centralizerMod L N P := fun x hx =>
    ⟨hx.1, hHL (hWH (hNW hx.1)), fun p hp => by
      have hxp : x * p = p * x := (Subgroup.mem_centralizer_iff.mp hx.2 p hp).symm
      rw [hxp, mul_inv_cancel_right, mul_inv_cancel]
      exact L.one_mem⟩
  have h2 : (centralizerMod L N P).relIndex N ≤
      (Subgroup.centralizer (P : Set G)).relIndex W := by
    calc (centralizerMod L N P).relIndex N
        ≤ (N ⊓ Subgroup.centralizer (P : Set G)).relIndex N :=
          Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
      _ = (Subgroup.centralizer (P : Set G)).relIndex N := Subgroup.inf_relIndex_left _ _
      _ ≤ (Subgroup.centralizer (P : Set G)).relIndex W :=
          Subgroup.relIndex_le_of_le_right hNW Subgroup.index_ne_zero_of_finite
  have h3 := Subgroup.relIndex_mul_card (Subgroup.centralizer (P : Set G)) W
  rw [inf_comm] at h3
  rw [← hcP]
  calc (centralizerMod L P N).relIndex P * Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G))
      ≤ (Subgroup.centralizer (P : Set G)).relIndex W *
          Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) :=
        Nat.mul_le_mul_right _ (h1.trans h2)
    _ = Nat.card W := h3

theorem conj_comm_eq_of_isQuadratic {S W : Subgroup G} (hWE : IsElemAbelian 2 W)
    (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hq : @IsQuadratic ↥W (commGroupOfElemAbelian hWE) (autOn S W)) {s₁ s₂ w : G}
    (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (hw : w ∈ W) :
    s₂ * (s₁ * w * s₁⁻¹ * w⁻¹) * s₂⁻¹ = s₁ * w * s₁⁻¹ * w⁻¹ := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWE
  set a₁ := conjAct W ⟨s₁, hSW hs₁⟩ with ha₁
  set a₂ := conjAct W ⟨s₂, hSW hs₂⟩ with ha₂
  have hm₁ : a₁ ∈ autOn S W := ⟨⟨s₁, hSW hs₁⟩, Subgroup.mem_subgroupOf.mpr hs₁, rfl⟩
  have hm₂ : a₂ ∈ autOn S W := ⟨⟨s₂, hSW hs₂⟩, Subgroup.mem_subgroupOf.mpr hs₂, rfl⟩
  have hx : a₁ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹ ∈ commV (autOn S W) :=
    Subgroup.subset_closure ⟨a₁, hm₁, ⟨w, hw⟩, rfl⟩
  have hfix := congrArg Subtype.val (hq hx a₂ hm₂)
  rw [ha₂, conjAct_apply_coe'] at hfix
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha₁, conjAct_apply_coe'] at hfix
  exact hfix

theorem commutator_commutator_eq_bot_of_isQuadratic {S W : Subgroup G}
    (hWE : IsElemAbelian 2 W) (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hq : @IsQuadratic ↥W (commGroupOfElemAbelian hWE) (autOn S W)) : ⁅⁅W, S⁆, S⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
  intro w hw s hs
  rw [Subgroup.mem_centralizer_iff]
  intro s' hs'
  have h := conj_comm_eq_of_isQuadratic hWE hSW hq hs hs' hw
  have e : ⁅w, s⁆ = (s * w * s⁻¹ * w⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  have h' : s' * (s * w * s⁻¹ * w⁻¹)⁻¹ * s'⁻¹ = (s * w * s⁻¹ * w⁻¹)⁻¹ := by
    calc s' * (s * w * s⁻¹ * w⁻¹)⁻¹ * s'⁻¹ = (s' * (s * w * s⁻¹ * w⁻¹) * s'⁻¹)⁻¹ := by group
      _ = (s * w * s⁻¹ * w⁻¹)⁻¹ := by rw [h]
  calc s' * (s * w * s⁻¹ * w⁻¹)⁻¹ = s' * (s * w * s⁻¹ * w⁻¹)⁻¹ * s'⁻¹ * s' := by group
    _ = (s * w * s⁻¹ * w⁻¹)⁻¹ * s' := by rw [h']

theorem one_le_qInt_of_minParabolic {H T M W : Subgroup G} (hmp : MinParabolic H T M)
    (hWE : IsElemAbelian 2 W) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hWR : W ≤ pCoreOf 2 H) (hRW : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G))
    (hCM : H ⊓ Subgroup.centralizer (W : Set G) ≤ M) : (1 : WithTop ℚ) ≤ qInt H W hWE := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWE
  have hsq' : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (hWE.2 v v.2)
  have key : ((1 : ℚ) : WithTop ℚ) ≤ kq (autOn H W) 2 := le_kq_iff.mpr fun A hA hq => by
    by_contra hlt
    push Not at hlt
    rw [rAV_lt_one_iff hsq' hA] at hlt
    set K : Subgroup G := H ⊓ (A.comap (conjAct W)).map (Subgroup.normalizer (W : Set G)).subtype
      with hK
    have hKN : K ≤ Subgroup.normalizer (W : Set G) := inf_le_left.trans hHW
    have hKA : autOn K W = A := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        obtain ⟨m, hm, hmn⟩ := (Subgroup.mem_subgroupOf.mp hn).2
        have : m = n := Subtype.ext hmn
        rw [← this]
        exact hm
      · intro a ha
        obtain ⟨n, hn, rfl⟩ := hA.1 ha
        exact ⟨n, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hn, n, ha, rfl⟩, rfl⟩
    obtain ⟨P, hP, -⟩ := B6.exists_isSylowTwoOf_ge (IsPGroup.of_bot (p := 2) (G := G))
      (bot_le : ⊥ ≤ K)
    have hA2 : IsPGroup 2 ↥A := hA.isElemAbelian2.isPGroup
    have hPA : autOn P W = A := by
      have hsyl := AutOn.isSylowTwoOf_autOn hP hKN
      rw [hKA] at hsyl
      exact (G64.IsSylowTwoOf.eq_of_le hsyl hsyl.1 le_rfl hA2).symm
    have hPN : P ≤ Subgroup.normalizer (W : Set G) := hP.1.trans hKN
    have hPH : P ≤ H := hP.1.trans inf_le_left
    have hqP : IsQuadratic (autOn P W) := by
      rw [hPA, isQuadratic_iff_commSeries_two]
      exact hq
    have hbound := relIndex_mul_card_le_of_minParabolic hmp hWE hHW hWR hRW hCM hPH hP.2.1
      (commutator_commutator_eq_bot_of_isQuadratic hWE hPN hqP)
    rw [← hPA, AutOn.card_autOn_eq_relIndex hPN, card_fixV_autOn_eq hWE hPN] at hlt
    exact absurd hbound (not_le.mpr hlt)
  rw [WithTop.coe_one] at key
  exact key

end CFSG.Quasithin.MS09

end
