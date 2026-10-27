module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Bridge
public import CFSG.LocalAnalysis.WeakClosure81.InFMulEquiv
public import CFSG.GroupTheory.AutSubJoin
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InF InFFor)
open scoped commutatorElement Pointwise
open CFSG.GroupTheory (iSup_autSub_eq ker_resHomOn_eq)

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def W4Lem4_16b : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ (Δ : Set (Subgroup (MulAut W))) (k : ℕ),
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      Δ.Finite →
      (∀ H ∈ Δ, H ≤ Y ∧ T ≤ H) →
      (⨆ H ∈ Δ, H) = Y →
      fIndexSum Δ ≤ (k : ℕ∞) →
      fixV T ≠ fixV Y → bParam L Y ≤ k

theorem fIndex_eq_of_bar2_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {H : Subgroup G} {H' : Subgroup G'}
    (e : CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H ≃*
      CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H') :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex H' =
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex H := by
  have hset : {i : ℕ | InFSq i H'} = {i : ℕ | InFSq i H} := by
    ext i
    simpa only [Set.mem_setOf_eq] using (inFSq_iff_bar2_inF_mulEquiv e i).symm
  unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex
  rw [hset]

theorem fIndexSum_image_le {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {Δ : Set (Subgroup G)} (hfin : Δ.Finite) (f : Subgroup G → Subgroup G')
    (hf : ∀ H ∈ Δ, CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex (f H) ≤
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex H) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexSum (f '' Δ) ≤
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexSum Δ := by
  classical
  have hfin' : (f '' Δ).Finite := hfin.image f
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexSum,
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndexSum,
    finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin']
  have hex : ∀ K ∈ hfin'.toFinset, ∃ H : Subgroup G, H ∈ Δ ∧ f H = K := by
    intro K hK
    obtain ⟨H, hH, hHK⟩ := (Set.Finite.mem_toFinset hfin').mp hK
    exact ⟨H, hH, hHK⟩
  let g : Subgroup G' → Subgroup G := fun K =>
    if h : K ∈ hfin'.toFinset then Classical.choose (hex K h) else ⊥
  have hg_mem : ∀ K ∈ hfin'.toFinset, g K ∈ Δ := by
    intro K hK
    simp only [g, dif_pos hK]
    exact (Classical.choose_spec (hex K hK)).1
  have hg_eq : ∀ K ∈ hfin'.toFinset, f (g K) = K := by
    intro K hK
    simp only [g, dif_pos hK]
    exact (Classical.choose_spec (hex K hK)).2
  have hinj : Set.InjOn g ↑hfin'.toFinset := by
    intro K₁ hK₁ K₂ hK₂ hgg
    rw [← hg_eq K₁ hK₁, ← hg_eq K₂ hK₂, hgg]
  have hsub : Finset.image g hfin'.toFinset ⊆ hfin.toFinset := by
    intro K hK
    obtain ⟨K₀, hK₀, rfl⟩ := Finset.mem_image.mp hK
    exact (Set.Finite.mem_toFinset hfin).mpr (hg_mem K₀ hK₀)
  calc ∑ K ∈ hfin'.toFinset,
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex K
      = ∑ K ∈ hfin'.toFinset,
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex (f (g K)) := by
        refine Finset.sum_congr rfl fun K hK => ?_
        rw [hg_eq K hK]
    _ ≤ ∑ K ∈ hfin'.toFinset, CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex (g K) := by
        refine Finset.sum_le_sum fun K hK => ?_
        exact hf (g K) (hg_mem K hK)
    _ = ∑ H ∈ Finset.image g hfin'.toFinset,
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex H := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ H ∈ hfin.toFinset, CFSG.LocalAnalysis.UniquenessCase.PartTwo.fIndex H := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i _ _
        exact zero_le

theorem bParam_le_aParam {X Y : Subgroup (MulAut W)} : bParam X Y ≤ E3.aParam Y := by
  rcases Nat.eq_zero_or_pos (bParam X Y) with h | hpos
  · exact h ▸ Nat.zero_le _
  · obtain ⟨A, hA, -⟩ := bParam_spec X Y hpos
    exact E3.le_aParam_of_mem_aSet hpos hA

theorem bar2_autSub_mulEquiv {W : Type} [CommGroup W] [Finite W]
    {Y H : Subgroup (MulAut W)} {U : Subgroup W}
    (hHY : H ≤ Y) (hstab : Y ≤ stabSub U)
    (hker : Y ⊓ centSub U = pCoreOf 2 Y) (hQH : pCoreOf 2 Y ≤ H) :
    Nonempty (Bar2 H ≃* Bar2 (autSub H U)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (MulAut W) := pCoreOf 2 Y with hQ
  have hQY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hkerQ : Y ⊓ centSub U = Q := by rw [hQ]; exact hker
  have hQcent : Q ≤ centSub U := by rw [← hkerQ]; exact inf_le_right
  let φ : ↥H →* ↥(autSub H U) :=
    ((resHomOn U hstab).comp (Subgroup.inclusion hHY)).codRestrict (autSub H U) (by
      intro x
      have hx : (Subgroup.inclusion hHY x : ↥Y) ∈ H.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr x.2
      have h := Subgroup.mem_map_of_mem (resHomOn U hstab) hx
      rwa [← autSub_eq_map_resHomOn hHY hstab] at h)
  have hφsurj : Function.Surjective φ := by
    intro z
    have hz : (z : MulAut U) ∈ (H.subgroupOf Y).map (resHomOn U hstab) := by
      rw [← autSub_eq_map_resHomOn hHY hstab]
      exact z.2
    obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp hz
    refine ⟨⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  have hφker : φ.ker = Q.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (resHomOn U hstab) (Subgroup.inclusion hHY x) = 1 := by
        have h := congrArg Subtype.val hx
        simpa [φ] using h
      have h2 : Subgroup.inclusion hHY x ∈ (resHomOn U hstab).ker :=
        MonoidHom.mem_ker.mpr h1
      rw [ker_resHomOn_eq hstab, Subgroup.mem_subgroupOf, hkerQ] at h2
      exact Subgroup.mem_subgroupOf.mpr h2
    · intro hx
      have hxQ : (x : MulAut W) ∈ Q := Subgroup.mem_subgroupOf.mp hx
      have h1 : (resHomOn U hstab) (Subgroup.inclusion hHY x) = 1 := by
        rw [← MonoidHom.mem_ker, ker_resHomOn_eq hstab, Subgroup.mem_subgroupOf, hkerQ]
        exact hxQ
      apply Subtype.ext
      exact h1
  have hφkerP : IsPGroup 2 φ.ker := by
    rw [hφker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hPp : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have hPnormal : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  have hPmapLe : (CFSG.pCore 2 ↥H).map φ ≤ CFSG.pCore 2 ↥(autSub H U) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (hPnormal.map φ hφsurj) (hPp.map φ)
  let ψ : ↥H →* Bar2 (autSub H U) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(autSub H U))).comp φ
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp hφsurj
  have hψker_le : ψ.ker ≤ CFSG.pCore 2 ↥H := by
    intro x hx
    have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
    have hx2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(autSub H U)) (φ x) = 1 := hx1
    have hx3 : φ x ∈ CFSG.pCore 2 ↥(autSub H U) := by
      rw [QuotientGroup.mk'_apply] at hx2
      exact (QuotientGroup.eq_one_iff (φ x)).mp hx2
    have hxR : x ∈ (CFSG.pCore 2 ↥(autSub H U)).comap φ := by
      rw [Subgroup.mem_comap]
      exact hx3
    exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
      (Subgroup.Normal.comap (CFSG.pCore_normal (p := 2) (G := ↥(autSub H U))) φ)
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥(autSub H U))).comap_of_ker_isPGroup φ
        hφkerP) hxR
  have hPle_ker : CFSG.pCore 2 ↥H ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (CFSG.pCore 2 ↥(autSub H U)) (φ x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hPmapLe (Subgroup.mem_map_of_mem φ hx)
  have hψker : ψ.ker = CFSG.pCore 2 ↥H := le_antisymm hψker_le hPle_ker
  have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψsurj
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans
      ((MulEquiv.subgroupCongr hψrange).trans Subgroup.topEquiv))⟩

theorem fIndex_autSub_eq {W : Type} [CommGroup W] [Finite W]
    {Y H : Subgroup (MulAut W)} {U : Subgroup W}
    (hHY : H ≤ Y) (hstab : Y ≤ stabSub U)
    (hker : Y ⊓ centSub U = pCoreOf 2 Y) (hQH : pCoreOf 2 Y ≤ H) :
    fIndex (autSub H U) = fIndex H := by
  obtain ⟨e⟩ := bar2_autSub_mulEquiv hHY hstab hker hQH
  exact fIndex_eq_of_bar2_mulEquiv e

theorem w4Lem4_16b_of_w4Lem4_16 (h : W4Lem4_16) : W4Lem4_16b := by
  intro W _ _ hw Y L T Δ k hLY hTY hLT hcomp hsyl hΔfin hΔT hgen hkSum hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup W := fixV (pCoreOf 2 Y)
  let Lb : Subgroup (MulAut ↥U) := autSub L U
  let Tb : Subgroup (MulAut ↥U) := autSub T U
  let Yb : Subgroup (MulAut ↥U) := autSub Y U
  let Δb : Set (Subgroup (MulAut ↥U)) := (fun H : Subgroup (MulAut W) => autSub H U) '' Δ
  have hst : Y ≤ stabSub U := B1Red.le_stabSub_fixV_pCoreOf Y
  have hker : Y ⊓ centSub U = pCoreOf 2 Y :=
    inf_centSub_fixV_pCoreOf_eq hw hLY hTY hLT hcomp hsyl
  have hQleT : pCoreOf 2 Y ≤ T :=
    hsyl.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hLnc : ¬ L ≤ centSub U := by
    intro hLc
    have hLQ : L ≤ pCoreOf 2 Y := by
      intro x hx
      have hx' : x ∈ Y ⊓ centSub U := ⟨hLY hx, hLc hx⟩
      rwa [hker] at hx'
    have hq : CFSG.IsQuasisimple ↥L :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hcomp.2.2
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥L
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hLQ).isNilpotent
  have hLperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hcomp.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcompb : IsComponentOf Lb Yb := isComponentOf_autSub hLY hst hcomp hLnc
  have hsylb : IsSylowIn 2 Tb Yb := isSylowIn_autSub hTY hQleT hker hsyl
  have hfixb : fixV Tb ≠ fixV Yb := fixV_autSub_ne hTY hQleT hfix
  have hO2b : O2Trivial Yb := o2Trivial_autSub hw hLY hTY hLT hcomp hsyl
  have hLbYb : Lb ≤ Yb := autSub_mono hLY U
  have hTbYb : Tb ≤ Yb := autSub_mono hTY U
  have hsupb : Lb ⊔ Tb = Yb := by
    show autSub L U ⊔ autSub T U = autSub Y U
    rw [← hLT]
    exact (CFSG.CGT.PushingUpLit.BHS.autSub_sup (hLY.trans hst) (hTY.trans hst)).symm
  have hbne : bParam L Y ≤ bParam Lb Yb :=
    bParam_le_autSub hLY hst fun k A hA hne =>
      commutator_autSub_ne_bot_of_centralizer hLY hA.1 hst hker
        (CFSG.Quasithin.H13.Ch4.commutator_eq_bot_of_isComponentOf hcomp
          (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
        (inf_pCoreOf_le_centralizer_of_isComponent hcomp) hLperf hne
  have hfinb : Δb.Finite := hΔfin.image _
  have hΔbmem : ∀ H' ∈ Δb, H' ≤ Yb ∧ Tb ≤ H' := by
    rintro H' ⟨H, hH, rfl⟩
    exact ⟨autSub_mono (hΔT H hH).1 U, autSub_mono (hΔT H hH).2 U⟩
  have hgenb : (⨆ H' ∈ Δb, H') = Yb := by
    have h1 : (⨆ H ∈ Δ, autSub H U) = autSub Y U :=
      iSup_autSub_eq hΔfin (fun H hH => (hΔT H hH).1) hgen hst
    have h2 : (⨆ H' ∈ Δb, H') = ⨆ H ∈ Δ, autSub H U := by
      refine le_antisymm ?_ ?_
      · refine iSup_le fun H' => iSup_le fun hH' => ?_
        obtain ⟨H, hH, rfl⟩ := hH'
        exact le_iSup₂_of_le H hH le_rfl
      · refine iSup_le fun H => iSup_le fun hH => ?_
        exact le_iSup₂_of_le (autSub H U) ⟨H, hH, rfl⟩ le_rfl
    exact h2.trans h1
  have hsum_b : fIndexSum Δb ≤ (k : ℕ∞) := by
    have hfidx : ∀ H ∈ Δ, fIndex (autSub H U) ≤ fIndex H := by
      intro H hH
      rw [fIndex_autSub_eq (hΔT H hH).1 hst hker (hQleT.trans (hΔT H hH).2)]
    exact (fIndexSum_image_le hΔfin (fun H => autSub H U) hfidx).trans hkSum
  have hne_top : fIndexSum Δb ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hsum_b (by simp))
  let k' : ℕ := (fIndexSum Δb).toNat
  have hsumeq : fIndexSum Δb = (k' : ℕ∞) := (ENat.coe_toNat hne_top).symm
  have hk'le : k' ≤ k := by
    have h' := hsum_b
    rw [hsumeq] at h'
    exact WithTop.coe_le_coe.mp h'
  have h16 := h ↥U (fun u => Subtype.ext (hw (u : W))) Yb Lb Tb Δb k' hLbYb hTbYb
    hsupb hcompb hsylb hO2b hfinb hΔbmem hgenb hsumeq
  have hpara : E3.aParam Yb ≤ k' := h16.2 hfixb
  have hb2 : bParam Lb Yb ≤ E3.aParam Yb := bParam_le_aParam
  exact hbne.trans (hb2.trans (hpara.trans hk'le))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
