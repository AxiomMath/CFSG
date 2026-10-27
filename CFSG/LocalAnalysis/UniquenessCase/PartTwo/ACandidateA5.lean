module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.Quasithin.Background.RonanE42SetS2
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract
public import CFSG.LocalAnalysis.ComponentInitial.KnownFourGroupDiagonalPump
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFLayer
public import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo


open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

section MbarBridge

variable {G : Type} [Group G] [Finite G]

noncomputable def mbarEquivBarSub {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] :
    F11.MBar11 M ⊥ V ≃* ↥(barSub ⊥ V hV M) := by
  let hMstab : M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let φ : ↥M →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hMstab)
  have hker : φ.ker = (F11.CTilde M ⊥ V).subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker]
    show actTil ⊥ V hV (Subgroup.inclusion hMstab m) = 1 ↔ _
    rw [actTil_eq_one_iff]
    rw [cTilde_bot, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨m.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' := h v hv
      rw [Subgroup.mem_bot] at hv'
      simp only [Subgroup.coe_inclusion] at hv'
      have h1 : (m : G) * v * (m : G)⁻¹ = v := by
        rwa [mul_inv_eq_one] at hv'
      calc v * (m : G) = ((m : G) * v * (m : G)⁻¹) * (m : G) := by rw [h1]
        _ = (m : G) * v := by group
    · rintro ⟨-, hc⟩ v hv
      rw [Subgroup.mem_bot]
      simp only [Subgroup.coe_inclusion]
      rw [mul_inv_eq_one]
      have h := Subgroup.mem_centralizer_iff.1 hc v hv
      rw [h.symm]
      group
  have hrange : φ.range = barSub ⊥ V hV M := by
    ext ψ
    constructor
    · rintro ⟨m, rfl⟩
      exact actTil_mem_barSub ⊥ V hV m.2 (Subgroup.inclusion hMstab m).2
    · intro hψ
      obtain ⟨g, hgM, hgψ⟩ := (mem_barSub ⊥ V hV M ψ).1 hψ
      refine ⟨⟨g, hgM⟩, ?_⟩
      show actTil ⊥ V hV g = ψ
      exact hgψ
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))


theorem map_barImage11_mbarEquivBarSub {M V X : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal]
    (hXM : X ≤ M) :
    ((F11.barImage11 M ⊥ V X).map (mbarEquivBarSub hMV hV).toMonoidHom).map
      (barSub ⊥ V hV M).subtype = barSub ⊥ V hV X := by
  classical
  let hMstab : M ≤ stabTil ⊥ V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let φ : ↥M →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hMstab)
  have hmem : ∀ m : ↥M,
      (barSub ⊥ V hV M).subtype ((mbarEquivBarSub hMV hV).toMonoidHom
        (QuotientGroup.mk' ((F11.CTilde M ⊥ V).subgroupOf M) m)) = φ m := by
    intro m
    change (barSub ⊥ V hV M).subtype ((mbarEquivBarSub hMV hV).toMonoidHom
      (QuotientGroup.mk m)) = φ m
    unfold mbarEquivBarSub
    simp only [MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom]
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  ext ψ
  constructor
  · rintro ⟨q, hq, hqψ⟩
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 hq
    rw [← hxq] at hqψ
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx
    rw [← hmx] at hqψ
    rw [← hqψ, hmem m]
    exact actTil_mem_barSub ⊥ V hV (Subgroup.mem_subgroupOf.1 hm)
      (Subgroup.inclusion hMstab m).2
  · intro hψ
    obtain ⟨g, hgX, hgψ⟩ := (mem_barSub ⊥ V hV X ψ).1 hψ
    refine ⟨(mbarEquivBarSub hMV hV) (QuotientGroup.mk' _ ⟨g, hXM hgX⟩), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.2 hgX))
    · change (barSub ⊥ V hV M).subtype ((mbarEquivBarSub hMV hV).toMonoidHom
        (QuotientGroup.mk' ((F11.CTilde M ⊥ V).subgroupOf M) ⟨g, hXM hgX⟩)) = ψ
      rw [hmem ⟨g, hXM hgX⟩]
      show actTil ⊥ V hV g = ψ
      exact hgψ

end MbarBridge

theorem aCandidate_le_two_of_isAlt_five [Finite W] {K : Subgroup (MulAut W)}
    (hK : IsAlt ↥K 5) : ∀ n, Nonempty (ACandidate ↥K n) → n ≤ 2 := by
  classical
  intro n ⟨c⟩
  let := c.commGroup
  have := c.finiteW
  have : Finite (MulAut c.W) :=
    Finite.of_injective (fun φ : MulAut c.W => (φ : c.W → c.W)) DFunLike.coe_injective
  have : Finite ↥c.Y := Subtype.finite
  rw [c.eq_n]
  have h1 : E3.aParam c.Y ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥c.Y) := by
    simpa using CFSG.Quasithin.RonanE42.Gen.aParam_le_pRank (V := c.W) (ρ := c.Y.subtype)
      c.Y.subtype_injective
  obtain ⟨eK⟩ := hK
  have hKq : CFSG.Open.IsQuasisimple ↥K :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt (by norm_num) eK
  have hKtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hKq
  have hftop : fstarTop ↥K = ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.fstar_eq_self_of_isQuasisimple hKtop
  have hKcenter : Subgroup.center ↥K = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eK (alternatingGroup.center_eq_bot (by simp))
  obtain ⟨Z₀, hZ₀, hZ₀le, ⟨e₀⟩⟩ := c.central_factor
  have hZbot : Z₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ Subgroup.center ↥(fstarTop ↥K) := hZ₀le hz
    have hcent : Subgroup.center ↥(fstarTop ↥K) = ⊥ := by
      rw [hftop]
      exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv Subgroup.topEquiv hKcenter
    rw [hcent] at hz'
    exact hz'
  have htopEquiv : ↥(fstarTop ↥K) ≃* ↥K := by
    rw [hftop]
    exact Subgroup.topEquiv
  have hq : quotBy Z₀ hZ₀ ≃* ↥K := by
    have e1 : (↥(fstarTop ↥K) ⧸ Z₀) ≃* (↥(fstarTop ↥K) ⧸ (⊥ : Subgroup ↥(fstarTop ↥K))) :=
      QuotientGroup.quotientMulEquivOfEq hZbot
    exact (e1.trans QuotientGroup.quotientBot).trans htopEquiv
  have hFiso : ↥(fstarSubOf c.Y) ≃* ↥K := e₀.trans hq
  have hFcenter : Subgroup.center ↥(fstarSubOf c.Y) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv hFiso hKcenter
  have : (fstarSubOf c.Y).Normal := c.hLgn
  let conj : ↥c.Y →* MulAut ↥(fstarSubOf c.Y) :=
    MulAut.conjNormal (G := ↥c.Y) (H := fstarSubOf c.Y)
  have hFstar : fstarSubOf c.Y = CFSG.generalizedFitting ↥c.Y := by
    unfold fstarSubOf CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations,
      CFSG.subgroupOf_map_subtype_eq (K := c.Y) (CFSG.generalizedFitting ↥c.Y)]
  have hker : conj.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxcomm : x ∈ Subgroup.centralizer (fstarSubOf c.Y : Set ↥c.Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : conj x (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) = (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) := by
        have := congrArg (fun φ : MulAut ↥(fstarSubOf c.Y) =>
          φ (⟨y, hy⟩ : ↥(fstarSubOf c.Y))) hx
        simpa using this
      have h2 : (x : ↥c.Y) * (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) * (x : ↥c.Y)⁻¹ =
          (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) := by
        rw [← MulAut.conjNormal_apply (g := x)
          (h := (⟨y, hy⟩ : ↥(fstarSubOf c.Y)))]
        exact congrArg Subtype.val h1
      have h3 : (x : ↥c.Y) * (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) =
          (⟨y, hy⟩ : ↥(fstarSubOf c.Y)) * (x : ↥c.Y) :=
        mul_inv_eq_iff_eq_mul.1 h2
      exact Subtype.ext (by simpa using (congrArg Subtype.val h3).symm)
    have hxle : x ∈ fstarSubOf c.Y := by
      have hcent := CFSG.centralizer_generalizedFitting_le ↥c.Y
      rw [← hFstar] at hcent
      exact hcent hxcomm
    have hxZ : (⟨x, hxle⟩ : ↥(fstarSubOf c.Y)) ∈ Subgroup.center ↥(fstarSubOf c.Y) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hxcomm (y : ↥c.Y) y.2
    rw [hFcenter] at hxZ
    have hx1 : (⟨x, hxle⟩ : ↥(fstarSubOf c.Y)) = 1 := Subgroup.mem_bot.1 hxZ
    exact Subtype.ext (by simpa using congrArg Subtype.val hx1)
  have hinj : Function.Injective conj := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker
  have h2 : CFSG.Open.pRank 2 (⊤ : Subgroup ↥c.Y) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut ↥(fstarSubOf c.Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective (p := 2) (by norm_num) conj hinj
  have h3 : CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut ↥(fstarSubOf c.Y))) =
      CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut ↥K)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) (MulAut.congr hFiso)
  have h4 : CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut ↥K)) ≤ 2 := by
    have := CFSG.AGLEmbedding.pRank_top_mulAut_le (K := ↥K) (n := 5) (by norm_num) (by norm_num)
      eK (p := 2) Nat.prime_two
    simpa using this
  omega


private theorem eq_bot_of_le_center_fstar_of_isPGroup [Finite W]
    {Y A : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hAY : A ≤ Y) (hA2 : IsPGroup 2 A)
    (hAZ : A.subgroupOf Y ≤ (Subgroup.center ↥(fstarSubOf Y)).map
      (fstarSubOf Y).subtype) : A = ⊥ := by
  classical
  let F : Subgroup ↥Y := fstarSubOf Y
  have hFnormal : F.Normal := by
    rw [show F = CFSG.Open.genFittingFStar ↥Y from ?_]
    exact CFSG.ClassicalInvolution.genFittingFStar_normal _
    unfold F fstarSubOf CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations,
      CFSG.subgroupOf_map_subtype_eq]
  have hA'le : A.subgroupOf Y ≤ F := hAZ.trans (Subgroup.map_subtype_le _)
  have hA'2 : IsPGroup 2 (A.subgroupOf Y) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm
  have hA'F2 : IsPGroup 2 ((A.subgroupOf Y).subgroupOf F) :=
    hA'2.of_equiv (Subgroup.subgroupOfEquivOfLe hA'le).symm
  have hcent : (A.subgroupOf Y).subgroupOf F ≤ Subgroup.center ↥F := by
    intro x hx
    have hxA' : (x : ↥Y) ∈ A.subgroupOf Y := Subgroup.mem_subgroupOf.1 hx
    have hxZ := hAZ hxA'
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 hxZ
    have hcx' : c = x := Subtype.ext hcx
    rwa [← hcx']
  have hN : ((A.subgroupOf Y).subgroupOf F).Normal :=
    Subgroup.normal_of_le_center hcent
  have hle : (A.subgroupOf Y).subgroupOf F ≤ CFSG.pCore 2 ↥F :=
    CFSG.LieType.BorelTits.le_pCore (r := 2) hN hA'F2
  let P : Subgroup ↥Y := (CFSG.pCore 2 ↥F).map F.subtype
  have hPchar : (CFSG.pCore 2 ↥F).Characteristic := CFSG.pCore_characteristic
  have hPnorm : P.Normal := by
    have : F.Normal := hFnormal
    have : (CFSG.pCore 2 ↥F).Characteristic := hPchar
    exact ConjAct.normal_of_characteristic_of_normal
  have hPmap2 : IsPGroup 2 (P.map Y.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥F)).map F.subtype |>.map Y.subtype
  have hPmapY : P.map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  have hPmapN : ((P.map Y.subtype).subgroupOf Y).Normal := by
    rw [CFSG.subgroupOf_map_subtype_eq]
    exact hPnorm
  have hPmap : P.map Y.subtype = ⊥ := hO2 _ hPmapY hPmapN hPmap2
  have hPbot : P = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := P) (f := Y.subtype)
      Y.subtype_injective).1 hPmap
  have hA'bot : A.subgroupOf Y = ⊥ := by
    apply le_bot_iff.1
    calc A.subgroupOf Y = ((A.subgroupOf Y).subgroupOf F).map F.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hA'le).symm
      _ ≤ (CFSG.pCore 2 ↥F).map F.subtype := Subgroup.map_mono hle
      _ = P := rfl
      _ = ⊥ := hPbot
  calc A = (A.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hAY).symm
    _ = ⊥ := by rw [hA'bot, Subgroup.map_bot]

private theorem eq_bot_of_mem_aSet_two_of_centralizes_components [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y A : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y)
    (hAY : A ≤ Y) (hA2 : A ∈ E3.aSet 2 Y)
    (hAc : ∀ K, IsComponentOf K Y → ⁅A, K⁆ = ⊥) : A = ⊥ := by
  classical
  have hAab : IsElemAbelian2 A := hA2.2.2.1
  have hA2g : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hAab
  have hOdd : A ≤ Subgroup.centralizer
      (CFSG.ClassicalInvolution.Balance.oddCoreIn Y : Set (MulAut W)) :=
    CFSG.Quasithin.E3.e3_40 hW hA2
  have hp2Y : CFSG.pCore 2 ↥Y = ⊥ := by
    have hP2 : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map Y.subtype) :=
      (CFSG.pCore_isPGroup (p := 2)).map Y.subtype
    have hPn : (((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf Y).Normal := by
      rw [CFSG.subgroupOf_map_subtype_eq (K := Y)]
      exact CFSG.pCore_normal
    have hbot := hO2 _ (Subgroup.map_subtype_le _) hPn hP2
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥Y) (f := Y.subtype)
      Y.subtype_injective).1 hbot
  have hfit : (CFSG.fittingSubgroup ↥Y).map Y.subtype ≤
      Subgroup.centralizer (A : Set (MulAut W)) := by
    have h1 := CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore (G := ↥Y)
    rw [hp2Y, bot_sup_eq] at h1
    have hodd : CFSG.oddCore ↥Y =
        (CFSG.ClassicalInvolution.Balance.oddCoreIn Y).subgroupOf Y := by
      rw [CFSG.ClassicalInvolution.Balance.oddCoreIn,
        CFSG.Quasithin.SBd19F.componentClassificationOddCore_eq_pPrimeCore,
        ← CFSG.Holt.StarLemma26.oddCore_eq_pPrimeCore_two]
      exact (CFSG.subgroupOf_map_subtype_eq (K := Y) (CFSG.oddCore ↥Y)).symm
    calc (CFSG.fittingSubgroup ↥Y).map Y.subtype
        ≤ (CFSG.oddCore ↥Y).map Y.subtype := Subgroup.map_mono h1
      _ = CFSG.ClassicalInvolution.Balance.oddCoreIn Y := by
          rw [hodd]
          exact Subgroup.map_subgroupOf_eq_of_le
            (CFSG.ClassicalInvolution.Balance.oddCoreIn_le Y)
      _ ≤ Subgroup.centralizer (A : Set (MulAut W)) :=
          Subgroup.le_centralizer_iff.1 hOdd
  have hlayer : (CFSG.layer ↥Y).map Y.subtype ≤
      Subgroup.centralizer (A : Set (MulAut W)) := by
    rw [CFSG.layer.eq_sSup]
    rw [show (sSup {K : Subgroup ↥Y | CFSG.IsComponent K}) =
        ⨆ K, ⨆ (_ : CFSG.IsComponent K), K from sSup_eq_iSup]
    rw [Subgroup.map_iSup]
    refine iSup_le fun K' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK' => ?_
    have hK'asm : CFSG.Assembly.IsComponentOf K' ⊤ :=
      (CFSG.Assembly.isComponentOf_iff_open).2 ((CFSG.isComponent_iff_open K').mp hK')
    have hKc : IsComponentOf (K'.map Y.subtype) Y :=
      (CFSG.Assembly.isComponentOf_iff_open).1
        (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_subtype_top hK'asm)
    have hcomm := hAc (K'.map Y.subtype) hKc
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact hcomm
  have hFcent : A ≤ Subgroup.centralizer (Fstar Y : Set (MulAut W)) := by
    have hFstar : Fstar Y = (CFSG.generalizedFitting ↥Y).map Y.subtype := by
      unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
      rw [CFSG.Adapters.genFittingFStar_eq_foundations]
    rw [hFstar, CFSG.generalizedFitting.eq_sup, Subgroup.map_sup]
    exact Subgroup.le_centralizer_iff.2 (sup_le hfit hlayer)
  have hAF : A ≤ Fstar Y := by
    have hA' : A.subgroupOf Y ≤ Subgroup.centralizer
        ((Fstar Y).subgroupOf Y : Set ↥Y) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : (b : MulAut W) ∈ Fstar Y := hb
      have ha' : (a : MulAut W) ∈ A := ha
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hFcent ha') (b : MulAut W) hb')
    have hF' : (Fstar Y).subgroupOf Y = CFSG.generalizedFitting ↥Y := by
      unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
      rw [CFSG.Adapters.genFittingFStar_eq_foundations,
        CFSG.subgroupOf_map_subtype_eq]
    rw [hF'] at hA'
    have hcent := CFSG.centralizer_generalizedFitting_le ↥Y
    have hle : A.subgroupOf Y ≤ (Fstar Y).subgroupOf Y := by
      rw [hF']
      exact hA'.trans hcent
    calc A = (A.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hAY).symm
      _ ≤ (Fstar Y) := by
          refine (Subgroup.map_mono hle).trans ?_
          rw [Subgroup.map_subgroupOf_eq_of_le
            (show Fstar Y ≤ Y from Subgroup.map_subtype_le _)]
  set F : Subgroup ↥Y := (Fstar Y).subgroupOf Y with hF
  have hA'Z : A.subgroupOf Y ≤ (Subgroup.center ↥F).map F.subtype := by
    intro a ha
    have haA : (a : MulAut W) ∈ A := ha
    have haF : (a : MulAut W) ∈ Fstar Y := hAF haA
    have haF' : a ∈ F := by
      rw [hF]
      exact haF
    refine ⟨⟨a, haF'⟩, ?_, rfl⟩
    change (⟨a, haF'⟩ : ↥F) ∈ Subgroup.center ↥F
    rw [Subgroup.mem_center_iff]
    intro f
    apply Subtype.ext
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.1 (hFcent haA) (f : MulAut W) f.2
    exact h
  have hF' : F = fstarSubOf Y := rfl
  rw [hF'] at hA'Z
  exact eq_bot_of_le_center_fstar_of_isPGroup hO2 hAY hA2g hA'Z


theorem aParam_le_of_components [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (h77 : W4Lem7_7) {Y : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hn : ∀ K, IsComponentOf K Y → ∀ k, Nonempty (ACandidate ↥K k) → k ≤ n) :
    E3.aParam Y ≤ n ∧ ∀ A ∈ E3.aSet n Y, A ≠ ⊥ → ∃ K, IsComponentOf K Y ∧ ⁅A, K⁆ ≠ ⊥ := by
  classical
  have hcomp_bot : ∀ A : Subgroup (MulAut W), A ∈ E3.aSet (n + 1) Y →
      (∀ K, IsComponentOf K Y → ⁅A, K⁆ = ⊥) → A = ⊥ := by
    intro A hA hAc
    exact eq_bot_of_mem_aSet_two_of_centralizes_components hW hO2 hA.1
      (E3.aSet_anti (by omega) Y hA) hAc
  constructor
  · refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty Y n ?_
    intro A hA
    have hAc : ∀ K, IsComponentOf K Y → ⁅A, K⁆ = ⊥ := by
      intro K hK
      have hlt : ∀ m, Nonempty (ACandidate ↥K m) → m < n + 1 := by
        intro m hm
        have := hn K hK m hm
        omega
      exact h77 W hW Y K A (n + 1) hK hA hlt
    exact hA.2.1 (hcomp_bot A hA hAc)
  · intro A hA hAne
    by_contra hcon
    push Not at hcon
    exact hAne (eq_bot_of_mem_aSet_two_of_centralizes_components hW hO2 hA.1
      (E3.aSet_anti hn2 Y hA) hcon)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
