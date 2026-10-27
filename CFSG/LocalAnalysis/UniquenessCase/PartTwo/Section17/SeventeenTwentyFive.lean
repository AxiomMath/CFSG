module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
public import CFSG.Quasithin.Vol2.Ch10SecD211F
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2Centralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def H17_25_one (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Subgroup G :=
  preBarSub (L ⊔ D.T) V₀ V hV
    (Subgroup.centralizer (((Subgroup.center ↥(barSub V₀ V hV D.T)).map
      (barSub V₀ V hV D.T).subtype) : Set (MulAut (Vtil V₀ V hV))))

theorem T_le_H17_25_one {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V) :
    D.T ≤ H17_25_one D V₀ V L h.isElemAbelian := by
  intro t ht
  have htS : t ∈ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ (D.sylowM.le ht)
  have hta : actTil V₀ V h.isElemAbelian ⟨t, htS⟩ ∈ barSub V₀ V h.isElemAbelian D.T :=
    actTil_mem_barSub V₀ V h.isElemAbelian ht htS
  refine (mem_preBarSub (L ⊔ D.T) V₀ V h.isElemAbelian _).2
    ⟨Subgroup.mem_sup_right ht, htS, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  have hcomm : w * ⟨actTil V₀ V h.isElemAbelian ⟨t, htS⟩, hta⟩ =
      ⟨actTil V₀ V h.isElemAbelian ⟨t, htS⟩, hta⟩ * w :=
    (Subgroup.mem_center_iff.1 hw ⟨actTil V₀ V h.isElemAbelian ⟨t, htS⟩, hta⟩).symm
  exact congrArg Subtype.val hcomm

theorem H17_25_one_le_M {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hLM : L ≤ D.M) : H17_25_one D V₀ V L h.isElemAbelian ≤ D.M :=
  inf_le_left.trans (sup_le hLM D.sylowM.le)

@[expose] def Gap17_25_H2 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  V₀ ≠ ⊥ → P17_24_1 D V₀ V L hV → IsSpor (Bar2 L) .J2 → D.sig = {5} →
    ∃ H₂ : Subgroup G, D.T ≤ H₂ ∧ H₂ ≤ D.M ∧ D.T.relIndex H₂ = 5 ∧
      barSub V₀ V hV H₂ ≤ barSub V₀ V hV D.T ⊔
        Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))

@[expose] def Gap17_25_max (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  V₀ ≠ ⊥ → P17_24_1 D V₀ V L hV → IsSpor (Bar2 L) .J2 → D.sig = {5} →
    WeakClosure81.InFSq 2 (H17_25_one D V₀ V L hV)

theorem sig_eq_five_of_J2 {D : Data G} {V₀ V L : Subgroup G}
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V) (c : Ctx17_17 D V₀ V L) :
    D.sig = {5} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h17_22 L P (centerOf P) c hP rfl with hHe | ⟨-, hsig5, -⟩
  · exact absurd (h17_23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · exact hsig5

theorem twoResidual_not_le_conjSubgroup_of_five {M : Subgroup G} {H : Subgroup G}
    (hHM : H ≤ M) (h5dvd : 5 ∣ Nat.card H)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 M) :
    ∀ g : G, g ∉ M → ¬ twoResidual H ≤ conjSubgroup M g := by
  intro g hg hle
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5 h5dvd
  have hxH : (y : G) ∈ H := y.2
  have hxord : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe, hyord]
  have hxodd : Odd (orderOf (y : G)) := by
    rw [hxord]
    exact ⟨2, by norm_num⟩
  have hxres : (y : G) ∈ twoResidual H :=
    CFSG.Quasithin.F6.mem_twoResidual_of_odd hxH hxodd
  have hxX : (y : G) ∈ M ⊓ conjSubgroup M g :=
    Subgroup.mem_inf.2 ⟨hHM hxH, hle hxres⟩
  have hdvd : 5 ∣ Nat.card ↥(M ⊓ conjSubgroup M g) := by
    have h := Subgroup.orderOf_dvd_natCard (M ⊓ conjSubgroup M g) hxX
    rwa [hxord] at h
  have hg' : g⁻¹ ∉ M := fun hh => hg (by simpa using M.inv_mem hh)
  exact hsp.2.2 g⁻¹ hg' (by simpa [conjSubgroup] using hdvd)

theorem isSpor_barSub_of_J2 {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    IsSpor ↥(barSub V₀ V h.isElemAbelian L) .J2 :=
  isSpor_barSub_of_isSpor_bar2_of_pcore h.isElemAbelian
    (c.mem_calC.1.le.trans (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀))
    (TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.isElemAbelian c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)) hL1 hJ2

theorem mem_pCoreOf_of_mem_centralizer_barSub {D : Data G}
    {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (hJ2 : IsSpor (Bar2 L) .J2) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {y : G} (hyL : y ∈ L) (hys : y ∈ stabTil V₀ V)
    (hyC : actTil V₀ V h.isElemAbelian ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian)))) :
    y ∈ pCoreOf 2 L := by
  classical
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLstab : L ≤ stabTil V₀ V :=
    c.mem_calC.1.le.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  let φ : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLstab)).codRestrict _
      (fun z => actTil_mem_barSub V₀ V hV z.2 (hLstab z.2))
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨g, hgL, hgy⟩ :=
      (mem_barSub V₀ V hV L (z : MulAut (Vtil V₀ V hV))).1 z.2
    refine ⟨⟨(g : G), hgL⟩, ?_⟩
    apply Subtype.ext
    change actTil V₀ V hV ⟨(g : G), hLstab hgL⟩ = (z : MulAut _)
    rwa [show (⟨(g : G), hLstab hgL⟩ : stabTil V₀ V) = g from rfl]
  haveI : IsSimpleGroup ↥(barSub V₀ V hV L) := by
    obtain ⟨e⟩ := isSpor_barSub_of_J2 h c hJ2 hL1
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcenter : Subgroup.center ↥(barSub V₀ V hV L) = ⊥ := by
    obtain ⟨e⟩ := isSpor_barSub_of_J2 h c hJ2 hL1
    haveI : IsSimpleGroup ↥(barSub V₀ V hV L) :=
      (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
    refine CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime ?_
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2]
    norm_num
  have hφy_center : φ ⟨y, hyL⟩ ∈ Subgroup.center ↥(barSub V₀ V hV L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := hφsurj z
    apply Subtype.ext
    change actTil V₀ V hV ⟨(w : G), hLstab w.2⟩ * actTil V₀ V hV ⟨y, hLstab hyL⟩ =
      actTil V₀ V hV ⟨y, hLstab hyL⟩ * actTil V₀ V hV ⟨(w : G), hLstab w.2⟩
    have hwmem : actTil V₀ V hV ⟨(w : G), hLstab w.2⟩ ∈ barSub V₀ V hV L :=
      actTil_mem_barSub V₀ V hV w.2 (hLstab w.2)
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hwmem
    rwa [show actTil V₀ V hV ⟨y, hLstab hyL⟩ = actTil V₀ V hV ⟨y, hys⟩ from rfl]
  have hφy1 : φ ⟨y, hyL⟩ = 1 := by
    rw [hcenter, Subgroup.mem_bot] at hφy_center
    exact hφy_center
  have hact : actTil V₀ V hV ⟨y, hys⟩ = 1 := by
    have hval2 : actTil V₀ V hV ⟨y, hLstab hyL⟩ = 1 := by
      have h := congrArg (fun t : ↥(barSub V₀ V hV L) => (t : MulAut (Vtil V₀ V hV))) hφy1
      exact h
    rwa [show (⟨y, hLstab hyL⟩ : stabTil V₀ V) = ⟨y, hys⟩ from rfl] at hval2
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  exact mem_pCoreOf_of_actTil_eq_one h c.mem_calC.1 hsimple hL1 hyL hys hact

theorem mbar_le_normalizer_barSub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hLM : L ≤ D.M) (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G)) :
    Mbar D.M V₀ V h.isElemAbelian ≤
      Subgroup.normalizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian))) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono V₀ V h.isElemAbelian hLM)).1
    (barSub_subgroupOf_mbar_normal h.isElemAbelian hLM hMnorm)

theorem actTil_conj_mul_inv_eq_one {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (c : Ctx17_17 D V₀ V L) {y x : G} (hys : y ∈ stabTil V₀ V)
    (hyC : actTil V₀ V h.isElemAbelian ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian))))
    (hxL : x ∈ L) (hstab : y * x * y⁻¹ * x⁻¹ ∈ stabTil V₀ V) :
    actTil V₀ V h.isElemAbelian ⟨y * x * y⁻¹ * x⁻¹, hstab⟩ = 1 := by
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hxstab : x ∈ stabTil V₀ V :=
    (le_stabTil hpair.le_normalizer hpair.le_normalizer₀) (hLM hxL)
  have hxbar : actTil V₀ V h.isElemAbelian ⟨x, hxstab⟩ ∈
      barSub V₀ V h.isElemAbelian L :=
    actTil_mem_barSub V₀ V h.isElemAbelian hxL hxstab
  have hcomm : actTil V₀ V h.isElemAbelian ⟨x, hxstab⟩ *
      actTil V₀ V h.isElemAbelian ⟨y, hys⟩ =
      actTil V₀ V h.isElemAbelian ⟨y, hys⟩ *
      actTil V₀ V h.isElemAbelian ⟨x, hxstab⟩ :=
    Subgroup.mem_centralizer_iff.mp hyC _ hxbar
  have harg : (⟨y * x * y⁻¹ * x⁻¹, hstab⟩ : stabTil V₀ V) =
      ⟨y, hys⟩ * ⟨x, hxstab⟩ * ⟨y, hys⟩⁻¹ * ⟨x, hxstab⟩⁻¹ := by
    apply Subtype.ext
    simp [mul_assoc]
  rw [harg, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [← hcomm]
  group

theorem actTil_mem_centralizer_of_le_sup {D : Data G} {V₀ V L H₂ : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G))
    (hbar : barSub V₀ V h.isElemAbelian H₂ ≤
      barSub V₀ V h.isElemAbelian D.T ⊔
        Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
          Set (MulAut (Vtil V₀ V h.isElemAbelian))))
    {y : G} (hyH₂ : y ∈ H₂) (hyord : orderOf y = 5) (hys : y ∈ stabTil V₀ V) :
    actTil V₀ V h.isElemAbelian ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  classical
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTstab : D.T ≤ stabTil V₀ V :=
    hTM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hybar_mem : actTil V₀ V hV ⟨y, hys⟩ ∈ barSub V₀ V hV H₂ :=
    actTil_mem_barSub V₀ V hV hyH₂ hys
  have hybar_sup : actTil V₀ V hV ⟨y, hys⟩ ∈
      barSub V₀ V hV D.T ⊔
        Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    hbar hybar_mem
  have hTsub : IsPGroup 2 (D.T.subgroupOf (stabTil V₀ V)) :=
    D.sylowM.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTstab).symm
  have hA2 : IsPGroup 2 (barSub V₀ V hV D.T) := by
    rw [barSub]
    exact hTsub.map (actTil V₀ V hV)
  have hMbarN : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    mbar_le_normalizer_barSub h hLM hMnorm
  have hAN : barSub V₀ V hV D.T ≤
      Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hTM).trans hMbarN
  have hANB : barSub V₀ V hV D.T ≤
      Subgroup.normalizer
        (Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :
          Set (MulAut (Vtil V₀ V hV))) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hAN
  have hybar_odd : Odd (orderOf (actTil V₀ V hV ⟨y, hys⟩)) := by
    have h1 : actTil V₀ V hV ⟨y, hys⟩ ^ 5 = 1 := by
      rw [← map_pow]
      have hy5 : (⟨y, hys⟩ : stabTil V₀ V) ^ 5 = 1 := by
        apply Subtype.ext
        show y ^ 5 = 1
        rw [← hyord, pow_orderOf_eq_one]
      rw [hy5, map_one]
    exact Odd.of_dvd_nat (by norm_num : Odd 5) (orderOf_dvd_of_pow_eq_one h1)
  have hybar_sup' : actTil V₀ V hV ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) ⊔
        barSub V₀ V hV D.T := by
    rw [sup_comm]
    exact hybar_sup
  exact CFSG.Quasithin.Vol2.Ch10.SecD.mem_of_odd_of_mem_sup hANB hA2 hybar_sup' hybar_odd

theorem not_isCyclic_closure_pair_of_J2 {D : Data G}
    {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) {x y : G} (hxL : x ∈ L)
    (hxord : orderOf x = 5) (hys : y ∈ stabTil V₀ V) (hyord : orderOf y = 5)
    (hyC : actTil V₀ V h.isElemAbelian ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian)))) :
    ¬ IsCyclic ↥(Subgroup.closure ({x, y} : Set G)) := by
  classical
  intro hcyc
  haveI : IsCyclic ↥(Subgroup.closure ({x, y} : Set G)) := hcyc
  let E : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxE : x ∈ E := Subgroup.subset_closure (by simp [E])
  have hyE : y ∈ E := Subgroup.subset_closure (by simp [E])
  have hxordE : orderOf (⟨x, hxE⟩ : ↥E) = 5 := by
    rw [← Subgroup.orderOf_coe (⟨x, hxE⟩ : ↥E)]
    exact hxord
  have hyordE : orderOf (⟨y, hyE⟩ : ↥E) = 5 := by
    rw [← Subgroup.orderOf_coe (⟨y, hyE⟩ : ↥E)]
    exact hyord
  have hy_zp : (⟨y, hyE⟩ : ↥E) ∈ Subgroup.zpowers (⟨x, hxE⟩ : ↥E) :=
    CFSG.GroupTheory.SuzukiTwoGroup.mem_zpowers_of_orderOf_eq
      (by rw [hxordE, hyordE])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_zp
  have hkG : x ^ k = y := by
    have h := congrArg (fun t : ↥E => (t : G)) hk
    simpa [Subgroup.coe_zpow] using h
  have hyL : y ∈ L := by
    rw [← hkG]
    exact L.zpow_mem hxL k
  have hyO2 : y ∈ pCoreOf 2 L :=
    mem_pCoreOf_of_mem_centralizer_barSub h c hJ2 hL1 hyL hys hyC
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨a, ha⟩ := hO2.exists_card_eq
  have hdvd : orderOf y ∣ Nat.card (pCoreOf 2 L) :=
    Subgroup.orderOf_dvd_natCard _ hyO2
  rw [ha, hyord] at hdvd
  exact (by norm_num : ¬ (5 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd)

theorem exists_index_barSub_pow_two {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (c : Ctx17_17 D V₀ V L) (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G)) :
    ∃ n : ℕ,
      ((barSub V₀ V h.isElemAbelian L).subgroupOf
        (barSub V₀ V h.isElemAbelian (L ⊔ D.T))).index = 2 ^ n := by
  classical
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hTstab : D.T ≤ stabTil V₀ V :=
    hTM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  set K : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L with hK
  set S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hS
  set H : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T) with hH
  have hHsup : H = K ⊔ S := by
    rw [hH, hK, hS]
    exact s16c7_barSub_sup V₀ V hV hLstab hTstab
  have hKH : K ≤ H := by rw [hHsup]; exact le_sup_left
  have hKMbar : K ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hLM
  have hSMbar : S ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hTM
  have hMbarN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKMbar).1
      (barSub_subgroupOf_mbar_normal hV hLM hMnorm)
  have hHsupN : H ≤ Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hHsup]
    exact sup_le Subgroup.le_normalizer (hSMbar.trans hMbarN)
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHsupN
  have hrel : (K.subgroupOf H).index = K.relIndex S := by
    rw [hHsup]
    rw [hHsup] at hKnormal
    have htop : (K.subgroupOf (K ⊔ S)) ⊔ (S.subgroupOf (K ⊔ S)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    calc
      (K.subgroupOf (K ⊔ S)).index = (K.subgroupOf (K ⊔ S)).relIndex ⊤ :=
        (Subgroup.relIndex_top_right _).symm
      _ = (K.subgroupOf (K ⊔ S)).relIndex
            ((K.subgroupOf (K ⊔ S)) ⊔ (S.subgroupOf (K ⊔ S))) := by rw [← htop]
      _ = (K.subgroupOf (K ⊔ S)).relIndex (S.subgroupOf (K ⊔ S)) :=
        @Subgroup.relIndex_sup_left _ _ (S.subgroupOf (K ⊔ S)) (K.subgroupOf (K ⊔ S)) hKnormal
      _ = K.relIndex S := Subgroup.relIndex_subgroupOf le_sup_right
  have hTsub : IsPGroup 2 (D.T.subgroupOf (stabTil V₀ V)) :=
    D.sylowM.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTstab).symm
  have hS2 : IsPGroup 2 S := by
    rw [hS, barSub]
    exact hTsub.map (actTil V₀ V hV)
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hdvd : (K.subgroupOf H).index ∣ Nat.card ↥S := by
    rw [hrel]
    exact Subgroup.relIndex_dvd_card K S
  rw [hk] at hdvd
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨n, hn⟩

theorem exists_five_barSub_centralizing_center
    (hJ2center : K_J2_center_five) {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G)) :
    ∃ xbar ∈ barSub V₀ V h.isElemAbelian L, orderOf xbar = 5 ∧
      xbar ∈ Subgroup.centralizer
        (((Subgroup.center (barSub V₀ V h.isElemAbelian D.T)).map
          (barSub V₀ V h.isElemAbelian D.T).subtype) :
            Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  classical
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  have hTstab : D.T ≤ stabTil V₀ V :=
    hTM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  set K : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L with hK
  set S : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hS
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (L ⊔ D.T) with hY
  have hYsup : Y = K ⊔ S := by
    rw [hY, hK, hS]
    exact s16c7_barSub_sup V₀ V hV hLstab hTstab
  have hKH : K ≤ Y := by rw [hYsup]; exact le_sup_left
  have hSY : S ≤ Y := by rw [hYsup]; exact le_sup_right
  have hKMbar : K ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hLM
  have hSMbar : S ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hTM
  have hKnormal : (K.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 ?_
    have hMbarN : Mbar D.M V₀ V hV ≤
        Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V hV))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKMbar).1
        (barSub_subgroupOf_mbar_normal hV hLM hMnorm)
    rw [hYsup]
    exact sup_le Subgroup.le_normalizer (hSMbar.trans hMbarN)
  have hKspor : IsSpor ↥(K.subgroupOf Y) .J2 := by
    obtain ⟨e⟩ := isSpor_barSub_of_J2 h c hJ2 hL1
    exact ⟨(Subgroup.subgroupOfEquivOfLe hKH).trans e⟩
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 S Y := isSylowIn_barSub_T_sup h hLM
  have hSsyl : CFSG.Quasithin.IsSylowIn 2 (S.subgroupOf Y) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hTsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
    · have hindex : (S.subgroupOf Y).index = S.relIndex Y := by
        rw [← Subgroup.relIndex_top_right (S.subgroupOf Y), ← Subgroup.subgroupOf_self Y]
        exact Subgroup.relIndex_subgroupOf (H := S) (K := Y) (L := Y) le_rfl
      rw [Subgroup.relIndex_top_right, hindex]
      exact hTsyl.not_dvd_relIndex
  obtain ⟨n, hn⟩ := exists_index_barSub_pow_two h c hMnorm
  obtain ⟨x₀, hx₀K, hx₀ord, hx₀cent⟩ :=
    hJ2center ↥Y (K.subgroupOf Y) hKnormal hKspor ⟨n, hn⟩ (S.subgroupOf Y) hSsyl
  refine ⟨(x₀ : MulAut (Vtil V₀ V hV)), ?_, ?_, ?_⟩
  · simpa [Subgroup.mem_subgroupOf] using hx₀K
  · rw [Subgroup.orderOf_coe (x₀ : ↥Y)]
    exact hx₀ord
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    let e : ↥(S.subgroupOf Y) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSY
    have hwScenter : e.symm w ∈ Subgroup.center ↥(S.subgroupOf Y) := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp hw (e u)
    have hx₀w := hx₀cent (e.symm w) (e.symm w).2 (fun u hu => ?_)
    · have hcoe : ((e.symm w : ↥(S.subgroupOf Y)) : MulAut (Vtil V₀ V hV)) =
          (w : MulAut (Vtil V₀ V hV)) := by
        have h1 : (((Subgroup.subgroupOfEquivOfLe hSY)
            ((Subgroup.subgroupOfEquivOfLe hSY).symm w) : ↥S) :
              MulAut (Vtil V₀ V hV)) = (w : MulAut (Vtil V₀ V hV)) := by
          rw [MulEquiv.apply_symm_apply]
        rw [Subgroup.subgroupOfEquivOfLe_apply_coe hSY
          ((Subgroup.subgroupOfEquivOfLe hSY).symm w)] at h1
        exact h1
      have hval := congrArg (fun t : ↥Y => (t : MulAut (Vtil V₀ V hV))) hx₀w
      simpa [Subgroup.coe_mul, hcoe] using hval.symm
    · have h := (Subgroup.mem_center_iff.mp hwScenter ⟨u, hu⟩).symm
      exact congrArg (fun t : ↥(S.subgroupOf Y) => (t : ↥Y)) h

theorem exists_five_mem_H17_25_one_commute
    (hJ2center : K_J2_center_five) {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (c : Ctx17_17 D V₀ V L) (hJ2 : IsSpor (Bar2 L) .J2)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hMnorm : D.M ≤ Subgroup.normalizer (L : Set G))
    {y : G} (hyM : y ∈ D.M) (hys : y ∈ stabTil V₀ V) (hyord : orderOf y = 5)
    (hyC : actTil V₀ V h.isElemAbelian ⟨y, hys⟩ ∈
      Subgroup.centralizer (barSub V₀ V h.isElemAbelian L :
        Set (MulAut (Vtil V₀ V h.isElemAbelian)))) :
    ∃ x, x ∈ L ∧ x ∈ H17_25_one D V₀ V L h.isElemAbelian ∧
      orderOf x = 5 ∧ x * y = y * x := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hpair.le_normalizer hpair.le_normalizer₀)
  obtain ⟨xbar, hxbarK, hxbarord, hxbarcent⟩ :=
    exists_five_barSub_centralizing_center hJ2center h c hJ2 hL1 hMnorm
  obtain ⟨g, hgL, hgact⟩ :=
    (mem_barSub V₀ V hV L xbar).1 hxbarK
  let x₁ : ↥L := ⟨(g : G), hgL⟩
  let φ : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLstab)).codRestrict _
      (fun z => actTil_mem_barSub V₀ V hV z.2 (hLstab z.2))
  have hφx₁ : φ x₁ = ⟨xbar, hxbarK⟩ := by
    apply Subtype.ext
    change actTil V₀ V hV ⟨(g : G), hLstab hgL⟩ = xbar
    rwa [show (⟨(g : G), hLstab hgL⟩ : stabTil V₀ V) = g from rfl]
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hMnorm hyM
  let yN : ↥(Subgroup.normalizer (L : Set G)) := ⟨y, hyN⟩
  let α : MulAut ↥L := Subgroup.normalizerMonoidHom L yN
  have hα5 : α ^ 5 = 1 := by
    change (Subgroup.normalizerMonoidHom L yN) ^ 5 = 1
    rw [← map_pow]
    have hy5 : yN ^ 5 = 1 := by
      apply Subtype.ext
      show y ^ 5 = 1
      rw [← hyord, pow_orderOf_eq_one]
    rw [hy5, map_one]
  let Np : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hNpnormal : Np.Normal := CFSG.pCore_normal (p := 2) (G := ↥L)
  have hNpp : IsPGroup 2 Np := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  have hr : ¬ 5 ∣ Nat.card ↥Np := by
    obtain ⟨k, hk⟩ := hNpp.exists_card_eq
    rw [hk]
    intro hd
    exact (by norm_num : ¬ (5 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
  have hNpα : ∀ n ∈ Np, α n ∈ Np := by
    intro n hn
    have hnG : (n : G) ∈ pCoreOf 2 L := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hyP : y ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hyN
    have hconj : y * (n : G) * y⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp hyP (n : G)).mp hnG
    have hαcoe : ((α n : ↥L) : G) = y * (n : G) * y⁻¹ := by
      change ((Subgroup.normalizerMonoidHom L yN) n : ↥L) = y * (n : G) * y⁻¹
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hsub : (pCoreOf 2 L).subgroupOf L = Np :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [← hsub, Subgroup.mem_subgroupOf, hαcoe]
    exact hconj
  have hαx₁ : ((α x₁ : ↥L) : G) = y * (x₁ : G) * y⁻¹ := by
    change ((Subgroup.normalizerMonoidHom L yN) x₁ : ↥L) = y * (x₁ : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  set zG : G := y * (x₁ : G) * y⁻¹ * (x₁ : G)⁻¹ with hzG
  have hx₁stab : (x₁ : G) ∈ stabTil V₀ V := hLstab x₁.2
  have hzGstab : zG ∈ stabTil V₀ V := by
    rw [hzG]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hys hx₁stab)
      (Subgroup.inv_mem _ hys)) (Subgroup.inv_mem _ hx₁stab)
  have hconjL : y * (x₁ : G) * y⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hyN (x₁ : G)).mp x₁.2
  have hzL : zG ∈ L := by
    rw [hzG]
    exact L.mul_mem hconjL (L.inv_mem x₁.2)
  have hzact : actTil V₀ V hV ⟨zG, hzGstab⟩ = 1 :=
    actTil_conj_mul_inv_eq_one h c hys hyC x₁.2 hzGstab
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hzP : zG ∈ pCoreOf 2 L :=
    mem_pCoreOf_of_actTil_eq_one h c.mem_calC.1 hsimple hL1 hzL hzGstab hzact
  have hxα : α x₁ * x₁⁻¹ ∈ Np := by
    have hsub : (pCoreOf 2 L).subgroupOf L = Np :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    have hval : ((α x₁ * x₁⁻¹ : ↥L) : G) = zG := by
      rw [hzG, Subgroup.coe_mul, Subgroup.coe_inv, hαx₁]
    rw [← hsub, Subgroup.mem_subgroupOf, hval]
    exact hzP
  obtain ⟨cc, hccN, hccα⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
      α hα5 Np hNpnormal hNpα hr x₁ hxα
  have hpcore_le_ker : Np ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change actTil V₀ V hV ⟨(n : G), hLstab n.2⟩ = 1
    have hnP : (n : G) ∈ pCoreOf 2 L := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hmem : actTil V₀ V hV ⟨(n : G), hLstab n.2⟩ ∈
        barSub V₀ V hV (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V hV hnP (hLstab n.2)
    rw [TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)] at hmem
    simpa using hmem
  have hφcc : φ cc = ⟨xbar, hxbarK⟩ := by
    have hmem : cc * x₁⁻¹ ∈ φ.ker := hpcore_le_ker hccN
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hmem
    have hφccx : φ cc = φ x₁ := mul_inv_eq_one.mp hmem
    rw [hφccx, hφx₁]
  have hcccomm : (cc : G) * y = y * (cc : G) := by
    have h := congrArg (fun t : ↥L => (t : G)) hccα
    rw [show ((α cc : ↥L) : G) = y * (cc : G) * y⁻¹ from by
      change ((Subgroup.normalizerMonoidHom L yN) cc : ↥L) = y * (cc : G) * y⁻¹
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]] at h
    calc
      (cc : G) * y = (y * (cc : G) * y⁻¹) * y := by rw [h]
      _ = y * (cc : G) := by group
  have hφcc_ord : orderOf (φ cc) = 5 := by
    rw [hφcc]
    simpa using hxbarord
  have hdvd_ord : 5 ∣ orderOf cc := by
    have h := orderOf_map_dvd φ cc
    rwa [hφcc_ord] at h
  have hdvd_zp : 5 ∣ Nat.card ↥(Subgroup.zpowers cc) := by
    rw [Nat.card_zpowers]
    exact hdvd_ord
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers cc)) 5 hdvd_zp
  have hxcomm : (((z : ↥L) : G) * y = y * ((z : ↥L) : G)) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    have hcommG : Commute (cc : G) y := hcccomm
    rw [show (z : ↥L) = cc ^ k from hk.symm, Subgroup.coe_zpow]
    exact (hcommG.zpow_left k).eq
  refine ⟨((z : ↥L) : G), (z : ↥L).2, ?_, ?_, ?_⟩
  · have hφz_mem : φ (z : ↥L) ∈ Subgroup.zpowers (⟨xbar, hxbarK⟩ : ↥(barSub V₀ V hV L)) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by rw [← hk, map_zpow, hφcc]⟩
    have hgen : (⟨xbar, hxbarK⟩ : ↥(barSub V₀ V hV L)) ∈
        Subgroup.comap (Subgroup.subtype (barSub V₀ V hV L))
          (Subgroup.centralizer
            (((Subgroup.center (barSub V₀ V hV D.T)).map
              (barSub V₀ V hV D.T).subtype) : Set (MulAut (Vtil V₀ V hV)))) :=
      Subgroup.mem_comap.mpr hxbarcent
    have hzp_le := Subgroup.zpowers_le.mpr hgen
    have hcent : ((φ (z : ↥L) : ↥(barSub V₀ V hV L)) : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer
          (((Subgroup.center (barSub V₀ V hV D.T)).map
            (barSub V₀ V hV D.T).subtype) : Set (MulAut (Vtil V₀ V hV))) :=
      Subgroup.mem_comap.mp (hzp_le hφz_mem)
    refine (mem_preBarSub (L ⊔ D.T) V₀ V hV _).2
      ⟨Subgroup.mem_sup_left (z : ↥L).2, hLstab (z : ↥L).2, ?_⟩
    convert hcent using 2
    change actTil V₀ V hV ⟨((z : ↥L) : G), hLstab (z : ↥L).2⟩ = (φ (z : ↥L) : MulAut _)
    rfl
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hzord
  · exact hxcomm

theorem seventeen_twentyfive
    (D : Data G) (V₀ V : Subgroup G)
    (h17_24 : R17_24At D V₀ V) (h17_20 : R17_20At D V₀ V)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (hH2 : ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L),
      Gap17_25_H2 D V₀ V L c.hyp125.isElemAbelian)
    (hMax : ∀ (L : Subgroup G) (c : Ctx17_17 D V₀ V L),
      Gap17_25_max D V₀ V L c.hyp125.isElemAbelian)
    (hJ2center : K_J2_center_five) :
    R17_25At D V₀ V := by
  intro L c
  rcases h17_24 L c with h1 | h2
  · exfalso
    obtain ⟨hm3, hN, -⟩ := h17_20 L c
    have hnt : ¬ F08.Thin8 L := by
      intro ht
      have hm3' : Open.pRank 3 L = 2 := by
        rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
        exact hm3
      have h3 : Open.pRank 3 L ≤ 1 := ht 3 Nat.prime_three (by norm_num)
      rw [hm3'] at h3
      exact absurd h3 (by norm_num)
    have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ := by
      by_cases hV0 : V₀ = ⊥
      · subst hV0
        exact barSub_ne_bot_of_not_thin_bot h869 h127 c.hyp125 c.mem_calC hnt
      · exact barSub_ne_bot_of_not_thin c.hyp125 hC117 c.mem_calC hnt
    have hconj : UC22.conjClosure D.M L = L :=
      le_antisymm
        (uc22p22v_conjClosure_le ((Subgroup.normal_subgroupOf_iff_le_normalizer
          c.mem_calC.1.le).1 hN) le_rfl)
        (TwelveTwentyThree.le_conjClosure D.M L)
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      have hb : bBar (UC22.conjClosure D.M L) D.M ⊥ V c.hyp125.isElemAbelian ≤ 3 := by
        rw [hconj]; exact h1.2
      have hU : UniqueMax D.M (UC22.conjClosure D.M L) :=
        uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt
      have hle := twelve_twentyThree_one D hx h61 h126 h111 c.hyp125 rfl c.mem_calC.1
        c.mem_calC.2.2 hL1 hU
      have h7 : 7 < mBar D.M ⊥ V c.hyp125.isElemAbelian :=
        (c.hyp125.mBarGT_iff_lt_mBar 7).1 h1.1
      have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
      omega
    · have hsig : D.sig = {5} := sig_eq_five_of_J2 h17_22 h17_23 c
      obtain ⟨H₂, hTH₂, hH₂M, hidx, hbar⟩ := hH2 L c hV0 h1 (h17_23 L c) hsig
      have hsig5 : 5 ∈ D.sig := by rw [hsig]; simp
      have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC c.mem_calC
      have hsp5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
        UC6S846.sp_of_mem_sig hSg hns hsig5
      have hFS1 : WeakClosure81.InFSq 2
          (H17_25_one D V₀ V L c.hyp125.isElemAbelian) :=
        hMax L c hV0 h1 (h17_23 L c) hsig
      have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
      have h5H₂ : 5 ∣ Nat.card H₂ := by
        rw [← hidx]
        exact Subgroup.relIndex_dvd_card (H := D.T) (K := H₂)
      obtain ⟨y₀, hy₀ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H₂) 5 h5H₂
      set y : G := (y₀ : G) with hydef
      have hyH₂ : y ∈ H₂ := y₀.2
      have hyord : orderOf y = 5 := by
        rw [hydef, Subgroup.orderOf_coe, hy₀ord]
      have hyM : y ∈ D.M := hH₂M hyH₂
      have hys : y ∈ stabTil V₀ V :=
        (le_stabTil c.hyp125.pairFacts.le_normalizer c.hyp125.pairFacts.le_normalizer₀) hyM
      have hyC : actTil V₀ V c.hyp125.isElemAbelian ⟨y, hys⟩ ∈
          Subgroup.centralizer (barSub V₀ V c.hyp125.isElemAbelian L :
            Set (MulAut (Vtil V₀ V c.hyp125.isElemAbelian))) :=
        actTil_mem_centralizer_of_le_sup c.hyp125 c hMnorm hbar hyH₂ hyord hys
      have hcardH₂ : Nat.card ↥H₂ = 5 * Nat.card ↥D.T := by
        have h := Subgroup.relIndex_mul_card D.T H₂
        rw [hidx, inf_of_le_left hTH₂] at h
        exact h.symm
      have hA₀card : Nat.card ↥(Subgroup.zpowers y) = 5 := by
        rw [Nat.card_zpowers, hyord]
      have hA₀inf : Subgroup.zpowers y ⊓ D.T = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        rw [hA₀card]
        obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
      have hsupH : Subgroup.zpowers y ⊔ D.T ≤ H₂ :=
        sup_le (Subgroup.zpowers_le.mpr hyH₂) hTH₂
      have hcardsup : Nat.card ↥(Subgroup.zpowers y ⊔ D.T) ≤ 5 * Nat.card ↥D.T := by
        calc
          Nat.card ↥(Subgroup.zpowers y ⊔ D.T) ≤ Nat.card ↥H₂ :=
            Nat.card_le_card_of_injective _
              (Subgroup.inclusion_injective hsupH)
          _ = 5 * Nat.card ↥D.T := hcardH₂
      have hcardsup' : Nat.card ↥(Subgroup.zpowers y ⊔ D.T) ≤
          Nat.card ↥(Subgroup.zpowers y) * Nat.card ↥D.T := by
        rw [← hA₀card] at hcardsup
        exact hcardsup
      have hperm : Permutes (Subgroup.zpowers y) D.T :=
        CFSG.Quasithin.H.L3Wr.permute_of_card hA₀inf hcardsup'
      have hsup_eq : Subgroup.zpowers y ⊔ D.T = H₂ := by
        refine Subgroup.eq_of_le_of_card_ge hsupH ?_
        rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hA₀inf,
          hA₀card, hcardH₂]
      have hFS2 : WeakClosure81.InFSq 2 H₂ := by
        rw [← hsup_eq]
        exact TwelveTwentyTwo.inFSq_mono (by norm_num)
          (CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group
            (Subgroup.zpowers y) D.T 5 Nat.prime_five (by norm_num) hA₀card
            D.sylowM.isPGroup hperm)
      let ι : Subgroup G → ℕ := fun _ => 2
      have hι₁ : ι (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≤ 2 := le_rfl
      have hι₂ : ι H₂ ≤ 2 := le_rfl
      obtain ⟨x, hxL, hxH₁, hxord, hxy⟩ :=
        exists_five_mem_H17_25_one_commute hJ2center c.hyp125 c (h17_23 L c) hL1 hMnorm
          hyM hys hyord hyC
      let E : Subgroup G := Subgroup.closure ({x, y} : Set G)
      have hxE : x ∈ E := Subgroup.subset_closure (by simp [E])
      have hyE : y ∈ E := Subgroup.subset_closure (by simp [E])
      have hEM : E ≤ D.M := by
        refine (Subgroup.closure_le D.M).mpr ?_
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact (H17_25_one_le_M c.hyp125 c.mem_calC.1.le) hxH₁
        · exact hH₂M hyH₂
      have hE5 : IsPGroup 5 E := by
        have hcomm : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
          intro a ha b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · rfl
          · exact hxy
          · exact hxy.symm
          · rfl
        have hp : ∀ a ∈ ({x, y} : Set G), a ^ 5 = 1 := by
          intro a ha
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · rw [← hxord, pow_orderOf_eq_one]
          · rw [← hyord, pow_orderOf_eq_one]
        exact (IsElemAbelian.closure_of_commute hcomm hp).isPGroup
      have hEnc : ¬ IsCyclic ↥E :=
        not_isCyclic_closure_pair_of_J2 c.hyp125 c (h17_23 L c) hL1 hxL hxord hys hyord hyC
      have hU : UniqueMax D.M E := h61 5 hsig5 E hEM hE5 hEnc
      have hEH : E ≤ H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂ := by
        refine (Subgroup.closure_le (H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂)).mpr ?_
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Subgroup.mem_sup_left hxH₁
        · exact Subgroup.mem_sup_right hyH₂
      have hΔU : UniqueMax D.M
          (H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊔ H₂) :=
        uc22p22u_uniqueMax_mono D hEH
          (sup_le (H17_25_one_le_M c.hyp125 c.mem_calC.1.le) hH₂M) hU
      have hO2₁ : ∀ g : G, g ∉ D.M →
          ¬ twoResidual (H17_25_one D V₀ V L c.hyp125.isElemAbelian) ≤ conjSubgroup D.M g := by
        refine twoResidual_not_le_conjSubgroup_of_five
          (H17_25_one_le_M c.hyp125 c.mem_calC.1.le) ?_ hsp5
        have h := Subgroup.orderOf_dvd_natCard
          (H17_25_one D V₀ V L c.hyp125.isElemAbelian) hxH₁
        rwa [hxord] at h
      have hO2₂ := twoResidual_not_le_conjSubgroup_of_five hH₂M h5H₂ hsp5
      classical
      set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian
      set Δ : Finset (Subgroup G) := {H₁, H₂}
      have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
        intro H hH
        simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl
        · exact ⟨T_le_H17_25_one c.hyp125,
            H17_25_one_le_M c.hyp125 c.mem_calC.1.le⟩
        · exact ⟨hTH₂, hH₂M⟩
      have hι : ∀ H ∈ Δ, WeakClosure81.InFSq (ι H) H := by
        intro H hH
        simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl
        · exact hFS1
        · exact hFS2
      have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
        intro H hH
        simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl
        · exact hO2₁
        · exact hO2₂
      have hsupeq : (⨆ H ∈ Δ, H) = H₁ ⊔ H₂ := by
        refine le_antisymm (iSup₂_le fun H hH => ?_) ?_
        · simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
          rcases hH with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · exact sup_le (le_iSup₂_of_le H₁ (by simp [Δ]) le_rfl)
            (le_iSup₂_of_le H₂ (by simp [Δ]) le_rfl)
      have hsup : Δ.sup ι ≤ 2 := by
        refine Finset.sup_le fun H hH => ?_
        simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl
        · exact hι₁
        · exact hι₂
      have hle := twelve_twentyThree_three D hx h61 h127 h1114 h162 hTor h1482 h126
        c.hyp125 hV0 c.mem_calC.1 c.mem_calC.2.2 hL1 hΔ (hsupeq ▸ hΔU) ι hι hO2
      rw [hconj] at hle
      have hb : bBar L D.M V₀ V c.hyp125.isElemAbelian ≤ 3 := h1.2
      have h7 : 7 < mBar D.M V₀ V c.hyp125.isElemAbelian :=
        (c.hyp125.mBarGT_iff_lt_mBar 7).1 h1.1
      have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
      omega
  · exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
