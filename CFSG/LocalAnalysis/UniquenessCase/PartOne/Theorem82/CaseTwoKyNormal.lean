module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.UC6K46Mult
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G}

namespace CaseTwoTransitive

variable (t : CaseTwoTransitive c)

private theorem K_eq_pCoreOf (i : Fin 3) :
    t.d.K i = CFSG.Open.pCoreOf 2 (t.d.Lf i) := by
  refine le_antisymm ?_ ?_
  · exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (t.d.hLM i)
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 (t.d.Lf i)) ?_
    have hsub : CFSG.Open.IsSubnormal (t.d.Lf i) t.d.M := by
      rw [t.hdM]
      exact (t.hcomp i).2.1
    exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub

private theorem phi_ker_eq_pCore (i : Fin 3) :
    (t.d.phi i).ker = CFSG.pCore 2 ↥(t.d.Lf i) := by
  rw [t.d.phi_ker i, K_eq_pCoreOf t i, CFSG.openPCoreOf_subgroupOf]

private noncomputable def eLb (i : Fin 3) :
    (↥(t.d.Lf i) ⧸ CFSG.pCore 2 ↥(t.d.Lf i)) ≃* ↥(t.d.Lb i) :=
  (QuotientGroup.quotientMulEquivOfEq (phi_ker_eq_pCore t i)).symm.trans
    (QuotientGroup.quotientKerEquivRange (t.d.phi i))

private theorem isQuasisimple_Lb (i : Fin 3) :
    CFSG.Open.IsQuasisimple ↥(t.d.Lb i) :=
  (CFSG.Open.IsQuasisimple.congr (eLb t i)).mp (t.hcomp i).2.2.2.2

theorem center_Lb_eq_bot (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) (i : Fin 3) :
    Subgroup.center ↥(t.d.Lb i) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hqsOpen : CFSG.Open.IsQuasisimple ↥(t.d.Lb i) := isQuasisimple_Lb t i
  have hqs : CFSG.IsQuasisimple ↥(t.d.Lb i) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hqsOpen
  have hcoreLb : CFSG.pCore 2 ↥(t.d.Lb i) = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 (eLb t i)
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hZL : ¬ 3 ∣ Nat.card (Subgroup.center ↥(t.d.Lb i)) :=
    SylowThreeData.three_not_dvd_center_Lb t.d i
  have hodd : Odd (Nat.card (Subgroup.center ↥(t.d.Lb i))) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨z, hzord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(t.d.Lb i))) 2 h2
    have hzord' : orderOf ((z : Subgroup.center ↥(t.d.Lb i)) : ↥(t.d.Lb i)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hzord
    have hzmem : ((z : Subgroup.center ↥(t.d.Lb i)) : ↥(t.d.Lb i)) ∈
        CFSG.pCore 2 ↥(t.d.Lb i) := by
      refine Subgroup.mem_sSup_of_mem ?_ (Subgroup.mem_zpowers _)
      refine ⟨?_, ?_⟩
      · refine ⟨fun x hx g => ?_⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hc : Commute g ((z : Subgroup.center ↥(t.d.Lb i)) : ↥(t.d.Lb i)) :=
          Subgroup.mem_center_iff.mp z.2 g
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
          rw [(hc.zpow_right k).eq, mul_inv_cancel_right]⟩
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hzord', pow_one]
    rw [hcoreLb, Subgroup.mem_bot] at hzmem
    have hz1 : ((z : Subgroup.center ↥(t.d.Lb i)) : ↥(t.d.Lb i)) = 1 := hzmem
    rw [← orderOf_eq_one_iff] at hz1
    rw [hzord'] at hz1
    exact absurd hz1 (by norm_num)
  have hne : t.d.Lf i ≠ ⊤ := by
    intro htop
    exact c.M_ne_top (t.hdM ▸ top_le_iff.mp (htop ▸ t.d.hLM i))
  have hKLi : CFSG.Open.IsKGroup ↥(t.d.Lf i) :=
    c.standing.kProper.isKGroup (t.d.Lf i) hne
  have hKX : CFSG.Open.IsKGroup
      (↥(t.d.Lf i) ⧸ CFSG.pCore 2 ↥(t.d.Lf i)) :=
    hKLi.quotient _
  have hKLb : CFSG.Open.IsKGroup ↥(t.d.Lb i) :=
    hKX.of_surjective (eLb t i).toMonoidHom (MulEquiv.surjective _)
  have hKQ : CFSG.Open.IsKGroup
      (↥(t.d.Lb i) ⧸ Subgroup.center ↥(t.d.Lb i)) :=
    hKLb.quotient _
  have hrankQ : CFSG.Open.pRank 3
      (⊤ : Subgroup (↥(t.d.Lb i) ⧸ Subgroup.center ↥(t.d.Lb i))) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    have h1 : CFSG.pRank 3 (↥(t.d.Lb i) ⧸ Subgroup.center ↥(t.d.Lb i)) =
        CFSG.pRank 3 ↥(t.d.Lb i) :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
        hZL
    rw [h1, CFSG.SectionRank.pRank_coe_eq_openPRank,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (t.d.Lb i)]
    exact t.d.pRank_Lb i
  have hlist := hK32 _ hKQ hqsOpen.2 hqs.2.2 hrankQ
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.center_eq_bot_of_catalog hGA hSp hqs hodd hZL
    hlist

private theorem Lf_le_M (i : Fin 3) : t.d.Lf i ≤ M t := by
  rw [show M t = t.d.M from t.hdM.symm]
  exact t.d.hLM i

private noncomputable def gHat (i : Fin 3) : ↥(t.d.Lf i) →* Mb t :=
  (qmk t).comp (Subgroup.inclusion (Lf_le_M t i))

private theorem gHat_range (i : Fin 3) : (gHat t i).range = Lhat t i := by
  rw [gHat, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

private theorem gHat_ker (i : Fin 3) :
    (gHat t i).ker = (t.d.K i).subgroupOf (t.d.Lf i) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hK : (⟨x.1, Lf_le_M t i x.2⟩ : ↥(M t)) ∈ Kq t :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact Subgroup.mem_subgroupOf.mpr
      ⟨x.2, (Subgroup.mem_subgroupOf.mp hK).2⟩
  · intro hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨t.hdL ▸ t.d.Lf_le_L i x.2, (Subgroup.mem_subgroupOf.mp hx).2⟩))

private theorem gHat_ker_eq_phi_ker (i : Fin 3) :
    (gHat t i).ker = (t.d.phi i).ker := by
  rw [gHat_ker, ← t.d.phi_ker i]

private noncomputable def eLhatLb (i : Fin 3) : ↥(Lhat t i) ≃* ↥(t.d.Lb i) :=
  (MulEquiv.subgroupCongr (gHat_range t i).symm).trans
    ((QuotientGroup.quotientKerEquivRange (gHat t i)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (gHat_ker_eq_phi_ker t i)).trans
        (QuotientGroup.quotientKerEquivRange (t.d.phi i))))

private theorem center_Lhat_eq_bot (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) (i : Fin 3) :
    Subgroup.center ↥(Lhat t i) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzimg : eLhatLb t i z ∈ Subgroup.center ↥(t.d.Lb i) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨u, rfl⟩ := (eLhatLb t i).surjective w
    rw [← map_mul, ← map_mul, (hz u).symm]
  have hz1 : eLhatLb t i z = 1 := by
    have h : eLhatLb t i z ∈ (⊥ : Subgroup ↥(t.d.Lb i)) := by
      rw [← center_Lb_eq_bot t hK32 hGA hSp i]
      exact hzimg
    simpa using h
  rw [Subgroup.mem_bot]
  exact (eLhatLb t i).injective (hz1.trans (map_one _).symm)

private theorem isSimpleGroup_Lb (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) (i : Fin 3) :
    IsSimpleGroup ↥(t.d.Lb i) := by
  have e : (↥(t.d.Lb i) ⧸ Subgroup.center ↥(t.d.Lb i)) ≃* ↥(t.d.Lb i) :=
    (QuotientGroup.quotientMulEquivOfEq (center_Lb_eq_bot t hK32 hGA hSp i)).trans
      (QuotientGroup.quotientBot (G := ↥(t.d.Lb i)))
  exact e.isSimpleGroup_congr.mp (isQuasisimple_Lb t i).2

private theorem isSimpleGroup_Lhat_zero (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    IsSimpleGroup ↥(Lhat t 0) :=
  (eLhatLb t 0).isSimpleGroup_congr.mpr (isSimpleGroup_Lb t hK32 hGA hSp 0)

private theorem muL_ker_le_center :
    (muL t).ker ≤ Subgroup.center ((↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2)) := by
  intro y hy
  set a : ↥(Lhat t 0) := y.1.1 with ha
  set b : ↥(Lhat t 1) := y.1.2 with hb
  set e : ↥(Lhat t 2) := y.2 with he
  have habc : (a : Mb t) * b * e = 1 := by
    rw [MonoidHom.mem_ker] at hy
    rw [muL, MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply] at hy
    change (y.1.1 : Mb t) * (y.1.2 : Mb t) * (y.2 : Mb t) = 1 at hy
    rw [← ha, ← hb, ← he] at hy
    exact hy
  have ha_center : a ∈ Subgroup.center ↥(Lhat t 0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : Mb t) * (a : Mb t) = (a : Mb t) * (w : Mb t)
    have hb' : Commute (w : Mb t) (b : Mb t) :=
      Lhat_comm t 0 1 (by decide) (w : Mb t) w.2 (b : Mb t) b.2
    have he' : Commute (w : Mb t) (e : Mb t) :=
      Lhat_comm t 0 2 (by decide) (w : Mb t) w.2 (e : Mb t) e.2
    have ha_eq : (a : Mb t) = ((b : Mb t) * (e : Mb t))⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← mul_assoc]
      exact habc
    rw [ha_eq]
    exact ((hb'.mul_right he').inv_right).eq
  have hb_center : b ∈ Subgroup.center ↥(Lhat t 1) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : Mb t) * (b : Mb t) = (b : Mb t) * (w : Mb t)
    have ha' : Commute (w : Mb t) (a : Mb t) :=
      Lhat_comm t 1 0 (by decide) (w : Mb t) w.2 (a : Mb t) a.2
    have he' : Commute (w : Mb t) (e : Mb t) :=
      Lhat_comm t 1 2 (by decide) (w : Mb t) w.2 (e : Mb t) e.2
    have hb_eq : (b : Mb t) = (a : Mb t)⁻¹ * (e : Mb t)⁻¹ := by
      calc (b : Mb t) = (a : Mb t)⁻¹ * ((a : Mb t) * b * e) * (e : Mb t)⁻¹ := by group
        _ = (a : Mb t)⁻¹ * 1 * (e : Mb t)⁻¹ := by rw [habc]
        _ = (a : Mb t)⁻¹ * (e : Mb t)⁻¹ := by group
    rw [hb_eq]
    exact ((ha'.inv_right).mul_right (he'.inv_right)).eq
  have he_center : e ∈ Subgroup.center ↥(Lhat t 2) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : Mb t) * (e : Mb t) = (e : Mb t) * (w : Mb t)
    have ha' : Commute (w : Mb t) (a : Mb t) :=
      Lhat_comm t 2 0 (by decide) (w : Mb t) w.2 (a : Mb t) a.2
    have hb' : Commute (w : Mb t) (b : Mb t) :=
      Lhat_comm t 2 1 (by decide) (w : Mb t) w.2 (b : Mb t) b.2
    have he_eq : (e : Mb t) = ((a : Mb t) * (b : Mb t))⁻¹ :=
      eq_inv_of_mul_eq_one_right habc
    rw [he_eq]
    exact ((ha'.mul_right hb').inv_right).eq
  rw [Subgroup.mem_center_iff]
  intro w
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      change (w.1.1 : Mb t) * (a : Mb t) = (a : Mb t) * (w.1.1 : Mb t)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha_center w.1.1)
    · apply Subtype.ext
      change (w.1.2 : Mb t) * (b : Mb t) = (b : Mb t) * (w.1.2 : Mb t)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb_center w.1.2)
  · apply Subtype.ext
    change (w.2 : Mb t) * (e : Mb t) = (e : Mb t) * (w.2 : Mb t)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp he_center w.2)

private theorem muL_apply (a : ↥(Lhat t 0)) (b : ↥(Lhat t 1)) (c : ↥(Lhat t 2)) :
    muL t ((a, b), c) = (a : Mb t) * (b : Mb t) * (c : Mb t) := by
  erw [muL, MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply]
  rfl

private theorem muL_ker_eq_bot (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    (muL t).ker = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyc := muL_ker_le_center t hy
  set a : ↥(Lhat t 0) := y.1.1 with ha
  set b : ↥(Lhat t 1) := y.1.2 with hb
  set e : ↥(Lhat t 2) := y.2 with he
  have ha_center : a ∈ Subgroup.center ↥(Lhat t 0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h := Subgroup.mem_center_iff.mp hyc (((w, 1), 1) :
      (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2))
    exact congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) => x.1.1) h
  have hb_center : b ∈ Subgroup.center ↥(Lhat t 1) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h := Subgroup.mem_center_iff.mp hyc (((1, w), 1) :
      (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2))
    exact congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) => x.1.2) h
  have he_center : e ∈ Subgroup.center ↥(Lhat t 2) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h := Subgroup.mem_center_iff.mp hyc (((1, 1), w) :
      (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2))
    exact congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) => x.2) h
  have ha1 : a = 1 := by
    have h := ha_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 0] at h
    exact Subgroup.mem_bot.mp h
  have hb1 : b = 1 := by
    have h := hb_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 1] at h
    exact Subgroup.mem_bot.mp h
  have he1 : e = 1 := by
    have h := he_center
    rw [center_Lhat_eq_bot t hK32 hGA hSp 2] at h
    exact Subgroup.mem_bot.mp h
  exact Prod.ext (Prod.ext ha1 hb1) he1

private theorem muL_injective (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    Function.Injective (muL t) :=
  (MonoidHom.ker_eq_bot_iff (muL t)).mp (muL_ker_eq_bot t hK32 hGA hSp)

private theorem Ky_le_M : t.Ky ≤ M t :=
  (t.Ky_le.trans inf_le_left).trans c.hyp81.1

private noncomputable def phiKy : ↥t.Ky →* Mb t :=
  (qmk t).comp (Subgroup.inclusion (Ky_le_M t))

private theorem phiKy_range :
    (phiKy t).range = (t.Ky.subgroupOf (M t)).map (qmk t) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨x.1, Ky_le_M t x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hx⟩, rfl⟩

private theorem phiKy_le_centralizer :
    (phiKy t).range ≤ Subgroup.centralizer ({ybar t} : Set (Mb t)) := by
  rintro z ⟨k, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hkC : (k : G) ∈ Subgroup.centralizer ({t.y} : Set G) := (t.Ky_le k.2).2
  have hcomm : (k : G) * t.y = t.y * (k : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hkC
  change qmk t (Subgroup.inclusion (Ky_le_M t) k) * qmk t (yM t) =
    qmk t (yM t) * qmk t (Subgroup.inclusion (Ky_le_M t) k)
  rw [← map_mul, ← map_mul]
  exact congrArg (qmk t) (Subtype.ext (by
    show (k : G) * t.y = t.y * (k : G)
    simpa [yM] using hcomm))

private theorem phiKy_le_image_L :
    (phiKy t).range ≤ (c.L.subgroupOf (M t)).map (qmk t) := by
  rintro z ⟨k, rfl⟩
  exact Subgroup.mem_map.mpr
    ⟨⟨k.1, Ky_le_M t k.2⟩, (t.Ky_le k.2).1, rfl⟩

private theorem mulAut_conj_sq (x : Mb t) :
    (MulAut.conj (ybar t)) ((MulAut.conj (ybar t)) x) =
      (MulAut.conj (ybar t ^ 2)) x := by
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, pow_two]
  group

private theorem mem_delta_range_of_mem_muL_range_of_centralizes
    (hmuL : Function.Injective (muL t)) {z : Mb t}
    (hzL : z ∈ (muL t).range) (hzcent : z * ybar t = ybar t * z) :
    z ∈ (delta t).range := by
  obtain ⟨⟨⟨a, b⟩, e⟩, rfl⟩ := hzL
  have hsa : (MulAut.conj (ybar t)) (a : Mb t) ∈ Lhat t 1 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ybar t)).toMonoidHom a.2
    rw [Lhat_conj t 0] at h
    simpa using h
  have hsb : (MulAut.conj (ybar t)) (b : Mb t) ∈ Lhat t 2 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ybar t)).toMonoidHom b.2
    rw [Lhat_conj t 1] at h
    simpa using h
  have hse : (MulAut.conj (ybar t)) (e : Mb t) ∈ Lhat t 0 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ybar t)).toMonoidHom e.2
    rw [Lhat_conj t 2] at h
    simpa using h
  let a1 : ↥(Lhat t 1) := ⟨(MulAut.conj (ybar t)) (a : Mb t), hsa⟩
  let b1 : ↥(Lhat t 2) := ⟨(MulAut.conj (ybar t)) (b : Mb t), hsb⟩
  let e1 : ↥(Lhat t 0) := ⟨(MulAut.conj (ybar t)) (e : Mb t), hse⟩
  have hconj : ybar t * muL t ((a, b), e) * (ybar t)⁻¹ = muL t ((e1, a1), b1) := by
    rw [muL_apply, muL_apply]
    rw [show ybar t * ((a : Mb t) * (b : Mb t) * (e : Mb t)) * (ybar t)⁻¹ =
        ((MulAut.conj (ybar t)) (a : Mb t)) * ((MulAut.conj (ybar t)) (b : Mb t)) *
          ((MulAut.conj (ybar t)) (e : Mb t)) from by
      simp only [MulAut.conj_apply]
      group]
    have hbe : (b1 : Mb t) * (e1 : Mb t) = (e1 : Mb t) * (b1 : Mb t) :=
      Lhat_comm t 2 0 (by decide) (b1 : Mb t) b1.2 (e1 : Mb t) e1.2
    have hae : (a1 : Mb t) * (e1 : Mb t) = (e1 : Mb t) * (a1 : Mb t) :=
      Lhat_comm t 1 0 (by decide) (a1 : Mb t) a1.2 (e1 : Mb t) e1.2
    rw [show ((MulAut.conj (ybar t)) (a : Mb t)) *
          ((MulAut.conj (ybar t)) (b : Mb t)) *
          ((MulAut.conj (ybar t)) (e : Mb t)) =
        (e1 : Mb t) * (a1 : Mb t) * (b1 : Mb t) from by
      calc ((MulAut.conj (ybar t)) (a : Mb t)) *
            ((MulAut.conj (ybar t)) (b : Mb t)) *
            ((MulAut.conj (ybar t)) (e : Mb t))
          = (a1 : Mb t) * ((b1 : Mb t) * (e1 : Mb t)) := by
            rw [mul_assoc]
        _ = (a1 : Mb t) * ((e1 : Mb t) * (b1 : Mb t)) := by rw [hbe]
        _ = ((a1 : Mb t) * (e1 : Mb t)) * (b1 : Mb t) := by rw [← mul_assoc]
        _ = ((e1 : Mb t) * (a1 : Mb t)) * (b1 : Mb t) := by rw [hae]
        _ = (e1 : Mb t) * (a1 : Mb t) * (b1 : Mb t) := by rw [mul_assoc]]
  have hfixed : muL t ((a, b), e) = muL t ((e1, a1), b1) := by
    rw [← hconj, ← hzcent]
    group
  have heq := hmuL hfixed
  have haeq : a = e1 := congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) =>
    x.1.1) heq
  have hbeq : b = a1 := congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) =>
    x.1.2) heq
  have heeq : e = b1 := congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) =>
    x.2) heq
  have hbval : (b : Mb t) = (MulAut.conj (ybar t)) (a : Mb t) := by
    rw [hbeq]
  have heval : (e : Mb t) = (MulAut.conj (ybar t)) (b : Mb t) := by
    rw [show (e : Mb t) = (b1 : Mb t) from congrArg Subtype.val heeq]
  refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
  rw [delta_apply, muL_apply, hbval, heval, hbval, mulAut_conj_sq]

private theorem phiKy_range_eq_delta_range
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    (phiKy t).range = (delta t).range := by
  have hinj := muL_injective t hK32 hGA hSp
  refine le_antisymm ?_ ?_
  · intro z hz
    exact mem_delta_range_of_mem_muL_range_of_centralizes t hinj
      (by
        rw [muL_range t]
        exact phiKy_le_image_L t hz)
      (Subgroup.mem_centralizer_singleton_iff.mp (phiKy_le_centralizer t hz))
  · rw [phiKy_range t]
    exact delta_range_le_image_Ky t

private theorem delta_injective (hmuL : Function.Injective (muL t)) :
    Function.Injective (delta t) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu1 : (u : Mb t) * (MulAut.conj (ybar t)) (u : Mb t) *
      (MulAut.conj (ybar t ^ 2)) (u : Mb t) = 1 := by
    rw [MonoidHom.mem_ker, delta_apply] at hu
    exact hu
  have hsu : (MulAut.conj (ybar t)) (u : Mb t) ∈ Lhat t 1 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ybar t)).toMonoidHom u.2
    rw [Lhat_conj t 0] at h
    simpa using h
  have hsu2 : (MulAut.conj (ybar t ^ 2)) (u : Mb t) ∈ Lhat t 2 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ybar t)).toMonoidHom hsu
    rw [Lhat_conj t 1] at h
    rw [← mulAut_conj_sq t (u : Mb t)]
    simpa using h
  let u1 : ↥(Lhat t 1) := ⟨(MulAut.conj (ybar t)) (u : Mb t), hsu⟩
  let u2 : ↥(Lhat t 2) := ⟨(MulAut.conj (ybar t ^ 2)) (u : Mb t), hsu2⟩
  have hmu : muL t ((u, u1), u2) = 1 := by
    rw [muL_apply]
    exact hu1
  have htriv : muL t ((u, u1), u2) = muL t (((1 : ↥(Lhat t 0)),
      (1 : ↥(Lhat t 1))), (1 : ↥(Lhat t 2))) := by
    rw [hmu, muL_apply]
    simp
  have h := hmuL htriv
  have h1 := congrArg (fun x : (↥(Lhat t 0) × ↥(Lhat t 1)) × ↥(Lhat t 2) => x.1.1) h
  simpa using h1

private noncomputable def eDeltaKy (hmuL : Function.Injective (muL t))
    (h : (delta t).range = (phiKy t).range) :
    ↥(Lhat t 0) ≃* ↥((phiKy t).range) :=
  (MonoidHom.ofInjective (delta_injective t hmuL)).trans (MulEquiv.subgroupCongr h)

private theorem isSimpleGroup_Kyhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    IsSimpleGroup ↥((phiKy t).range) := by
  have h := phiKy_range_eq_delta_range t hK32 hGA hSp
  exact (eDeltaKy t (muL_injective t hK32 hGA hSp) h.symm).isSimpleGroup_congr.mp
    (isSimpleGroup_Lhat_zero t hK32 hGA hSp)

theorem le_N_or_eq_Ky (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    {N : Subgroup G} (hNK : N ≤ t.Ky) (hN : t.Ky ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ t.d.N ∨ N = t.Ky := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup ↥((phiKy t).range) :=
    isSimpleGroup_Kyhat t hK32 hGA hSp
  let f : ↥t.Ky →* ↥((phiKy t).range) := (phiKy t).rangeRestrict
  have hf : Function.Surjective f := (phiKy t).rangeRestrict_surjective
  have hker_le : f.ker ≤ (t.d.N ⊓ t.Ky).subgroupOf t.Ky := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hq : (phiKy t k : Mb t) = 1 := by
      have := congrArg Subtype.val hk
      simpa [f] using this
    have hK : (Subgroup.inclusion (Ky_le_M t) k) ∈ Kq t :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hK).2, k.2⟩
  have hkerP : IsPGroup 2 ↥f.ker := by
    have hN2 : IsPGroup 2 ↥(t.d.N) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.d.M
    have hNK2 : IsPGroup 2 ↥(t.d.N ⊓ t.Ky) := hN2.to_le inf_le_left
    have hsub2 : IsPGroup 2 ↥((t.d.N ⊓ t.Ky).subgroupOf t.Ky) :=
      hNK2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    exact hsub2.to_le hker_le
  have hNnormal : (N.subgroupOf t.Ky).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hN
  let N₀ : Subgroup ↥t.Ky := N.subgroupOf t.Ky
  haveI : N₀.Normal := hNnormal
  haveI : (N₀.map f).Normal := hNnormal.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map f) with hbot | htop
  · left
    intro x hx
    have hfk : f ⟨x, hNK hx⟩ = 1 := by
      have hmem : f ⟨x, hNK hx⟩ ∈ N₀.map f :=
        Subgroup.mem_map.mpr ⟨⟨x, hNK hx⟩, hx, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    have hq : (phiKy t ⟨x, hNK hx⟩ : Mb t) = 1 := by
      have := congrArg Subtype.val hfk
      simpa [f] using this
    have hK : (Subgroup.inclusion (Ky_le_M t) ⟨x, hNK hx⟩) ∈ Kq t :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact (Subgroup.mem_subgroupOf.mp hK).2
  · right
    have hquotP : IsPGroup 2 (↥t.Ky ⧸ N₀) := by
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have hb : f b ∈ N₀.map f := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.mp hb
      have hker : n⁻¹ * b ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfn]
        group
      obtain ⟨e, he⟩ := hkerP ⟨n⁻¹ * b, hker⟩
      refine ⟨e, ?_⟩
      have h1 : (QuotientGroup.mk b : ↥t.Ky ⧸ N₀) = QuotientGroup.mk (n⁻¹ * b) := by
        rw [QuotientGroup.eq]
        have hN₀norm : N₀.Normal := hNnormal
        have := hN₀norm.conj_mem n⁻¹ (N₀.inv_mem hn) b⁻¹
        simpa [mul_assoc] using this
      rw [h1, ← QuotientGroup.mk_pow]
      have h3 : (n⁻¹ * b) ^ 2 ^ e = 1 := congrArg Subtype.val he
      rw [h3, QuotientGroup.mk_one]
    obtain ⟨k, hk⟩ := hquotP.exists_card_eq
    have hindex : N₀.index = 2 ^ k := by
      rw [Subgroup.index_eq_card, hk]
    haveI : Group.IsPerfect ↥t.Ky := Subgroup.isPerfect_iff.mpr t.commutator_Ky
    have hperfTop : ⁅(⊤ : Subgroup ↥t.Ky), (⊤ : Subgroup ↥t.Ky)⁆ = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    have hle := Subgroup.le_of_commutator_eq_self_of_index_eq_prime_pow
      (G := ↥t.Ky) (M := N₀) (H := ⊤) (p := 2) (k := k) Nat.prime_two hindex hperfTop
    have hN₀top : N₀ = ⊤ := le_antisymm le_top hle
    have hKyN : t.Ky ≤ N := by
      intro x hx
      have hxN₀ : (⟨x, hx⟩ : ↥t.Ky) ∈ N₀ := by
        rw [hN₀top]
        exact Subgroup.mem_top _
      exact hxN₀
    exact le_antisymm hNK hKyN

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
