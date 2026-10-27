module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rck_coreCommAt_of_weakK1At {X : Type} [Group X] [Finite X] {J V : Subgroup X} {r : X}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) (hrV : r ∈ V) (hVJ : V ≤ J)
    (hV : IsElemAbelian 2 V) (hK1 : WeakK1At J V r) : CoreCommAt J V r := by
  set H : Subgroup X := J ⊓ Subgroup.centralizer ({r} : Set X) with hHdef
  set Y : Subgroup X := pCoreOf 2 H with hYdef
  have hYleH : Y ≤ H := GGRootNorm.pCoreOf_le H
  have hYJ : Y ≤ J := hYleH.trans inf_le_left
  have hYC : Y ≤ Subgroup.centralizer ({r} : Set X) := hYleH.trans inf_le_right
  have hVH : V ≤ H := by
    refine le_inf hVJ ?_
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext_iff.mp (hV.1.is_comm.comm ⟨v, hv⟩ ⟨r, hrV⟩))
  have hNY : H ≤ Subgroup.normalizer (Y : Set X) := GGRootNorm.le_normalizer_pCoreOf H
  intro v hv y hy
  obtain ⟨k, z, hzC, heq⟩ := hK1 Y (GGRootNorm.isPGroup_pCoreOf H)
    (hYJ.trans Subgroup.le_normalizer) hYC
    (fun c hcJ hcr => hNY (Subgroup.mem_inf.mpr
      ⟨hcJ, Subgroup.mem_centralizer_singleton_iff.mpr hcr⟩)) v hv y hy
  set c : X := r ^ k * z with hcdef
  have hconj : v * y * v⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hNY (hVH hv)) y).mp hy
  have hcY : c ∈ Y := by
    rw [← heq]
    exact Y.mul_mem hconj (Y.inv_mem hy)
  have hrkJ : r ^ k ∈ J := J.zpow_mem (hVJ hrV) k
  have hzc : z = (r ^ k)⁻¹ * c := by rw [hcdef]; group
  have hzJ : z ∈ J := by
    rw [hzc]
    exact J.mul_mem (J.inv_mem hrkJ) (hYJ hcY)
  have hzcenter : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hzC (g : X) g.2
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (GGRootNorm.isPGroup_pCoreOf H)) ⟨c, hcY⟩
  have hm' : orderOf c = 2 ^ m := by
    rw [← Subgroup.orderOf_mk c hcY]
    exact hm
  have hcn : c ^ 2 ^ (max m 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hm']; exact pow_dvd_pow 2 (le_max_left m 1))
  have hrkn : (r ^ k) ^ 2 ^ (max m 1) = 1 := by
    have h2 : (r ^ k) ^ 2 = 1 := hV.2 (r ^ k) (V.zpow_mem hrV k)
    have hdvd : orderOf (r ^ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans (dvd_pow_self 2 (by omega)))
  have hcz : Commute (r ^ k) z := hzC (r ^ k) hrkJ
  have hczc : Commute (r ^ k) c := by
    rw [hcdef]
    exact (Commute.refl (r ^ k)).mul_right hcz
  have hzn : z ^ 2 ^ (max m 1) = 1 := by
    rw [hzc, (hczc.inv_left).mul_pow, inv_pow, hrkn, inv_one, hcn, mul_one]
  have hzn' : (⟨z, hzJ⟩ : ↥J) ^ 2 ^ (max m 1) = 1 := by
    apply Subtype.ext
    simpa using hzn
  have hdvd2 : orderOf (⟨z, hzJ⟩ : ↥J) ∣ 2 ^ (max m 1) := orderOf_dvd_iff_pow_eq_one.2 hzn'
  have hdvdZ : orderOf (⟨z, hzJ⟩ : ↥J) ∣ Nat.card (Subgroup.center ↥J) :=
    Subgroup.orderOf_dvd_natCard _ hzcenter
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥J)) (2 ^ (max m 1)) :=
    hZ.coprime_two_right.pow_right _
  have hz1' : (⟨z, hzJ⟩ : ↥J) = 1 := by
    have h1 : orderOf (⟨z, hzJ⟩ : ↥J) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hdvdZ hdvd2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hz1 : z = 1 := congrArg Subtype.val hz1'
  rw [heq, hcdef, hz1, mul_one]
  exact Subgroup.zpow_mem_zpowers r k

theorem rckRowK2_IIp_of
    (hRec : RCKIIpRecognition) (hSL : RCKIIpSLFourBridge) (hOm : RCKIIpOmegaSixBridge)
    (hOrth : RCKOrthPointK2) (hFlag : RCKK2FlagRootSub) :
    RCKRowK2 .IIp (RCKPosCent 96) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  intro e heD hene K hKcomp hJK hOddK
  have hrne : r ≠ 1 := by
    intro h
    exact hK1.2.1 (by rw [← hr_eq, h, map_one])
  have hrneX : (r : X) ≠ 1 := by
    intro h
    exact hrne (Subtype.ext (by simpa using h))
  have hFour : FourAt J V (r : X) := ⟨hrV, hVJ, hVab, hVcard, hrneX, hConj⟩
  have hCore : CoreCommAt J V (r : X) := rck_coreCommAt_of_weakK1At hOddCenJ hrV hVJ hVab hK1'
  have hCent : Cent96At J (r : X) := ⟨r, rfl, by rw [hr_eq]; exact hPos⟩
  rcases hRec X t n f ψ p G₀ A B₁ D J L hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard
      hAnorm hMarkG hB1norm hB1cap hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ
      hLG0 hExists hNotCent hCompL hNoA6 e heD hene K hKcomp hJK hOddK with hKJ | hSLe | hOme
  · subst hKJ
    exact rck_K2_self hOddCenJ hrV hVJ hVab hVcard hK1'
  · exact (hFlag X K V (hSL X K J V (r : X) hOddCenJ hOddK hFour hCore hCent hSLe) (r : X) hrV
      hrneX).trans (Subgroup.centralizer_le_normalizer (V : Set X))
  · exact hOrth X K V (r : X) hOddK (hOm X K J V (r : X) hOddCenJ hOddK hFour hCore hCent hOme)

end CFSG.StandardType.RCKC1
