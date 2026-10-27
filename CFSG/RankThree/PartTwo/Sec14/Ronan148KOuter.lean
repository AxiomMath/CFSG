module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KDefs
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeC
import CFSG.RankThree.PartTwo.Sec14.Ronan148KPoint
import CFSG.RankThree.PartTwo.Sec14.Ronan148KTypes
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofTheta
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open Res148 Main148 Res2

theorem step148KThetaOuter_of_typed (hKF : KF148ThetaTyped) (h41 : Sec4.Item4_1LargePrime)
    (hGW : Sec6.GWLBalanceStatement) (hKHJ : Step148KThetaHJ) (hKL3 : Step148KThetaL3) (hKA7 : Step148KThetaA7)
    (hKM22 : Step148KThetaM22) (hKM12 : Step148KThetaM12) (hKON : Step148KThetaON) :
    Step148KThetaOuter := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP J hJ hKJ hAJ h3J hc
  let := ker148_normal hY.2
  have hT : Hyp429In148 := hyp429In148_of h41
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hB : IsHyperplane A B := hP.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have he : e ∈ A := hB.1 hP.2.2.2.1
  have hK := hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hKYe : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKM : K ≤ Y ⊔ A := hKJ.trans hJM
  have hKe : K ≤ Subgroup.centralizer {e} := hKYe.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hKtype : Type148 (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    type148_of_point hKHJ hKL3 hKA7 hKM22 hKM12 hKON h hY hs hYB hP
  set ψ : ↥K →* ↥(img148 A Y K) :=
    (MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hKM)).toMonoidHom.comp
      (phi148 (A := A) (Y := Y) hKM).rangeRestrict with hψ
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨w, hw⟩ := (phi148 (A := A) (Y := Y) hKM).rangeRestrict_surjective
      ((MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hKM)).symm z)
    refine ⟨w, ?_⟩
    rw [hψ, MonoidHom.comp_apply, hw, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hψker : ψ.ker = (phi148 (A := A) (Y := Y) hKM).ker := by
    ext k
    simp only [hψ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff _ (MulEquiv.injective _), ← Subtype.coe_inj]
    rfl
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [hψker]
    exact not_three_dvd_card_ker_phi148 hKM
  have hθK : inSubgroup (aschbacherSolvableCore 3) K ≤ K := Subgroup.map_subtype_le _
  rcases ker_le_theta_or_subsingleton ψ hψs hKαp hKq hker3 with hle | hsub
  swap
  ·
    refine hθK.trans fun k hk => ?_
    have h1 : ψ ⟨k, hk⟩ = 1 := Subsingleton.elim _ _
    have h2 : phi148 (A := A) (Y := Y) hKM ⟨k, hk⟩ = 1 := by
      have : (⟨k, hk⟩ : ↥K) ∈ ψ.ker := h1
      rw [hψker] at this
      exact this
    exact (phi148_eq_one_iff hKM ⟨k, hk⟩).mp h2
  obtain ⟨hθeq, ⟨η⟩⟩ := theta_quot_of_ker_le ψ hψs hle hker3
  have hKαtype : Type148 (↥(img148 A Y K) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y K)) :=
    type148_of_mulEquiv η.symm hKtype
  have h3Kα : 3 ∣ Nat.card ↥(img148 A Y K) :=
    (three_dvd_card_of_type148 hKαtype).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hT G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hAC : img148 A Y A ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_right
  have hLC : img148 A Y J ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_left
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hJc : ¬ img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y e he} := by
    intro hJc
    apply hc
    refine ⟨he, fun j hj => ?_⟩
    have hjM : j ∈ Y ⊔ A := hJM hj
    have hjα : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ ∈ img148 A Y J :=
      mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hJc hjα)
    have heM : e ∈ Y ⊔ A := Subgroup.mem_sup_right he
    have hmem : e * j * e⁻¹ * j⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem heM hjM) ((Y ⊔ A).inv_mem heM))
        ((Y ⊔ A).inv_mem hjM)
    refine (mk'_ker148_eq_one_iff (A := A) (Y := Y) (g := ⟨_, hmem⟩)).mp ?_
    have h1 : QuotientGroup.mk' (ker148 A Y) ⟨e * j * e⁻¹ * j⁻¹, hmem⟩ =
        alpha148 A Y e he * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
          (alpha148 A Y e he)⁻¹ * (QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩)⁻¹ := by
      rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [h1, ← hcomm, mul_inv_cancel_right, mul_inv_cancel]
  have hCJ := img148_inf_centralizer_alpha148 hY.2 hJM hAJ he (hA3 e he)
  have hKL : img148 A Y K ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he} := by
    rw [hCJ]
    exact img148_mono (le_inf hKJ hKe)
  have hKsubJ : (K.subgroupOf (J ⊓ Subgroup.centralizer {e})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hK).2.2.1
    have hle' : J ⊓ Subgroup.centralizer {e} ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle')
    have heq : (K.subgroupOf (Y ⊓ Subgroup.centralizer ({e} : Set G))).comap
        (Subgroup.inclusion hle') = K.subgroupOf (J ⊓ Subgroup.centralizer {e}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hKsub : ((img148 A Y K).subgroupOf
      (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he})).IsSubnormal := by
    rw [hCJ]
    exact isSubnormal_img148 (le_inf hKJ hKe) (inf_le_left.trans hJM) hKsubJ
  have hKαq : IsQuasisimple (↥(img148 A Y K) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y K)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv η hKq
  have hKmem : img148 A Y K ∈
      thetaComponentsIn (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y e he}) :=
    Sec6.mem_thetaComponentsIn_of hKL hKαp hKsub hKαq
  have hcent : Subgroup.zpowers (alpha148 A Y e he) =
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have h3K : 3 ∣ Nat.card K := h3Kα.trans (card_img148_dvd hKM)
    have hsec := sectionCentralizer_eq_zpowers148 hA hY.2 hYB he he1 hKYe hKΔ h3K
    exact (img148_inf_centralizer_eq (A := A) (Y := Y) (J := K) hKM he hKe hsec rfl).symm
  have hθZ : aschbacherSolvableCore 3 ↥(img148 A Y K) ≤ Subgroup.center ↥(img148 A Y K) := by
    have h3K : 3 ∣ Nat.card K := h3Kα.trans (card_img148_dvd hKM)
    have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
    have hMtop : Y ⊔ A ≠ ⊤ := by
      intro htop
      have : IsSimpleGroup G := h.isSimpleGroup
      have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
      rcases hYn.eq_bot_or_eq_top with hY1 | hYt
      · apply hs
        rw [hY1]
        infer_instance
      · exact hY.1 hYt
    have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
    have hYnorm : (Y.subgroupOf (Y ⊔ A)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMN
    have hJsn : (J.subgroupOf (Y ⊔ A)).IsSubnormal :=
      isSubnormal_subgroupOf_trans148 hJY le_sup_left (mem_thetaComponentsIn_iff.mp hJ).2.2.1
        hYnorm.isSubnormal
    have hJYA : J ∈ thetaComponentsIn (Y ⊔ A) :=
      Sec6.mem_thetaComponentsIn_of hJM (isPerfect_of_mem_thetaComponentsIn hJ) hJsn
        (Sec6.isQuasisimple_of_mem_thetaComponentsIn hJ)
    have hb := Sec6.bThreeProperty_of_three_dvd hGW hM4 hJYA (Subgroup.mem_sup_right he)
      (hA3 e he) (le_inf hKJ hKe) hKp hKsubJ hKq h3K
    have hθJ : inSubgroup (aschbacherSolvableCore 3) J ≤ pPrimeCoreOf 3 Y := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn hJ]
      exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf Y)
    exact theta_le_center_img148 hKM ψ hψs hψker hθeq (hb.trans hθJ)
  have hθKα := hKF _ (img148 A Y (J ⊔ A)) hC4 hCθ hCE (img148 A Y A) (img148 A Y J)
    (img148 A Y K) (alpha148 A Y e he) hAC hLC (img148_isE27 hA) (alpha148_mem_img148 he)
    (alpha148_ne_one he he1 (hA3 e he)) hJq hLn hJc hKmem (img148_le_normalizer hAK) hcent hθZ
    hKαtype
  rw [hθeq, Subgroup.map_eq_bot_iff] at hθKα
  rintro _ ⟨t, ht, rfl⟩
  have h1 : ψ t = 1 := hθKα ht
  have h2 : phi148 (A := A) (Y := Y) hKM t = 1 := by
    have : t ∈ ψ.ker := h1
    rw [hψker] at this
    exact this
  exact (phi148_eq_one_iff hKM t).mp h2

theorem step148KTheta_of_typed (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement) (hKF : KF148ThetaTyped)
    (hKHJ : Step148KThetaHJ) (hKL3 : Step148KThetaL3) (hKA7 : Step148KThetaA7)
    (hKM22 : Step148KThetaM22) (hKM12 : Step148KThetaM12) (hKON : Step148KThetaON) :
    Step148KTheta :=
  step148KTheta_of_outer h45 h48
    (step148KThetaOuter_of_typed hKF h41 hGW hKHJ hKL3 hKA7 hKM22 hKM12 hKON)

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
