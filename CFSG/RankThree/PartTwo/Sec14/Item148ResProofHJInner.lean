module

public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Res148 Main148

theorem three_dvd_card_of_ydType148 {G : Type} [Group G] [Finite G] {d : G} {Yd : Subgroup G}
    (h : YdType148 d Yd) : 3 ∣ Nat.card Yd := by
  refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Yd))
  rcases h with ⟨⟨φ⟩⟩ | ⟨hc, -⟩ | ⟨-, hc, -⟩
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num
  · have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd))
    rwa [hc] at h
  · have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd))
    rwa [hc] at h

section Certificates

@[expose] def Step148HJTypeJOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd →
        A ≤ Subgroup.normalizer (Yd : Set G) → YdType148 d Yd →
      ∀ J ∈ thetaComponentsIn Y, Yd ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        3 ∣ Nat.card J → d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
      letI := ker148_normal hY.2
      (Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) ∨
        (Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y)

theorem step148HJTypeJ_of_outer (hO : Step148HJTypeJOuter) : Step148HJTypeJ := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd hYdt J
    hJ hYdJ hAJ
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 hYdt
  have h3J : 3 ∣ Nat.card J := h3Yd.trans (Subgroup.card_dvd_of_le hYdJ)
  by_cases hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)
  swap
  · exact hO G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd hYdt J
      hJ hYdJ hAJ h3J hdc
  left
  have hYdYC : Yd ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) := le_of_mem_thetaComponentsIn hYd
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYde : Yd ≤ Subgroup.centralizer {d} := hYdYC.trans inf_le_right
  have hYdp : Group.IsPerfect Yd := isPerfect_of_mem_thetaComponentsIn hYd
  have hYdq : IsQuasisimple (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd
  have hYdαp : Group.IsPerfect ↥(img148 A Y Yd) := isPerfect_img148 hYdM
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hJc : img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y d hd} := by
    intro x hx
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hdc.2 j hjJ
    have hdM : d ∈ Y ⊔ A := Subgroup.mem_sup_right hd
    have hmem : d * j * d⁻¹ * j⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hdM hjM) ((Y ⊔ A).inv_mem hdM))
        ((Y ⊔ A).inv_mem hjM)
    have h2 := (mk'_ker148_eq_one_iff (A := A) (Y := Y) (g := ⟨_, hmem⟩)).mpr h1
    have h3 : alpha148 A Y d hd * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
        (alpha148 A Y d hd)⁻¹ * (QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩)⁻¹ = 1 := by
      rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hCJ := img148_inf_centralizer_alpha148 hY.2 hJM hAJ hd (hA3 d hd)
  rw [inf_eq_left.mpr hJc] at hCJ
  have hYdsubJ : (Yd.subgroupOf (J ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hYd).2.2.1
    have hle' : J ⊓ Subgroup.centralizer {d} ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle')
    have heq : (Yd.subgroupOf (Y ⊓ Subgroup.centralizer ({d} : Set G))).comap
        (Subgroup.inclusion hle') = Yd.subgroupOf (J ⊓ Subgroup.centralizer {d}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hYdsub : ((img148 A Y Yd).subgroupOf (img148 A Y J)).IsSubnormal := by
    rw [hCJ]
    exact isSubnormal_img148 (le_inf hYdJ hYde) (inf_le_left.trans hJM) hYdsubJ
  set ψ : ↥Yd →* ↥(img148 A Y Yd) :=
    (MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hYdM)).toMonoidHom.comp
      (phi148 (A := A) (Y := Y) hYdM).rangeRestrict with hψ
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨w, hw⟩ := (phi148 (A := A) (Y := Y) hYdM).rangeRestrict_surjective
      ((MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hYdM)).symm z)
    refine ⟨w, ?_⟩
    rw [hψ, MonoidHom.comp_apply, hw, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hψker : ψ.ker = (phi148 (A := A) (Y := Y) hYdM).ker := by
    ext k
    simp only [hψ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff _ (MulEquiv.injective _), ← Subtype.coe_inj]
    rfl
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [hψker]
    exact not_three_dvd_card_ker_phi148 hYdM
  have hYdα1 : Nontrivial ↥(img148 A Y Yd) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hker3
    have htop : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      intro k _
      exact Subsingleton.elim _ _
    rw [htop, Subgroup.card_top]
    exact h3Yd
  have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 ↥Yd := by
    rcases ker_le_theta_or_subsingleton ψ hψs hYdαp hYdq hker3 with hle' | hsub
    · exact hle'
    · exact absurd hsub (not_subsingleton_iff_nontrivial.mpr hYdα1)
  obtain ⟨-, ⟨η⟩⟩ := theta_quot_of_ker_le ψ hψs hkerθ hker3
  have hYdJα : img148 A Y Yd = img148 A Y J :=
    eq_of_le_of_isSubnormal_of_isQuasisimple (img148_mono hYdJ) hJq hYdαp hYdα1 hYdsub
  have hθYdα : aschbacherSolvableCore 3 ↥(img148 A Y Yd) = ⊥ := by
    rw [hYdJα]
    exact hJθ
  set ε : ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J) :=
    (η.trans ((QuotientGroup.quotientMulEquivOfEq hθYdα).trans QuotientGroup.quotientBot)).trans
      (MulEquiv.subgroupCongr hYdJα) with hε
  rcases hYdt with ⟨⟨φ⟩⟩ | htc | ⟨-, htc⟩
  · exact Or.inl ⟨ε.symm.trans φ⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl (KFacts.KS14.isTripleCover_congr ε htc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (KFacts.KS14.isTripleCover_congr ε htc))))

end Certificates

end CFSG.RankThree.PartTwo.Sec14
