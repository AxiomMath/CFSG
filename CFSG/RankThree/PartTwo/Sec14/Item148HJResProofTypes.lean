module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofOuter
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofEps
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes148

open Res148 Main148

omit [Finite G] in
theorem mem_sectionCentralizer_of_le_centralizer {A Y J : Subgroup G} [(ker148 A Y).Normal]
    (hJM : J ≤ Y ⊔ A) {d : G} (hd : d ∈ A)
    (hJc : img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y d hd}) :
    d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
  refine ⟨hd, fun j hj => ?_⟩
  have hjM : j ∈ Y ⊔ A := hJM hj
  have hjα : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp (hJc hjα)
  have hdM : d ∈ Y ⊔ A := Subgroup.mem_sup_right hd
  have hmem : d * j * d⁻¹ * j⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hdM hjM) ((Y ⊔ A).inv_mem hdM))
      ((Y ⊔ A).inv_mem hjM)
  have h1 : QuotientGroup.mk' (ker148 A Y) (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) = 1 := by
    have e : (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) =
        ⟨d, hdM⟩ * ⟨j, hjM⟩ * (⟨d, hdM⟩)⁻¹ * (⟨j, hjM⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← alpha148_eq_mk', mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, hc']
  exact mk'_ker148_eq_one_iff.mp h1

theorem img148_eq_of_mem_sectionCentralizer {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {d : G} (hd : d ∈ A)
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (h3Yd : 3 ∣ Nat.card Yd) (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    img148 A Y Yd = img148 A Y J ∧
      Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) := by
  have h3J : 3 ∣ Nat.card J := h3Yd.trans (Subgroup.card_dvd_of_le hYdJ)
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
  have hCJ := img148_inf_centralizer_alpha148 hAY hJM hAJ hd (hA3 d hd)
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
  refine ⟨hYdJα, ⟨?_⟩⟩
  exact (η.trans ((QuotientGroup.quotientMulEquivOfEq hθYdα).trans QuotientGroup.quotientBot)).trans
    (MulEquiv.subgroupCongr hYdJα)

omit [Finite G] in
theorem card_of_ydType148 {d : G} {Yd : Subgroup G}
    (h : YdType148 d Yd) :
    Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 60 ∨
      Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 1080 ∨
      Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 3 * 460815505920 := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨hc, ⟨e⟩⟩ | ⟨-, hc, ⟨e⟩⟩
  · left
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  · right; left
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)), Nat.card_congr e.toEquiv, hc,
      KFacts.KS14.card_alternatingGroup_six]
  · right; right
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)), Nat.card_congr e.toEquiv, hc,
      CFSG.Sporadic.ON.card_ON_eq]

theorem card_img148_yd_of_a6 {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {d : G} (hd : d ∈ A) (hd3 : d ^ 3 = 1)
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y) :
    1080 ≤ Nat.card ↥(img148 A Y Yd) ∧
      img148 A Y Yd ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hd} := by
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
  obtain ⟨hKle, -, -, -, ⟨η⟩⟩ := ydAlpha_facts hAY hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have h1080 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 1080 := by
    obtain ⟨hc, ⟨e⟩⟩ := hA6
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)), Nat.card_congr e.toEquiv, hc,
      KFacts.KS14.card_alternatingGroup_six]
  have hdvd : 1080 ∣ Nat.card ↥(img148 A Y Yd) := by
    rw [← h1080, Nat.card_congr η.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact ⟨Nat.le_of_dvd Nat.card_pos hdvd, hKle⟩

end HJRes148

open HJRes148 Main148

section Certificates

theorem HJRes148.jalpha_config
    (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h134 : Item134) (h427 : Sec4.Item4_27)
    (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime) (hTYd : Step148HJTypeYd)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y) {B : Subgroup G}
    (hB : IsHyperplane A B) (hnot : ¬ YBOne A (lB A) Y B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hΔ : deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB)
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hYBJ : YB ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    letI := ker148_normal hY.2
    ∃ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd ∧ Yd ≤ J ∧
      A ≤ Subgroup.normalizer (Yd : Set G) ∧ YdType148 d Yd ∧ 3 ∣ Nat.card J ∧
      ((d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ∧
          img148 A Y Yd = img148 A Y J ∧
          Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J))) ∨
        (d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ∧
          Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) ∧
          ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y ∧
          Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer (Subgroup.zpowers d : Set G))) := by
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA3 d hd
  obtain ⟨Yd, hYd, hYBYd, hAYd, J', hJ', hYdJ', -⟩ := exists_yd_j148 h45 h48 h hY hB hYB hc
  have hYB1 : YB ≠ ⊥ := by
    have : Nontrivial (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) :=
      CFSG.LocalCores.isQuasisimple_nontrivial (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
    have : Nontrivial ↥YB :=
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥YB)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot YB).mp this
  have hJJ' : J' = J := Sec6.eq_of_mem_thetaComponentsIn_of_le hJ' hJ
    (isPerfect_of_mem_thetaComponentsIn hYB) hYB1 (hYBYd.trans hYdJ') hYBJ
  rw [hJJ'] at hYdJ'
  have hYdt := hTYd G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd
    J hJ hYdJ' hAJ
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 hYdt
  have h3J : 3 ∣ Nat.card J := h3Yd.trans (Subgroup.card_dvd_of_le hYdJ')
  refine ⟨Yd, hYd, hYBYd, hYdJ', hAYd, hYdt, h3J, ?_⟩
  by_cases hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)
  · exact Or.inl ⟨hdc, img148_eq_of_mem_sectionCentralizer hY.2 hA3 hd hYd hJ hYdJ' hAJ h3Yd hdc⟩
  right
  have hW := normalizer_le_normalizer_zpowers_d h134 h48 h hB hc
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · apply hs
      rw [hY1]
      infer_instance
    · exact hY.1 hYt
  have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hθ := theta_commutator_le hGW hY.2 hM4 hd hd3 hYd hJ hYdJ' h3Yd
  rcases hYdt with hA5 | hA6 | ⟨hdYd, hON⟩
  · exact (false_of_outer_a5_on h427 h41 h hY hs hd hd1 hW hYd hJ hYdJ' hAJ h3J h3Yd hθ
      (Or.inl hA5) hdc).elim
  · exact ⟨hdc, hA6, hθ, hW⟩
  · exact (false_of_outer_a5_on h427 h41 h hY hs hd hd1 hW hYd hJ hYdJ' hAJ h3J h3Yd hθ
      (Or.inr ⟨hdYd, hON⟩) hdc).elim

@[expose] def Step148HJM24Outer : Prop :=
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
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJHJOuter : Prop :=
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
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJNormalOuterON : Prop :=
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
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJNormalInner : Prop :=
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
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        (Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148HJA5Inner : Prop :=
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
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

section Narrow

theorem step148HJM24_of_outer (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h134 : Item134) (h427 : Sec4.Item4_27)
    (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime) (hTYd : Step148HJTypeYd)
    (hO : Step148HJM24Outer) : Step148HJM24 := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ hM
  let := ker148_normal hY.2
  obtain ⟨Yd, hYd, hYBYd, hYdJ, hAYd, hYdt, -, hin | ⟨hdc, hA6, hθ, hW⟩⟩ :=
    jalpha_config h45 h48 h134 h427 hGW h41 hTYd h hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ hAJ
  · exfalso
    obtain ⟨-, -, ⟨η⟩⟩ := hin
    obtain ⟨φ⟩ := hM
    have hcard : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 244823040 := by
      rw [Nat.card_congr (η.trans φ).toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    rcases card_of_ydType148 hYdt with h1 | h1 | h1 <;> omega
  · exact hO G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hA6 hθ hW hdc hM

theorem step148HJHJ_of_outer (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hTYd : Step148HJTypeYd) (hO : Step148HJHJOuter) : Step148HJHJ := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ hH
  let := ker148_normal hY.2
  obtain ⟨Yd, hYd, hYBYd, hYdJ, hAYd, hYdt, -, hin | ⟨hdc, hA6, hθ, hW⟩⟩ :=
    jalpha_config h45 h48 h134 h427 hGW h41 hTYd h hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ hAJ
  · exfalso
    obtain ⟨-, -, ⟨η⟩⟩ := hin
    obtain ⟨φ⟩ := hH
    have hcard : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 604800 := by
      rw [Nat.card_congr (η.trans φ).toEquiv]
      exact KFacts.KS14.card_nativeJ2
    rcases card_of_ydType148 hYdt with h1 | h1 | h1 <;> omega
  · exact hO G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hA6 hθ hW hdc hH

theorem step148HJA5_of_inner (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hTYd : Step148HJTypeYd) (hI : Step148HJA5Inner) : Step148HJA5 := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ h5
  let := ker148_normal hY.2
  obtain ⟨Yd, hYd, hYBYd, hYdJ, hAYd, hYdt, -, ⟨hdc, heq, hη⟩ | ⟨hdc, hA6, hθ, hW⟩⟩ :=
    jalpha_config h45 h48 h134 h427 hGW h41 hTYd h hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ hAJ
  · exact hI G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hYdt hdc heq hη h5
  · exfalso
    have hA : Late.IsE27 A := h.isE27
    obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
    have hd : d ∈ A := hB.1 hdB
    obtain ⟨h1080, hKle⟩ :=
      card_img148_yd_of_a6 hY.2 hd (hA.1.2 d hd) hYd hJ hYdJ hAJ hA6 hθ
    have hle : Nat.card ↥(img148 A Y Yd) ≤ Nat.card ↥(img148 A Y J) :=
      Subgroup.card_le_of_le (hKle.trans inf_le_left)
    have h60 : Nat.card ↥(img148 A Y J) = 60 := by
      obtain ⟨φ⟩ := h5
      rw [Nat.card_congr φ.toEquiv]
      exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    omega

theorem step148HJNormal_of_res (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hTYd : Step148HJTypeYd) (hI : Step148HJNormalInner) (hO : Step148HJNormalOuterON) :
    Step148HJNormal := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ hJt
  let := ker148_normal hY.2
  obtain ⟨Yd, hYd, hYBYd, hYdJ, hAYd, hYdt, -, ⟨hdc, heq, hη⟩ | ⟨hdc, hA6, hθ, hW⟩⟩ :=
    jalpha_config h45 h48 h134 h427 hGW h41 hTYd h hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ hAJ
  · exact hI G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hYdt hdc heq hη hJt
  rcases hJt with hJA6 | hJON
  · exfalso
    have hA : Late.IsE27 A := h.isE27
    obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
    have hd : d ∈ A := hB.1 hdB
    obtain ⟨h1080, hKle⟩ :=
      card_img148_yd_of_a6 hY.2 hd (hA.1.2 d hd) hYd hJ hYdJ hAJ hA6 hθ
    have hJ1080 : Nat.card ↥(img148 A Y J) = 1080 := by
      obtain ⟨hcz, ⟨e⟩⟩ := hJA6
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(img148 A Y J)), Nat.card_congr e.toEquiv, hcz,
        KFacts.KS14.card_alternatingGroup_six]
    have heq' : img148 A Y Yd = img148 A Y J :=
      Subgroup.eq_of_le_of_card_ge (hKle.trans inf_le_left) (by omega)
    apply hdc
    have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
    exact mem_sectionCentralizer_of_le_centralizer hJM hd (heq' ▸ (hKle.trans inf_le_right))
  · exact hO G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hA6 hθ hW hdc hJON

end Narrow

end Certificates

end CFSG.RankThree.PartTwo.Sec14
