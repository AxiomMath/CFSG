module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJTypes
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AInnerCenter

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

variable {G : Type} [Group G] [Finite G]

section Certificates


@[expose] def Step148NormalHJA6E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
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
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        ∀ hdA : d ∈ A,
        img148 A Y Y ≤ Subgroup.normalizer
          (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        (∀ x y : ↥(Y ⊔ A) ⧸ ker148 A Y,
          (img148 A Y J).map (MulAut.conj x).toMonoidHom = img148 A Y J ∨
            (img148 A Y J).map (MulAut.conj y).toMonoidHom = img148 A Y J ∨
            (img148 A Y J).map (MulAut.conj x).toMonoidHom =
              (img148 A Y J).map (MulAut.conj y).toMonoidHom) →
        (∀ K₁ K₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K₁ → IsComponent K₂ →
          K₁ ≠ img148 A Y J → K₂ ≠ img148 A Y J → K₁ ≠ K₂ →
          ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, u₁ ^ 3 = 1 → u₂ ^ 3 = 1 →
            u₁ ∉ Subgroup.centralizer (K₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
            u₂ ∉ Subgroup.centralizer (K₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → False) →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

theorem step148NormalHJA6_of_e
    (hR : Step148NormalHJA6E) :
    Step148NormalHJA6 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJ3 : 3 ∣ Nat.card J := (three_dvd_card_of_ydType148 hYdt).trans
    (Subgroup.card_dvd_of_le hYdJ)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ hJ3
  exact hR G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hdA
    (img148_le_normalizer_zpowers_d_of_innerA6 hS hY hB hYB htype hc hle hJ hYd hYBYd hYdJ hAYd hdc
      hη hJ6 hdA)
    (map_conj_eq_or_of_tripleCover_A6148 hS hJc hJ6)
    (fun K₁ K₂ hK₁ hK₂ h₁ h₂ h₁₂ u₁ hu₁ u₂ hu₂ hu₁3 hu₂3 hu₁Z hu₂Z =>
      false_of_three_components_A6148 hS hJc hJ6 hK₁ hK₂ h₁ h₂ h₁₂ hu₁ hu₂ hu₁3 hu₂3 hu₁Z hu₂Z)

@[expose] def Step148NormalHJONE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
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
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → d ∈ Yd →
        ∀ hdA : d ∈ A,
        (∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y,
          (img148 A Y J).map (MulAut.conj x).toMonoidHom = img148 A Y J) →
        img148 A Y Y ≤ Subgroup.normalizer
          (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

theorem step148NormalHJON_of_e
    (hR : Step148NormalHJONE) : Step148NormalHJON := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hJ3 : 3 ∣ Nat.card J := (three_dvd_card_of_ydType148 hYdt).trans
    (Subgroup.card_dvd_of_le hYdJ)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ hJ3
  exact hR G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hdA
    (map_conj_eq_of_tripleCover_ON148 hS hJc hJON)
    (img148_le_normalizer_zpowers_d_of_innerON hS hY hdA hd1 hJ hYdJ hdc hJON hdYd)

theorem step148NormalHJ_of_leavesE
    (h142 : Concl142S14) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hTYd : Step148HJTypeYd) (hKF : KF148HJA6Outer) (hP1 : Step148HJCentPoint1)
    (hA5 : Step148NormalHJA5) (hA6 : Step148NormalHJA6E) (hON : Step148NormalHJONE) :
    Step148NormalHJ :=
  step148NormalHJ_of_leaves h142 h45 h48 h134 h427 hGW h41 hTYd hKF hP1 hA5
    (step148NormalHJA6_of_e hA6) (step148NormalHJON_of_e hON)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
