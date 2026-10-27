module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def YdType148 {G : Type} [Group G] (d : G) (Yd : Subgroup G) : Prop :=
  Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* alternatingGroup (Fin 5)) ∨
    Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) ∨
    (d ∈ Yd ∧ Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)
      CFSG.Blueprint.NativeSporadic.ON)

section Certificates

@[expose] def Step148HJTypeYd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G), Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd →
        A ≤ Subgroup.normalizer (Yd : Set G) →
      ∀ J ∈ thetaComponentsIn Y, Yd ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        YdType148 d Yd

@[expose] def Step148HJTypeJ : Prop :=
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
      letI := ker148_normal hY.2
      (Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) ∨
        (Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y)

theorem step148HJType_of_yd (hTYd : Step148HJTypeYd) (hTJ : Step148HJTypeJ) :
    Step148HJType := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd J hJ
    hYdJ hAJ
  exact hTJ G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd
    (hTYd G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd J hJ
      hYdJ hAJ) J hJ hYdJ hAJ

theorem step148HJ_of_yd (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hTYd : Step148HJTypeYd)
    (hTJ : Step148HJTypeJ) (hM : Step148HJM24) (hN : Step148HJNormal) (hH : Step148HJHJ)
    (h5 : Step148HJA5) : Step148HJ :=
  step148HJ_of_type h45 h48 (step148HJType_of_yd hTYd hTJ) hM hN hH h5

end Certificates

end CFSG.RankThree.PartTwo.Sec14
