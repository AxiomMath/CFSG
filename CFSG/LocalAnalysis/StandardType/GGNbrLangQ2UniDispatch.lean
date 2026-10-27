module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniTwA
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniTagA
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

theorem q2U_m_ne_one_of_quasisimple {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    {m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) E (2 ^ m))) :
    m ≠ 1 := by
  rintro rfl
  haveI : Finite E := hE.finite
  have hcardE : Nat.card E = (2 ^ 1) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  haveI : Group.IsSolvable (LargeEvenSUGroup (Fin 3) E (2 ^ 1)) :=
    Quasithin.isSolvable_statedSU_one hcardE
  haveI : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin 3) E (2 ^ 1))) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  haveI hsolv : Group.IsSolvable (X ⧸ Subgroup.center X) :=
    Group.isSolvable_of_isSolvable_injective (f := θ.toMonoidHom) θ.injective
  haveI : Nontrivial (X ⧸ Subgroup.center X) := hX.2.toNontrivial
  haveI : Group.IsPerfect X := ⟨hX.1⟩
  haveI : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    RankThree.PartOne.KCUnitary.isPerfect_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem uniS1_ne_three_one {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hID : GGInnerDiagOn Bs L)
    {m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) E (2 ^ m))) :
    m ≠ 1 := by
  obtain ⟨-, lab, -, hraw⟩ := hID
  obtain ⟨R, _, I, F, -, -, θL, hN, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨y, u, -, -, -, -, hJL, hJcomp⟩ := q1_fixed_component_data hcfg hN
  exact q2U_m_ne_one_of_quasisimple hJcomp.2.2 hE
    ((centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)).trans θ)


theorem ggBstarAbelianPreimageJUniS1Input_of_classes
    (hTwA : GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .twA))
    (hA : GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .A))
    (hRest : GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag ≠ .A ∧ lab.tag ≠ .twA)) :
    GGBstarAbelianPreimageJUniS1Input := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm E _ hE θ
  have hdm : ¬ (d = 3 ∧ m = 1) := by
    rintro ⟨rfl, rfl⟩
    exact uniS1_ne_three_one hcfg hID hE θ rfl
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨lab, hlab2, hhas, R, _, I, F, θL, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcfg.1.2.2.2.2.2.2.2.1
  have hall : GGInnerDiagOnLab (fun _ _ => True) p Bs L :=
    ggInnerDiagOnLab_of_hasLabel hRig hID hlab2 hhas trivial hP.1
  have hcls : GGInnerDiagOnLab (fun _ lab => (lab.tag = .twA ∨ lab.tag = .A) ∨
      (lab.tag ≠ .A ∧ lab.tag ≠ .twA)) p Bs L :=
    GGInnerDiagOnLab.mono (fun _ lab _ => by
      by_cases h1 : lab.tag = .twA
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : lab.tag = .A
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨h2, h1⟩) hall
  exact ((hTwA.or hA).or hRest) G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ hcls


theorem ggBstarAbelianPreimageJUniS1Input_of_rest
    (hRest : GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag ≠ .A ∧ lab.tag ≠ .twA)) :
    GGBstarAbelianPreimageJUniS1Input :=
  ggBstarAbelianPreimageJUniS1Input_of_classes ggBstarAbelianPreimageJUniS1On_twA
    ggBstarAbelianPreimageJUniS1On_tagA hRest

end CFSG.StandardType
