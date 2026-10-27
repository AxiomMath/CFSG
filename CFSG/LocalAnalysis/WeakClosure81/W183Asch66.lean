module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
import CFSG.Adapters.StatedPSLTwo
import CFSG.GH74.Generic.S1.KL5Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (CoverOf Bar2)
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

@[expose] def Asch6_6Family : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → Nat.card A = 4 → IsElemAbelian 2 A →
      IsQuadraticOn ρ A →
      ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ F6.IsL2 p e ↥L) ∨
        (∃ (p e : ℕ) (Y : Type) (_ : Group Y), p.Prime ∧ p ≠ 2 ∧ 3 < p ^ e ∧
          ((Odd e ∧ LieModel Y .PSL 3 p e) ∨ LieModel Y .PSU 3 p e) ∧
          CoverOf ↥L Y)) → False

@[expose] def Asch6_6Pgl : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → Nat.card A = 4 → IsElemAbelian 2 A →
      IsQuadraticOn ρ A → F6.IsPGL2 7 Q →
      F6.IsL2 7 1 ↥L ∧ A ≤ L ∧
        ∀ I : Subgroup V, IsIrr ρ L I → IsNaturalL3Two ρ L I ∧
          ∀ g : Q, g ∉ L →
            (⨆ y : Q, I.map (ρ y).toMonoidHom) = I ⊔ I.map (ρ g).toMonoidHom ∧
              Disjoint I (I.map (ρ g).toMonoidHom) ∧
              IsDualPairing ρ L I (I.map (ρ g).toMonoidHom)

theorem asch6_6_of_parts (hF : Asch6_6Family) (hP : Asch6_6Pgl) : Asch6_6 := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hA hAe hq hshape
  rcases hshape with h1 | h2 | h3
  · exact (hF Q V hV ρ hρ L A hL hA hAe hq (Or.inl h1)).elim
  · exact (hF Q V hV ρ hρ L A hL hA hAe hq (Or.inr h2)).elim
  · exact hP Q V hV ρ hρ L A hL hA hAe hq h3

theorem asch6_6Family_of_cited
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h4 : Asch6_4Odd) (h5 : Asch6_5Odd) : Asch6_6Family := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hA hAe hq hshape
  have hLsub : CFSG.ComponentClassification.GeneralizedFitting.subgroup Q = L := hL
  haveI hLnormal : L.Normal := hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hcent_le : Subgroup.centralizer (L : Set Q) ≤ L :=
    hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Q
  have hsub : CFSG.Open.IsSubnormal L ⊤ :=
    CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤)
  have hAnorm : A ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLnormal]
    exact le_top
  rcases hshape with ⟨p, e, hp, hp2, h9, hL2⟩ | ⟨p, e, Y, hYgrp, hp, hp2, h3, hY, hcov⟩
  ·
    haveI hsimp : IsSimpleGroup ↥L :=
      CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hL2
    have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
      obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hL2
      have hFne2 : Nat.card F ≠ 2 := by rw [hF]; omega
      have hFne3 : Nat.card F ≠ 3 := by rw [hF]; omega
      obtain ⟨x, y, hxy⟩ :=
        CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
          F hFne2 hFne3
      let e' := eF.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
      exact ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
    haveI hperf : Group.IsPerfect ↥L :=
      ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥L hnab⟩
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot ↥L hnab
    have hcomp : IsComponentOf L ⊤ :=
      ⟨le_top, hsub, CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥L⟩
    have hAL : A ⊓ Subgroup.centralizer (L : Set Q) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L := hcent_le hx.2
      have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : Q) y.2)
      rw [hZ, Subgroup.mem_bot] at hxZ
      exact Subgroup.mem_bot.mpr (by simpa using Subtype.ext_iff.mp hxZ)
    exact h4 Q V hV ρ hρ L A hcomp hAnorm hA hAe hq hAL p e hp hp2 (by omega) hL2
  ·
    have hcomp : IsComponentOf L ⊤ := ⟨le_top, hsub, hcov.1⟩
    have hperf : Group.IsPerfect ↥L := ⟨hcov.1.1⟩
    obtain ⟨eL⟩ := hcov.2
    have hK : CFSG.IsQuasisimple ↥L :=
      ⟨hperf, hcov.1.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hcov.1⟩
    have hmodelL : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p e ∨
        StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p e := by
      rcases hY with ⟨-, hY'⟩ | hY'
      · exact Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel
          (CFSG.Blueprint.LieModel.of_mulEquiv eL.symm hY') (by decide))
      · exact Or.inr (CFSG.Blueprint.LieModel.statedClassicalModel
          (CFSG.Blueprint.LieModel.of_mulEquiv eL.symm hY') (by decide))
    have hZodd : Odd (Nat.card ↥(Subgroup.center ↥L)) :=
      CFSG.GH74.Generic.S1.kl5_odd_center_of_model_three hGA hK hp2 hmodelL
    have hAL : A ⊓ Subgroup.centralizer (L : Set Q) = ⊥ := by
      let C : Subgroup Q := A ⊓ Subgroup.centralizer (L : Set Q)
      have hC4 : Nat.card ↥C ∣ 4 := by
        rw [← hA]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hCZ : Nat.card ↥C ∣ Nat.card ↥(Subgroup.center ↥L) := by
        let f : ↥C →* ↥(Subgroup.center ↥L) :=
          { toFun := fun x => ⟨⟨x.1, hcent_le x.2.2⟩, by
              rw [Subgroup.mem_center_iff]
              intro y
              exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 (y : Q) y.2)⟩
            map_one' := Subtype.ext (Subtype.ext rfl)
            map_mul' := fun x y => Subtype.ext (Subtype.ext rfl) }
        refine Subgroup.card_dvd_of_injective f ?_
        intro x y hxy
        have h3 : ((f x).val).val = ((f y).val).val :=
          congrArg (fun z => (Subtype.val (Subtype.val z))) hxy
        exact Subtype.ext h3
      have hcop : Nat.Coprime 4 (Nat.card ↥(Subgroup.center ↥L)) := by
        simpa using (hZodd.coprime_two_left).pow_left 2
      have hC1 : Nat.card ↥C = 1 := by
        have hdvd1 : Nat.card ↥C ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd hC4 hCZ
        exact Nat.dvd_one.mp hdvd1
      exact Subgroup.eq_bot_of_card_eq C hC1
    exact h5 Q V hV ρ hρ L A hcomp hZodd hAnorm hA hAe hq hAL p e Y hYgrp hp hp2 h3 hY hcov

end CFSG.LocalAnalysis.WeakClosure81

end
