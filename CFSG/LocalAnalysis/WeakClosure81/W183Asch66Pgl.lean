module

public import CFSG.LocalAnalysis.WeakClosure81.W183Asch66
import CFSG.Adapters.StatedPSLTwo
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped MatrixGroups

@[expose] def Asch6_6PglMod : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → Nat.card A = 4 → IsElemAbelian 2 A →
      IsQuadraticOn ρ A → F6.IsPGL2 7 Q → A ≤ L →
      ∀ I : Subgroup V, IsIrr ρ L I → IsNaturalL3Two ρ L I ∧
        ∀ g : Q, g ∉ L →
          (⨆ y : Q, I.map (ρ y).toMonoidHom) = I ⊔ I.map (ρ g).toMonoidHom ∧
            Disjoint I (I.map (ρ g).toMonoidHom) ∧
            IsDualPairing ρ L I (I.map (ρ g).toMonoidHom)

theorem w183_pgl2Seven_fstar {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hQ : F6.IsPGL2 7 Q) (hL : genFittingFStar Q = L) :
    F6.IsL2 7 1 ↥L ∧ Nat.card Q = 336 ∧ Nat.card ↥L = 168 := by
  obtain ⟨F, hF, hFfin, hFcard, ⟨eQ⟩⟩ := hQ
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  let e : Q ≃* CFSG.GorensteinWalter.PGL2 F :=
    eQ.trans (QuotientGroup.quotientMulEquivOfEq hcs).symm
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    rw [hFcard]
    exact ⟨7, 1, by norm_num, ⟨3, by norm_num⟩, by norm_num, by norm_num⟩
  have hcard : 3 < Nat.card F := by rw [hFcard]; norm_num
  let L' : Subgroup Q := commutator Q
  have hLn' : L'.Normal := inferInstance
  obtain ⟨eL⟩ :=
    CFSG.GorensteinWalter.commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      F hodd hcard e
  have hsimple : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hFcard]; norm_num)
  have hsimpleL : IsSimpleGroup ↥L' := (MulEquiv.isSimpleGroup_congr eL).mpr hsimple
  have hnabL : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        F (by rw [hFcard]; norm_num) (by rw [hFcard]; norm_num)
    exact ⟨eL.symm a, eL.symm b, fun h => hab (by simpa using congrArg eL h)⟩
  haveI : IsSimpleGroup ↥L' := hsimpleL
  have hquasi : CFSG.IsQuasisimple ↥L' :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabL).1
  have hL'map : L'.map e.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    have h1 : L'.map e.toMonoidHom = commutator (CFSG.GorensteinWalter.PGL2 F) := by
      rw [show L' = commutator Q from rfl,
        show commutator Q = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    rw [h1,
      CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd hcard]
  have hcentL' : Subgroup.centralizer (L' : Set Q) = ⊥ := by
    have hle := CFSG.GorensteinWalter.centralizer_map_le_of_mulEquiv e L'
      (Subgroup.centralizer (L' : Set Q)) le_rfl
    rw [hL'map, CFSG.GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot F hodd] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp (le_bot_iff.mp hle)
  have hcomp : CFSG.IsComponent L' := ⟨hquasi, hLn'.isSubnormal⟩
  have hgen : CFSG.generalizedFitting Q = L' :=
    CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot L' hcomp hcentL'
  have hgen' : genFittingFStar Q = L' := by
    change CFSG.ComponentClassification.GeneralizedFitting.subgroup Q = L'
    rw [← CFSG.generalizedFitting_eq_componentClassification, hgen]
  have hLeq : L = L' := hL.symm.trans hgen'
  have hL2' : F6.IsL2 7 1 ↥L' := by
    refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
      F, hF, hFfin, ?_, ?_⟩
    · rw [hFcard]; norm_num
    · exact ⟨eL.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hLeq]; exact hL2'
  · rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F, hFcard]
    norm_num
  · rw [hLeq, Nat.card_congr eL.toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula F hodd, hFcard]
    norm_num

theorem w183_le_of_asch6_4Seven (h4 : Asch6_4Seven) {Q : Type} [Group Q] [Finite Q] {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V}
    (hρ : Function.Injective ρ) {L A : Subgroup Q} (hL : genFittingFStar Q = L)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A)
    (hL2 : F6.IsL2 7 1 ↥L) (hQcard : Nat.card Q = 336) (hLcard : Nat.card ↥L = 168) : A ≤ L := by
  have hLnormal : L.Normal := by
    rw [← hL]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hcent_le : Subgroup.centralizer (L : Set Q) ≤ L := by
    rw [← hL]
    exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Q
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
  have hsub : CFSG.Open.IsSubnormal L ⊤ :=
    CFSG.Open.IsSubnormal.step le_top (hLnormal.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
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
  have hAnorm : A ≤ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLnormal]
    exact le_top
  have hinner := h4 Q V hV ρ hρ L A hcomp hAnorm hA hAe hq hAL hL2
  intro a ha
  obtain ⟨l, hl, hal⟩ := hinner a ha
  have hmemL : a * l⁻¹ ∈ L := hcent_le hal
  have haeq : a = (a * l⁻¹) * l := by group
  rw [haeq]
  exact L.mul_mem hmemL hl

theorem asch6_6Pgl_of_parts (h4 : Asch6_4Seven) (hMod : Asch6_6PglMod) : Asch6_6Pgl := by
  intro Q _ _ V _ _ hV ρ hρ L A hL hA hAe hq hQ
  obtain ⟨hL2, hQcard, hLcard⟩ := w183_pgl2Seven_fstar hQ hL
  have hAL : A ≤ L := w183_le_of_asch6_4Seven h4 hV hρ hL hA hAe hq hL2 hQcard hLcard
  exact ⟨hL2, hAL, hMod Q V hV ρ hρ L A hL hA hAe hq hQ hAL⟩

end CFSG.LocalAnalysis.WeakClosure81

end
