module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProof
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofComp
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Item148Res6

section Steps


theorem step148PGLNorm_holds :
    Step148PGLNorm := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl heΩ hLeA
  let := ker148_normal hY.2
  refine Or.inl fun Q' hQ' hQ'Y => ?_
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h := isSimpleGroup_img148_of_kType148 hstd hkt
    rw [hJeq] at h
    exact h
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hstd.isE27'
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAc : ∀ a ∈ img148 A Y A, ∀ a' ∈ img148 A Y A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hAE.1.1.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        w ^ 3 = 1 → w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hAF hAY hw hw3
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have hZJ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  obtain ⟨p, f, -, hpgl'⟩ := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  have hE9 := e9Closed_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hA3 h27
  have h3J : 3 ∣ Nat.card ↥(img148 A Y J) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf b = 3 := orderOf_eq_prime (hA3 b hbA) hb1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hbJ
  have hQ'M : Q' ≤ Y ⊔ A := hQ'Y.trans le_sup_left
  have hRcomm : img148 A Y Q' ≤ ⁅img148 A Y Q', img148 A Y A⁆ := by
    conv_lhs => rw [hQ'.2]
    rw [Item148PtRes.img148_commutator hQ'M le_sup_right]
  exact le_normalizer_of_component_inf hJc hZJ hE9 h3J hA3 hAc h27 hAN hF3
    (alpha148_mem_img148 he) hAJc.le hbA hbJ hb1 hRcomm

theorem step148PGLImg_of_cent
    (hCe : Step148PGLCent) : Step148PGLImg :=
  step148PGLImg_of_res step148PGLNorm_holds kf148PGLInnerV hCe

end Steps

end Item148Res6

end CFSG.RankThree.PartTwo.Sec14
