module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCent
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148StepRank
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofON
import CFSG.RankThree.PartTwo.Sec14.Item148Res9Proof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]


theorem exists_isoLThreePi_lA_of_pgl {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] (hs : ¬ Group.IsSolvable ↥Y)
    (ih : Ind148 A (lB A) Y) (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hkt : KType148 A Y e K Le) (he : e ∈ A) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hKJ : K ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hEq : Lift148Eq A Y K J)
    {p f : ℕ} (hf : 1 ≤ f) (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f) :
    Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
      ∃ (_ : Fact p.Prime) (e₁ : ℕ), 1 ≤ e₁ ∧
        Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e₁) := by
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  have hEq' : img148 A Y K = img148 A Y J := hEq
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hEq'] at h1
    exact h1
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
  have hA7 : ¬ Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) := by
    rintro ⟨φ⟩
    have hJ7 : Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 7)) := by
      rw [← hEq']
      exact ⟨φ⟩
    exact false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM he
      (eq_zpowers_sup_inf_of_inner148 kf148Inner hAF hAY hJY hAJ he hCJ (Or.inr (Or.inl hJ7)))
      hpgl
  rcases hkt.2 with ⟨heΩ, hLeA, ⟨⟨φ⟩⟩ | ⟨-, hK7⟩ | ⟨p', f', e', hp', hf', he', hiso, hL3⟩⟩ |
      ⟨hONc, hK7 | h7⟩
  ·
    have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) p f := by
      rw [hEq']
      exact hJpi
    refine ⟨heΩ, hLeA, hp, 1, le_rfl, ?_⟩
    rw [mul_one]
    exact isoLThreePi_of_mulEquiv148 φ.symm hKpi
  · exact (hA7 hK7).elim
  ·
    have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) p' f' :=
      step148KTypeSigma_holds G A c L h Y hY hs hYB B Q e K Le hP hkt.1 heΩ hLeA p' f' e' hp'
        hf' he' hiso hL3
    have hJpi' : Sec4.IsoLThreePi ↥(img148 A Y J) p' f' := by
      rw [← hEq']
      exact hKpi
    obtain ⟨rfl, rfl⟩ := isoLThreePi_unique hf' hf hJpi' hJpi
    exact ⟨heΩ, hLeA, hp', e', he', hiso⟩
  · exact (hA7 hK7).elim
  · exact (step148PGLON_holds G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq
      ⟨p, f, hf, hpgl⟩ hONc h7).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
