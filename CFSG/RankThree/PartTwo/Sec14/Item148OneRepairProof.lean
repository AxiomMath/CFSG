module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step148KTypeSigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      ∀ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f → 1 ≤ e' →
        Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') →
        (letI := ker148_normal hY.2; IsLThreeEpsAt ↥(img148 A Y K) p f) →
        letI := ker148_normal hY.2
        Sec4.IsoLThreePi ↥(img148 A Y K) p f

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isLThreePi_of_mulEquiv148 {X X' : Type} [Group X] [Group X'] (φ : X ≃* X')
    (h : IsLThreePi X') : IsLThreePi X := by
  obtain ⟨p, f, hp, hf, hcase⟩ := h
  refine ⟨p, f, hp, hf, ?_⟩
  rcases hcase with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩

theorem type148Pi_of_kType148 (hσ : Step148KTypeSigma) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B Q : Subgroup G}
    {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le) [(ker148 A Y).Normal]
    (hkt : KType148 A Y e K Le) :
    IsLThreePi ↥(img148 A Y K) ∨ Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  rcases hkt.2 with ⟨he, hLe, hφ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩⟩
  ·
    obtain ⟨φ⟩ := hφ
    rcases (h.chosen136.2 e he Le hLe).1 with ⟨⟨ψ⟩⟩ | hL | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨φ.trans ψ⟩)))
    · exact Or.inl (isLThreePi_of_mulEquiv148 φ hL)
    · exact Or.inr (Or.inl ⟨φ.trans ψ⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))
  · exact Or.inr (Or.inl ⟨φ⟩)
  ·
    exact Or.inl ⟨p, f, hp, hf,
      hσ G A c L h Y hY hs hYB B Q e K Le hP hkt.1 he hLe p f e' hp hf he' hiso hL3⟩
  · exact Or.inr (Or.inl ⟨φ⟩)
  ·
    exact Or.inl ⟨7, 1, hp7, le_rfl, Or.inl ⟨by norm_num, ⟨φ⟩⟩⟩

section Step


theorem step148One_of_pi (hI : KF148Inner) (hPGL : KF148PGLPi)
    (hF : KF148Field) (hσ : Step148KTypeSigma) : Step148One := by
  have hC := kf148CenterL3
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  rcases halt with hEq | hTen | hField
  ·
    have hEq' : img148 A Y K = img148 A Y J := hEq
    have hT := type148Pi_of_kType148 hσ h hY hs hYB hP hkt
    rw [hEq'] at hT
    rcases hT with hL3 | hA7 | hM12 | hM22 | hJ2
    ·
      by_cases hall : ∀ (a : G) (ha : a ∈ A), InnerOn148 (img148 A Y J) (alpha148 A Y a ha)
      · refine Or.inl (eq_zpowers_sup_inf_of_innerOn hAF hAY hJY hAJ he (hC _ hJp (Or.inl hL3))
          hCJ fun a ha => ⟨0, ?_⟩)
        rw [pow_zero, mul_one]
        exact hall a ha
      · push Not at hall
        obtain ⟨a, ha, hna⟩ := hall
        right
        have hz : alpha148 A Y e he ≠ 1 := by
          intro h1
          have h1' : alpha148 A Y e he = alpha148 A Y 1 A.one_mem := by
            rw [h1, alpha148_eq_mk']
            exact (map_one _).symm
          exact hP.2.2.2.2.1 (alpha148_injective hA3 he A.one_mem h1')
        obtain ⟨hE, hE27⟩ := img148_isE27 (Y := Y)
          (Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE)
        obtain ⟨p, f, hf, hpgl⟩ := hPGL _ (img148 A Y J) (img148 A Y A) hJp hL3
          (img148_le_normalizer hAJ) hE hE27
          (fun g hg hg3 => mem_img148_of_commute hAF hAY hg hg3)
          ⟨alpha148 A Y e he, hz, img148_inf_centralizer_eq hKM he hKe hkt.1 hEq'⟩
          ⟨alpha148 A Y a ha, alpha148_mem_img148 ha, hna⟩
        refine ⟨p, f, hf, ?_⟩
        rw [img148_sup hJM le_sup_right]
        exact hpgl
    · exact Or.inl (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY hAJ he hCJ
        (Or.inr (Or.inl hA7)))
    · exact Or.inl (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY hAJ he hCJ
        (Or.inr (Or.inr (Or.inr (Or.inl hM12)))))
    · exact Or.inl (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY hAJ he hCJ
        (Or.inr (Or.inr (Or.inl hM22))))
    · exact Or.inl (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY hAJ he hCJ (Or.inl hJ2))
  ·
    exact Or.inl (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY hAJ he hCJ
      (Or.inr (Or.inr (Or.inr (Or.inr hTen.2)))))
  ·
    exact Or.inl (eq_zpowers_sup_inf_of_field148 hF hAF hAY hJ hAJ he hCJ hField)

theorem step148One_of'
    (hPGL : KF148PGLPi) (hσ : Step148KTypeSigma) :
    Step148One :=
  step148One_of_pi kf148Inner hPGL kf148Field_holds hσ

theorem step148One_of_sigma
    (hσ : Step148KTypeSigma) : Step148One :=
  step148One_of' kf148PGLPi_holds hσ

end Step

end CFSG.RankThree.PartTwo.Sec14
