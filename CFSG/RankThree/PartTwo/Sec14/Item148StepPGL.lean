module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KF148PGLAbel : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (p f : ℕ), IsZ3PGLThreeAt Γ p f →
    ∀ x : Γ, commutator Γ ⊔ Subgroup.zpowers x ≠ ⊤

section Steps


@[expose] def Step148PGLImg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) = img148 A Y J ∨ Case148Seven A (lB A) Y

@[expose] def Step148PGLON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON →
        (∃ _ : Fact (Nat.Prime 7), letI := ker148_normal hY.2;
          Nonempty (↥(img148 A Y K) ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) →
        False

end Steps

variable {G : Type} [Group G] [Finite G]

section Abel

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem false_of_isZ3PGLThreeAt148 (hAb : KF148PGLAbel) {J : Subgroup G} (hJM : J ≤ Y ⊔ A)
    [Group.IsPerfect J] {e : G} (he : e ∈ A) (hA : A = Subgroup.zpowers e ⊔ (A ⊓ J)) {p f : ℕ}
    (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f) : False := by
  set H := img148 A Y (J ⊔ A) with hH
  have hHeq : H = img148 A Y J ⊔ Subgroup.zpowers (alpha148 A Y e he) :=
    img148_sup_eq_zpowers hJM he hA rfl
  have hJH : img148 A Y J ≤ H := hHeq ▸ le_sup_left
  have hEH : Subgroup.zpowers (alpha148 A Y e he) ≤ H := hHeq ▸ le_sup_right
  have heH : alpha148 A Y e he ∈ H := hEH (Subgroup.mem_zpowers _)
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJp' : Group.IsPerfect ↥((img148 A Y J).subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  apply hAb _ p f hpgl ⟨alpha148 A Y e he, heH⟩
  rw [eq_top_iff]
  have htop : (⊤ : Subgroup ↥H) =
      (img148 A Y J).subgroupOf H ⊔ (Subgroup.zpowers (alpha148 A Y e he)).subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hJH hEH, ← hHeq, Subgroup.subgroupOf_self]
  rw [htop]
  refine sup_le_sup ?_ ?_
  · rw [← (Subgroup.isPerfect_iff).mp hJp', commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow]
    exact hk

end Abel

theorem step148PGL_of
    (hImg : Step148PGLImg) (hON : Step148PGLON) (hAb : KF148PGLAbel) (hI : KF148Inner)
    (hF : KF148Field) : Step148PGL := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  rcases halt with hEq | hTen | hField
  ·
    have hEq' : img148 A Y K = img148 A Y J := hEq
    rcases hkt.2 with ⟨heΩ, hLeA, htype⟩ | ⟨hONc, htype⟩
    · rcases hImg G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl heΩ
        hLeA with hXJ | h7
      · exact Or.inl (case148Two_of_img148_eq (hXJ.trans hEq'.symm) hKY hKΔ heΩ hLeA htype)
      · exact Or.inr h7
    · rcases htype with hK7 | h7
      ·
        obtain ⟨p, f, -, hpgl'⟩ := hpgl
        have hJ7 : Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 7)) := by
          rw [← hEq']
          exact hK7
        exact (false_of_isZ3PGLThreeAt148 hAb hJM he (eq_zpowers_sup_inf_of_inner148 hI hAF hAY
          hJY hAJ he hCJ (Or.inr (Or.inl hJ7))) hpgl').elim
      · exact (hON G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl hONc
          h7).elim
  ·
    obtain ⟨p, f, -, hpgl'⟩ := hpgl
    exact (false_of_isZ3PGLThreeAt148 hAb hJM he (eq_zpowers_sup_inf_of_inner148 hI hAF hAY hJY
      hAJ he hCJ (Or.inr (Or.inr (Or.inr (Or.inr hTen.2))))) hpgl').elim
  ·
    obtain ⟨p, f, -, hpgl'⟩ := hpgl
    exact (false_of_isZ3PGLThreeAt148 hAb hJM he
      (eq_zpowers_sup_inf_of_field148 hF hAF hAY hJ hAJ he hCJ hField) hpgl').elim

end CFSG.RankThree.PartTwo.Sec14
