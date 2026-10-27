module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALinearBranch
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAUnitaryBranch
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RASelfMarking
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Models.PGLSimple

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def NoB2derProp : LargeEvenRawCont := fun R _ I _ =>
  ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
    ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
      GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) → False

theorem not_ggLabelIso_b2der {lab : LargeEvenLabel}
    (h : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .twD) :
    ¬ GGLabelIso lab (⟨.B2der, 0, 1⟩ : LargeEvenLabel) := by
  obtain ⟨tag, rank, n⟩ := lab
  intro hiso
  simp only at h
  rcases hiso with
    heq | ⟨-, hB, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ht : tag = .B2der := congrArg LargeEvenLabel.tag heq
    subst ht
    simp at h
  · simp at hB
  · have ht := congrArg LargeEvenLabel.tag h2
    simp at ht
  · have ht := congrArg LargeEvenLabel.tag h2
    simp at ht
  · have ht := congrArg LargeEvenLabel.tag h2
    simp at ht
  · have ht := congrArg LargeEvenLabel.tag h2
    simp at ht
  · have ht := congrArg LargeEvenLabel.tag h2
    simp at ht
  · have ht := congrArg LargeEvenLabel.tag h1
    simp at ht

private theorem a1l_exists_noncomm_of_isQuasisimple {R : Type*} [Group R] {J : Subgroup R}
    (hJq : CFSG.Assembly.IsQuasisimple J) : ∃ a b : R, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center (↥J) = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b =>
      Subtype.ext (h (b : R) (a : R))
  haveI hnt : Nontrivial (↥J ⧸ Subgroup.center (↥J)) := hJq.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥J ⧸ Subgroup.center (↥J))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

private theorem a1l_linNoB2der_of_guard {R : Type} [Group R] [Finite R]
    (lab : LargeEvenLabel) (I F : Set (MulAut R)) (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A)
    (hguard : LargeEvenSimpleGuard
      (fun R _ I _ => ∀ β ∈ I, CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab β) R I F)
    (hsimple : IsSimpleGroup R) (hRig : GGLabelRigidInput) : NoB2derProp R I F := by
  intro φ _ hφ3 hφI J hJ hlab
  haveI : IsSimpleGroup R := hsimple
  have hna : ∃ a b : R, a * b ≠ b * a := a1l_exists_noncomm_of_isQuasisimple hJ.2.2
  have hcen : Subgroup.center R = ⊥ := center_eq_bot_of_simple_nonabelian hna
  have hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab φ :=
    hguard hsimple hna φ hφI
  have hJ' : IsComponentOf J (ggAutFixedSubgroup φ) := by
    have hfix : ggFixSub φ = ggAutFixedSubgroup φ := Subgroup.ext fun _ => Iff.rfl
    rwa [hfix] at hJ
  obtain ⟨labC, hΛC, htagC, hC⟩ :=
    CFSG.StandardType.GGInnerD4RAParts.raLinearBranch_holds R lab φ J hcen hΛ htag hφ3 hin hJ'
  have htagC' : labC.tag = .A ∨ labC.tag = .twA := htagC
  exact not_ggLabelIso_b2der
    (htagC'.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
    (hRig labC ⟨.B2der, 0, 1⟩ (↥J ⧸ Subgroup.center ↥J) hΛC
      (show LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) from ⟨le_rfl, rfl, rfl⟩)
      hC hlab)

private theorem a1l_uniNoB2der_of_guard {R : Type} [Group R] [Finite R]
    (lab : LargeEvenLabel) (I F : Set (MulAut R)) (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA)
    (hguard : LargeEvenSimpleGuard
      (fun R _ I _ => ∀ β ∈ I, CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab β) R I F)
    (hsimple : IsSimpleGroup R) (hRig : GGLabelRigidInput) : NoB2derProp R I F := by
  intro φ _ hφ3 hφI J hJ hlab
  haveI : IsSimpleGroup R := hsimple
  have hna : ∃ a b : R, a * b ≠ b * a := a1l_exists_noncomm_of_isQuasisimple hJ.2.2
  have hcen : Subgroup.center R = ⊥ := center_eq_bot_of_simple_nonabelian hna
  have hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab φ :=
    hguard hsimple hna φ hφI
  have hJ' : IsComponentOf J (ggAutFixedSubgroup φ) := by
    have hfix : ggFixSub φ = ggAutFixedSubgroup φ := Subgroup.ext fun _ => Iff.rfl
    rwa [hfix] at hJ
  obtain ⟨labC, hΛC, htagC, hC⟩ :=
    CFSG.StandardType.GGInnerD4RAParts.raUnitaryBranch_holds R lab φ J hcen hΛ htag hφ3 hin hJ'
  have htagC' : labC.tag = .A ∨ labC.tag = .twA := htagC
  exact not_ggLabelIso_b2der
    (htagC'.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
    (hRig labC ⟨.B2der, 0, 1⟩ (↥J ⧸ Subgroup.center ↥J) hΛC
      (show LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) from ⟨le_rfl, rfl, rfl⟩)
      hC hlab)

theorem linNoB2der_recipe
    {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) (h2 : d = 2 → 2 ≤ n) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeLinear d (2 ^ n) Q) :
    LargeEvenRecipeLinear d (2 ^ n) fun R _ I F => Q R I F ∧ NoB2derProp R I F := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hΛ : LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    exact ⟨hn, by omega, fun h => h2 (by omega)⟩
  have hQ' : CFSG.StandardType.LargeEvenRawDatum (⟨.A, r, n⟩ : LargeEvenLabel) Q := by
    change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q
    exact hQ
  have hmodel := CFSG.StandardType.GGInnerD4RAParts.raModelSelfMarking_holds
    (⟨.A, r, n⟩ : LargeEvenLabel) hΛ (Or.inl rfl) Q hQ'
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hmodel
  obtain ⟨K, hKf, hKfin, hcard, hQK, hguard⟩ := hmodel
  refine ⟨K, hKf, hKfin, hcard, hQK, ?_⟩
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI hRfin : Finite (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) :=
    CFSG.StandardType.TCJ.tcjDatum_finite_proj _
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) := by
    have h22 : r + 1 ≠ 2 ∨ Nat.card K ≠ 2 := by
      by_cases h : r + 1 = 2
      · right
        have hn2 : 2 ≤ n := h2 h
        intro hpow
        rw [hcard] at hpow
        have hle : 4 ≤ 2 ^ n := by
          simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
        omega
      · exact Or.inl h
    have h23 : r + 1 ≠ 2 ∨ Nat.card K ≠ 3 := by
      by_cases h : r + 1 = 2
      · right
        have hn2 : 2 ≤ n := h2 h
        intro hpow
        rw [hcard] at hpow
        have hle : 4 ≤ 2 ^ n := by
          simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
        omega
      · exact Or.inl h
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) K) :=
      CFSG.BenderSuzuki.External.huppert_II_6_13 (K := K) (r + 1) (by omega) h22 h23
    exact MulEquiv.isSimpleGroup
      ((CFSG.StandardType.TypeA.recipeEquiv (r + 1) K).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          (r + 1) K).symm)
  exact a1l_linNoB2der_of_guard (⟨.A, r, n⟩ : LargeEvenLabel) _ _ hΛ rfl hguard hsimple
    CFSG.StandardType.ggLabelRigidInput_holds

theorem uniNoB2der_recipe
    {d n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n) (h3 : d = 3 → 2 ≤ n) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ NoB2derProp R I F := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hΛ : LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    exact ⟨hn, by omega, fun h => h3 (by omega)⟩
  have hQ' : CFSG.StandardType.LargeEvenRawDatum (⟨.twA, r, n⟩ : LargeEvenLabel) Q := by
    change LargeEvenRecipeUnitary (r + 1) (2 ^ n) Q
    exact hQ
  have hmodel := CFSG.StandardType.GGInnerD4RAParts.raModelSelfMarking_holds
    (⟨.twA, r, n⟩ : LargeEvenLabel) hΛ (Or.inr rfl) Q hQ'
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hmodel
  obtain ⟨K, hKf, hKfin, hcard, hQK, hguard⟩ := hmodel
  refine ⟨K, hKf, hKfin, hcard, hQK, ?_⟩
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI hRfin : Finite (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))) :=
    CFSG.StandardType.TCJ.tcjDatum_finite_proj _
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ n))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hcard
      (r + 1) (by omega) (by
        intro h
        obtain ⟨hr, hpow⟩ := Prod.mk.inj h
        have hn2 : 2 ≤ n := h3 hr
        have hle : 4 ≤ 2 ^ n := by
          simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn2
        omega)
  exact a1l_uniNoB2der_of_guard (⟨.twA, r, n⟩ : LargeEvenLabel) _ _ hΛ rfl hguard hsimple
    CFSG.StandardType.ggLabelRigidInput_holds

theorem linearNoB2derInput_holds :
    LinearNoB2derInput := by
  intro lab hΛ htag Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have htag' : tag = .A := htag
  subst htag'
  have h := hΛ
  simp only [LargeEvenInLambda2] at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact linNoB2der_recipe (d := rank + 1) (n := n) (by omega) h.1
    (fun hd => h.2.2 (by omega)) hQ

theorem unitaryNoB2derInput_holds :
    UnitaryNoB2derInput := by
  intro lab hΛ htag Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have htag' : tag = .twA := htag
  subst htag'
  have h := hΛ
  simp only [LargeEvenInLambda2] at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact uniNoB2der_recipe (d := rank + 1) (n := n) (by omega) h.1
    (fun hd => h.2.2 (by omega)) hQ

end CFSG.StandardType.S2MathAs4B2der1822

end
