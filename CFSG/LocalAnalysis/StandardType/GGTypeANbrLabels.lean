module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank Matrix SpecialLinear

theorem ggHasLabel_D3_iff_A3 {R : Type} [Group R] {f : ℕ} :
    GGHasLabel ⟨.D, 3, f⟩ R ↔ GGHasLabel ⟨.A, 3, f⟩ R := Iff.rfl

theorem ggLabelIso_typeA_cases (hRig : GGLabelRigidInput) {R : Type} [Group R] {r f : ℕ}
    (hr : 2 ≤ r) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hA : LargeEvenInLambda2 ⟨.A, r, f⟩) (h : GGHasLabel lab R)
    (hA' : GGHasLabel ⟨.A, r, f⟩ R) :
    lab = ⟨.A, r, f⟩ ∨ (r = 3 ∧ lab = ⟨.D, 3, f⟩) := by
  have hiso := hRig lab ⟨.A, r, f⟩ R hlab hA h hA'
  obtain ⟨t, l, n⟩ := lab
  unfold GGLabelIso at hiso
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at hiso
  rcases hiso with ⟨rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, -, hr3, rfl⟩ | ⟨-, -, hr1, -⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hr3, rfl⟩
  · omega

theorem statedClassicalModel_of_hasLabel_typeA {X : Type} [Group X] {n f : ℕ}
    (hΛ : LargeEvenInLambda2 ⟨.A, n, f⟩) (hX : GGHasLabel ⟨.A, n, f⟩ X) :
    StatedClassicalModel X .PSL (n + 1) 2 f := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  have hf : 1 ≤ f := hΛ.1
  have hn : 1 ≤ n := hΛ.2.1
  have hn1 : n = 1 → 2 ≤ f := hΛ.2.2
  refine ⟨⟨Nat.prime_two, hf, by omega, ?_, ?_⟩, K, hF, hfin, hK, ⟨?_⟩⟩
  · intro h
    have h1 : n + 1 = 2 := (Prod.mk.inj h).1
    have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
    have := hn1 (by omega)
    have h3 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
    omega
  · intro h
    have h1 : n + 1 = 2 := (Prod.mk.inj h).1
    have h2 : 2 ^ f = 3 := (Prod.mk.inj h).2
    have : 2 ^ f % 2 = 0 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [pow_succ]; omega
    omega
  · exact (((e.trans (TypeA.recipeEquiv (n + 1) K)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) K).symm).trans
      (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (n + 1) K))

theorem ggHasLabel_J_of_lift {G : Type} [Group G] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {J : Subgroup G} {φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hk : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J) :
    GGHasLabel ⟨.A, n - 1, f⟩ (J ⧸ Subgroup.center J) := by
  have hinj := injective_comp_slLowerBlockHom hk
  let e : SpecialLinearGroup (Fin n) (GaloisField 2 f) ≃* J :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hJ)
  let e' : ProjectiveSpecialLinearGroup (Fin n) (GaloisField 2 f) ≃* (J ⧸ Subgroup.center J) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hmodel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL n 2 f := by
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_, ?_⟩, GaloisField 2 f, inferInstance, inferInstance,
      GaloisField.card 2 f (by omega), ⟨?_⟩⟩
    · intro h
      have h1 : n = 2 := (Prod.mk.inj h).1
      omega
    · intro h
      have h1 : n = 2 := (Prod.mk.inj h).1
      omega
    · exact e'.symm.trans (projectiveSpecialLinearGroupEquivStatedProj n _)
  have h1 : n - 1 + 1 = n := by omega
  exact ggHasLabel_typeA (n := n - 1) (f := f) (by rw [h1]; exact hmodel)

end CFSG.StandardType

end
