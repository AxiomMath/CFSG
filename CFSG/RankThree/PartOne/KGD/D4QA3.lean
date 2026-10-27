module

public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KGD.ThreeA1Twisted
public import CFSG.RankThree.PartOne.KGD.D4QTorus
public import CFSG.RankThree.PartOne.KGD.D4Twist

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.QuadraticSL2
open scoped Matrix MatrixGroups Pointwise

section Roots

@[expose] def d4Qr₁ : Fin TwistTag.D4.tag.rank → ℤ := Pi.single i0 1
@[expose] def d4Qr₂ : Fin TwistTag.D4.tag.rank → ℤ := -Pi.single i1 1
@[expose] def d4Qr₃ : Fin TwistTag.D4.tag.rank → ℤ := Pi.single i3 1

theorem d4Q_isRoot :
    IsRoot TwistTag.D4.tag d4Qr₁ ∧ IsRoot TwistTag.D4.tag d4Qr₂ ∧
      IsRoot TwistTag.D4.tag d4Qr₃ :=
  ⟨isRoot_single _ _, IsRoot.neg (isRoot_single _ _), isRoot_single _ _⟩

theorem d4Q_orth :
    iform d4Qr₁ d4Qr₂ = 0 ∧ iform d4Qr₁ d4Qr₃ = 0 ∧ iform d4Qr₂ d4Qr₃ = 0 := by
  decide +kernel

theorem d4Q_sum_check :
    List.ofFn (d4Qr₁ + d4Qr₂) ∉ TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (d4Qr₁ - d4Qr₂) ∉ TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (d4Qr₁ + d4Qr₃) ∉ TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (d4Qr₁ - d4Qr₃) ∉ TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (d4Qr₂ + d4Qr₃) ∉ TwistTag.D4.tag.artifactRoots ∧
      List.ofFn (d4Qr₂ - d4Qr₃) ∉ TwistTag.D4.tag.artifactRoots := by
  decide +kernel

theorem d4Q_not_isRoot {v : Fin TwistTag.D4.tag.rank → ℤ}
    (h : List.ofFn v ∉ TwistTag.D4.tag.artifactRoots) : ¬IsRoot TwistTag.D4.tag v :=
  fun hv => h (isRoot_iff_mem_artifactRoots.1 hv)

variable {L : Type} [Field L]

theorem d4Q_commute₁₂ (A B : SL2 L) :
    Commute (rootSL2 TwistTag.D4.tag L d4Qr₁ A) (rootSL2 TwistTag.D4.tag L d4Qr₂ B) :=
  rootSL2_commute_of_orth (d4Q_isRoot).1 (d4Q_isRoot).2.1 d4Q_orth.1
    (d4Q_not_isRoot d4Q_sum_check.1) (d4Q_not_isRoot d4Q_sum_check.2.1) A B

theorem d4Q_commute₁₃ (A B : SL2 L) :
    Commute (rootSL2 TwistTag.D4.tag L d4Qr₁ A) (rootSL2 TwistTag.D4.tag L d4Qr₃ B) :=
  rootSL2_commute_of_orth (d4Q_isRoot).1 (d4Q_isRoot).2.2 d4Q_orth.2.1
    (d4Q_not_isRoot d4Q_sum_check.2.2.1) (d4Q_not_isRoot d4Q_sum_check.2.2.2.1) A B

theorem d4Q_commute₂₃ (A B : SL2 L) :
    Commute (rootSL2 TwistTag.D4.tag L d4Qr₂ A) (rootSL2 TwistTag.D4.tag L d4Qr₃ B) :=
  rootSL2_commute_of_orth (d4Q_isRoot).2.1 (d4Q_isRoot).2.2 d4Q_orth.2.2
    (d4Q_not_isRoot d4Q_sum_check.2.2.2.2.1) (d4Q_not_isRoot d4Q_sum_check.2.2.2.2.2) A B

end Roots

section Rel

variable {L : Type} [Field L]

theorem d4Q_perm_r₁ : permLattice TwistTag.D4.perm d4Qr₁ = Pi.single i1 1 := by
  rw [d4Qr₁, permLattice_single, perm_i0]

theorem d4Q_perm_r₂ : permLattice TwistTag.D4.perm d4Qr₂ = -Pi.single i3 1 := by
  rw [d4Qr₂, permLattice_neg, permLattice_single, perm_i1]

theorem d4Q_perm_r₃ : permLattice TwistTag.D4.perm d4Qr₃ = Pi.single i0 1 := by
  rw [d4Qr₃, permLattice_single, perm_i3]

theorem d4Q_rels {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x) :
    ∃ s₁ s₂ y : Lˣ,
      (∀ A : SL2 L, n * diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L d4Qr₁ A *
        (n * diagramMap TwistTag.D4 L)⁻¹ =
          rootSL2 TwistTag.D4.tag L d4Qr₂ (conjSL (diagUnitOne s₁) A)) ∧
      (∀ A : SL2 L, n * diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L d4Qr₂ A *
        (n * diagramMap TwistTag.D4 L)⁻¹ =
          rootSL2 TwistTag.D4.tag L d4Qr₃ (conjSL (diagUnitOne s₂) A)) ∧
      (∀ A : SL2 L, n * diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L d4Qr₃ A *
        (n * diagramMap TwistTag.D4 L)⁻¹ =
          rootSL2 TwistTag.D4.tag L d4Qr₁ (conjSL (swapGL * diagUnitOne y) A)) := by
  obtain ⟨s₁, h₁⟩ := exists_conj_rootSL2_eq_twist hn (d4Q_isRoot).1
  obtain ⟨s₂, h₂⟩ := exists_conj_rootSL2_eq_twist hn (d4Q_isRoot).2.1
  obtain ⟨s₃, h₃⟩ := exists_conj_rootSL2_eq_twist hn (d4Q_isRoot).2.2
  rw [d4Q_perm_r₁, hnW] at h₁
  rw [d4Q_perm_r₂, hnW] at h₂
  rw [d4Q_perm_r₃, hnW] at h₃
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) (isRoot_single TwistTag.D4.tag i0)
  refine ⟨s₁, s₂, a * s₃, fun A => ?_, fun A => ?_, fun A => ?_⟩
  · rw [h₁ A]
    rfl
  · rw [h₂ A, neg_neg]
    rfl
  · rw [h₃ A]
    have : (rootSL2 TwistTag.D4.tag L (-Pi.single i0 1) : SL2 L →* ModGL TwistTag.D4.tag L) =
        rootSL2 TwistTag.D4.tag L (-(Pi.single i0 1)) := rfl
    rw [ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]
    rfl

end Rel

section Mul

variable {L : Type} [Field L]

@[expose] def d4QBCMul (L : Type) [Field L] : SL2 L × SL2 L →* ModGL TwistTag.D4.tag L :=
  (rootSL2 TwistTag.D4.tag L d4Qr₂).noncommCoprod (rootSL2 TwistTag.D4.tag L d4Qr₃)
    d4Q_commute₂₃

@[expose] def d4QMul (L : Type) [Field L] : SL2 L × SL2 L × SL2 L →* ModGL TwistTag.D4.tag L :=
  (rootSL2 TwistTag.D4.tag L d4Qr₁).noncommCoprod (d4QBCMul L) fun A BC =>
    (d4Q_commute₁₂ A BC.1).mul_right (d4Q_commute₁₃ A BC.2)

theorem d4QMul_apply (A B C : SL2 L) :
    d4QMul L (A, B, C) = rootSL2 TwistTag.D4.tag L d4Qr₁ A * rootSL2 TwistTag.D4.tag L d4Qr₂ B *
      rootSL2 TwistTag.D4.tag L d4Qr₃ C :=
  (mul_assoc _ _ _).symm

end Mul

section Transport

variable {L : Type} [Field L]

@[expose] def twHom (Fr : L →+* L) (M : GL (Fin 2) L) : SL2 L →* SL2 L :=
  (conjSL M).comp (Matrix.SpecialLinearGroup.map Fr)

theorem twHom_apply (Fr : L →+* L) (M : GL (Fin 2) L) (A : SL2 L) :
    twHom Fr M A = conjSL M (Matrix.SpecialLinearGroup.map Fr A) := rfl

@[expose] def glTw (Fr : L →+* L) (M : GL (Fin 2) L) : GL (Fin 2) L →* GL (Fin 2) L :=
  (MulAut.conj M).toMonoidHom.comp (Matrix.GeneralLinearGroup.map Fr)

theorem toGL_twHom (Fr : L →+* L) (M : GL (Fin 2) L) (A : SL2 L) :
    Matrix.SpecialLinearGroup.toGL (twHom Fr M A) = glTw Fr M (Matrix.SpecialLinearGroup.toGL A) := by
  apply Units.ext
  simp only [twHom_apply, glTw, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_conjSL,
    Matrix.SpecialLinearGroup.map_apply_coe, Matrix.GeneralLinearGroup.coe_inv]
  rfl

theorem glMap_bijective {Fr : L →+* L} (hFr : Function.Bijective Fr) :
    Function.Bijective (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L) := by
  let e : L ≃+* L := RingEquiv.ofBijective Fr hFr
  have h : (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L) =
      (Units.mapEquiv (e.mapMatrix (m := Fin 2)).toMulEquiv).toMonoidHom := rfl
  rw [h]
  exact (Units.mapEquiv _).bijective

theorem glTw_bijective {Fr : L →+* L} (hFr : Function.Bijective Fr) (M : GL (Fin 2) L) :
    Function.Bijective (glTw Fr M) :=
  (MulAut.conj M).bijective.comp (glMap_bijective hFr)

theorem glTw_scalar (Fr : L →+* L) (M : GL (Fin 2) L) (c : Lˣ) :
    glTw Fr M (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map Fr.toMonoidHom c) := by
  have h1 : (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map Fr.toMonoidHom c) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar]
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map Fr.toMonoidHom c) ∈
      Subgroup.center (GL (Fin 2) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  change (MulAut.conj M) ((Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) = _
  rw [h1, MulAut.conj_apply]
  have hc := Subgroup.mem_center_iff.1 h2 M
  rw [hc, mul_inv_cancel_right]

theorem twHom_injective {Fr : L →+* L} (M : GL (Fin 2) L) :
    Function.Injective (twHom Fr M) := by
  intro A B h
  have h0 : ∀ C : SL2 L, conjSL M⁻¹ (conjSL M C) = C := fun C => by
    rw [← conjSL_mul, inv_mul_cancel, conjSL_one]
  have h1 : Matrix.SpecialLinearGroup.map Fr A = Matrix.SpecialLinearGroup.map Fr B := by
    have := congrArg (conjSL M⁻¹) h
    rwa [twHom_apply, twHom_apply, h0, h0] at this
  apply Subtype.ext
  have h2 := congrArg Subtype.val h1
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h2
  exact Matrix.map_injective Fr.injective h2

theorem isQuasisimple_map_twHom {Fr : L →+* L} (M : GL (Fin 2) L) {S : Subgroup (SL2 L)}
    (hS : CFSG.IsQuasisimple S) : CFSG.IsQuasisimple (S.map (twHom Fr M)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective S (twHom Fr M) (twHom_injective M)) hS

theorem centralizer_map_twHom {Fr : L →+* L} (hFr : Function.Bijective Fr) (M : GL (Fin 2) L)
    {S : Subgroup (SL2 L)}
    (hz : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    Subgroup.centralizer (((S.map (twHom Fr M)).map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  ext X
  obtain ⟨Y, rfl⟩ := (glTw_bijective hFr M).2 X
  have key : glTw Fr M Y ∈ Subgroup.centralizer (((S.map (twHom Fr M)).map
      Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) ↔
      Y ∈ Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) := by
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      obtain ⟨s, hs, rfl⟩ := hg
      have := h (Matrix.SpecialLinearGroup.toGL (twHom Fr M s))
        ⟨twHom Fr M s, ⟨s, hs, rfl⟩, rfl⟩
      rw [toGL_twHom, ← map_mul, ← map_mul] at this
      exact (glTw_bijective hFr M).1 this
    · intro h g hg
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hg
      rw [toGL_twHom, ← map_mul, ← map_mul, h _ ⟨s, hs, rfl⟩]
  rw [key, hz]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Units.map Fr.toMonoidHom c, (glTw_scalar Fr M c).symm⟩
  · rintro ⟨c', hc'⟩
    let e : L ≃+* L := RingEquiv.ofBijective Fr hFr
    have hc'' : Units.map Fr.toMonoidHom (Units.map e.symm.toRingHom.toMonoidHom c') = c' := by
      apply Units.ext
      exact e.apply_symm_apply _
    have hY : glTw Fr M Y = glTw Fr M (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map e.symm.toRingHom.toMonoidHom c')) := by
      rw [glTw_scalar, hc'', hc']
    exact ⟨_, ((glTw_bijective hFr M).1 hY).symm⟩

end Transport

section Twisted

variable {L : Type} [Field L]

theorem map_map_sl2 (f g : L →+* L) (B : SL2 L) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.map g B) =
      Matrix.SpecialLinearGroup.map (f.comp g) B :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
    rfl)

theorem glMap_diagUnitOne (Fr : L →+* L) (c : Lˣ) :
    (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L) (diagUnitOne c) =
      diagUnitOne (Units.map Fr.toMonoidHom c) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, coe_diagUnitOne]

theorem glMap_swapGL (Fr : L →+* L) :
    (Matrix.GeneralLinearGroup.map Fr : GL (Fin 2) L →* GL (Fin 2) L) swapGL = swapGL := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, coe_swapGL]

theorem twHom_comp_three (Fr : L →+* L) (M₁ M₂ M₃ : GL (Fin 2) L) (B : SL2 L) :
    twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B)) =
      conjSL (M₃ * Matrix.GeneralLinearGroup.map Fr
        (M₂ * Matrix.GeneralLinearGroup.map Fr M₁))
        (Matrix.SpecialLinearGroup.map (Fr.comp (Fr.comp Fr)) B) := by
  simp only [twHom_apply, map_conjSL, ← conjSL_mul, map_mul, map_map_sl2]

end Twisted

section Family

theorem twistedFixedPoints_twistHom {L : Type} [Field L] (t : TwistTag) (n : ModGL t.tag L)
    (Fr : L →+* L) :
    twistedFixedPoints n (twistHom t L Fr) =
      twistedFixedPoints (n * diagramMap t L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedFixedPoints, mem_twistedFixedPoints, twistHom_apply]
  have : (n * diagramMap t L) * Units.map (entrywiseHom Fr) y * (n * diagramMap t L)⁻¹ =
      n * (diagramMap t L * Units.map (entrywiseHom Fr) y * (diagramMap t L)⁻¹) * n⁻¹ := by
    group
  rw [this]

theorem twistedTorusOf_twistHom {L : Type} [Field L] (t : TwistTag) (n : ModGL t.tag L)
    (Fr : L →+* L) :
    twistedTorusOf n (twistHom t L Fr) =
      twistedTorusOf (n * diagramMap t L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedTorusOf, mem_twistedTorusOf, twistHom_apply]
  have : (n * diagramMap t L) * Units.map (entrywiseHom Fr) y * (n * diagramMap t L)⁻¹ =
      n * (diagramMap t L * Units.map (entrywiseHom Fr) y * (diagramMap t L)⁻¹) * n⁻¹ := by
    group
  rw [this]

theorem subtorusSigma_twistHom {L : Type} [Field L] (t : TwistTag) (n : ModGL t.tag L)
    (Fr : L →+* L) (S : Set (Fin t.tag.rank → ℤ)) :
    subtorusSigma n (twistHom t L Fr) S =
      subtorusSigma (n * diagramMap t L) (Units.map (entrywiseHom Fr)) S := by
  unfold subtorusSigma
  rw [twistedTorusOf_twistHom]

end Family

section A3

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ] [IsAlgClosed L]

theorem iterateFrobenius_bijective :
    Function.Bijective (iterateFrobenius L ℓ f) := by
  refine ⟨(iterateFrobenius L ℓ f).injective, fun y => ?_⟩
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
  exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩

theorem d4Q_a3_family (hf : 1 ≤ f) (hq4 : 4 ≤ ℓ ^ f) {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x) :
    ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L (threeRootSet d4Qr₁ d4Qr₂ d4Qr₃) ∧
      P ≤ twistedFixedPoints n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔
          rootSpan TwistTag.D4.tag L (threeRootSet d4Qr₁ d4Qr₂ d4Qr₃),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
          ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔
          rootSpan TwistTag.D4.tag L (threeRootSet d4Qr₁ d4Qr₂ d4Qr₃),
        y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
          (∀ u ∈ P, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))
              (threeRootSet d4Qr₁ d4Qr₂ d4Qr₃)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  obtain ⟨s₁, s₂, y, h₁, h₂, h₃⟩ := d4Q_rels hn hnW
  set M₁ : GL (Fin 2) L := diagUnitOne s₁ with hM₁
  set M₂ : GL (Fin 2) L := diagUnitOne s₂ with hM₂
  set M₃ : GL (Fin 2) L := swapGL * diagUnitOne y with hM₃
  have hΘ : ∀ A B C : SL2 L,
      n * diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) (d4QMul L (A, B, C)) *
          (n * diagramMap TwistTag.D4 L)⁻¹ =
        d4QMul L (twHom Fr M₃ C, twHom Fr M₁ A, twHom Fr M₂ B) := by
    intro A B C
    rw [d4QMul_apply, d4QMul_apply, map_mul, map_mul, entrywise_rootSL2_of_field,
      entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
    set N := n * diagramMap TwistTag.D4 L with hN
    set Ra := rootSL2 TwistTag.D4.tag L d4Qr₁ (Matrix.SpecialLinearGroup.map Fr A)
    set Rb := rootSL2 TwistTag.D4.tag L d4Qr₂ (Matrix.SpecialLinearGroup.map Fr B)
    set Rc := rootSL2 TwistTag.D4.tag L d4Qr₃ (Matrix.SpecialLinearGroup.map Fr C)
    have e1 : N * Ra * N⁻¹ = rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) := h₁ _
    have e2 : N * Rb * N⁻¹ = rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) := h₂ _
    have e3 : N * Rc * N⁻¹ = rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C) := h₃ _
    calc N * (Ra * Rb * Rc) * N⁻¹ = (N * Ra * N⁻¹) * (N * Rb * N⁻¹) * (N * Rc * N⁻¹) := by group
      _ = rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) *
            rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) *
              rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C) := by rw [e1, e2, e3]
      _ = _ := by
        have c12 := (d4Q_commute₁₂ (twHom Fr M₃ C) (twHom Fr M₁ A)).eq
        have c13 := (d4Q_commute₁₃ (twHom Fr M₃ C) (twHom Fr M₂ B)).eq
        calc rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) *
              rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) *
                rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C)
            = rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) *
                (rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) *
                  rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C)) := mul_assoc _ _ _
          _ = rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) *
                (rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C) *
                  rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B)) := by rw [c13]
          _ = (rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A) *
                rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C)) *
                  rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) := (mul_assoc _ _ _).symm
          _ = (rootSL2 TwistTag.D4.tag L d4Qr₁ (twHom Fr M₃ C) *
                rootSL2 TwistTag.D4.tag L d4Qr₂ (twHom Fr M₁ A)) *
                  rootSL2 TwistTag.D4.tag L d4Qr₃ (twHom Fr M₂ B) := by rw [c12]
  obtain ⟨k₃, _, _, _, hk₃⟩ := exists_finite_field_into ℓ (3 * f) (by omega) L
  set Fr₃ : L →+* L := iterateFrobenius L ℓ (3 * f) with hFr₃def
  have hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k₃ := fun c => by
    rw [hk₃]
    exact iterateFrobenius_def ℓ (3 * f) c
  have hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃ := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hFrdef, hFr₃def, iterateFrobenius_def]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hk4₃ : 4 ≤ Nat.card k₃ := by
    rw [hk₃]
    calc 4 ≤ ℓ ^ f := hq4
      _ ≤ ℓ ^ (3 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
  set g : GL (Fin 2) L := M₃ * Matrix.GeneralLinearGroup.map Fr
    (M₂ * Matrix.GeneralLinearGroup.map Fr M₁) with hgdef
  have hg : g = swapGL * diagUnitOne (y * Units.map Fr.toMonoidHom
      (s₂ * Units.map Fr.toMonoidHom s₁)) := by
    rw [hgdef, hM₃, hM₂, hM₁, glMap_diagUnitOne, diagUnitOne_mul, glMap_diagUnitOne, mul_assoc,
      diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k₃) Fr₃ hFr₃ 1
    (y * Units.map Fr.toMonoidHom (s₂ * Units.map Fr.toMonoidHom s₁)) g (by
      rw [hg, coe_swapGL_mul_diagUnitOne]
      simp)
  set S₃ : Subgroup (SL2 L) := (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)).range.map
    (conjSL Pm) with hS₃def
  have hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B)) = B := by
    intro B
    rw [twHom_comp_three, hFr3eq, ← hgdef, ← hPm]
    exact (sl2_twistedFixed_iff Fr₃ (frobenius_fixed_iff Fr₃ hFr₃) Pm B).symm
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (K := k₃) (L := L) hk4₃ Pm
  have hz₃ := sl2_conj_range_centralizer (K := k₃) (L := L) Pm
  have hq₂ := isQuasisimple_map_twHom (Fr := Fr) M₁ hq₃
  have hq₁ := isQuasisimple_map_twHom (Fr := Fr) M₂ hq₂
  have hz₂ := centralizer_map_twHom hFrbij M₁ hz₃
  have hz₁ := centralizer_map_twHom hFrbij M₂ hz₂
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ :=
    three_A1_twisted_cyclic_family d4Q_commute₁₂ d4Q_commute₁₃ d4Q_commute₂₃
      (d4Q_isRoot).1 (d4Q_isRoot).2.1 (d4Q_isRoot).2.2 (d4QMul L) d4QMul_apply Fr
      (n * diagramMap TwistTag.D4 L) (twHom Fr M₁) (twHom Fr M₂) (twHom Fr M₃) hΘ
      _ _ S₃ rfl rfl hS₃ hq₁ hq₂ hq₃ hz₁ hz₂ hz₃
  refine ⟨P, hPfin, hPq, hPQ, ?_, hPadj, ?_, ?_⟩
  · rw [twistedFixedPoints_twistHom]
    exact hPR
  · intro y' hy hyR
    rw [twistedFixedPoints_twistHom] at hyR
    exact hPnorm y' hy hyR
  · intro y' hy hyR hcomm
    rw [twistedFixedPoints_twistHom] at hyR
    rw [subtorusSigma_twistHom]
    exact hPcent y' hy hyR hcomm

end A3

end CFSG.RankThree.PartOne.KGD
