module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups Matrix

theorem s16c1_G47_sl2five_unique_involution {X : Type} [Group X] (hX : IsSL2Prime X 5) :
    ∃ t : X, t * t = 1 ∧ t ≠ 1 ∧ ∀ a : X, a * a = 1 → a = 1 ∨ a = t := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := hX
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h1 : addOrderOf (1 : K) ∣ 5 := hcard ▸ addOrderOf_dvd_natCard (1 : K)
    have h2' : addOrderOf (1 : K) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa using h)
    have h3 : addOrderOf (1 : K) = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h1 h2')
    exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h3)
  let φ : X ≃* SL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have hneg : (-1 : SL(2, K)) ≠ 1 := by
    intro h
    have h' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h'
    simp at h'
    exact h2 (by linear_combination -h')
  refine ⟨φ.symm (-1), ?_, ?_, ?_⟩
  · rw [← map_mul, neg_mul_neg, mul_one, map_one]
  · intro h
    apply hneg
    simpa using congrArg φ h
  · intro a ha
    have hsq : (φ a) ^ 2 = 1 := by rw [sq, ← map_mul, ha, map_one]
    by_cases h1 : φ a = 1
    · left
      exact φ.injective (by rw [h1, map_one])
    · right
      have hm := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (φ a) hsq h1
      have hneg1 : φ a = -1 := Subtype.ext (by simpa using hm)
      exact φ.injective (by rw [hneg1, MulEquiv.apply_symm_apply])

theorem s16c1_G47_sl2_cent_scalar {F : Type} [Field F] (A : Matrix (Fin 2) (Fin 2) F)
    (hA : ∀ B : SL(2, F), A * (B : Matrix (Fin 2) (Fin 2) F) =
      (B : Matrix (Fin 2) (Fin 2) F) * A) :
    ∃ c : F, A = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  let U : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let L : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have h1 := hA U
  have h2 := hA L
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have f00 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, U, L] at e00 e01 f00
  have e : A 0 0 = A 1 1 := by linear_combination e01
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, f00, e]

theorem s16c1_G47_L3_embed {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) :
    ∃ (P : GL (Fin 3) F) (ρ : ↥X →* SL(2, F)), Function.Injective ρ ∧
      ∀ x : ↥X, ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat
            ((ρ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 *
            ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h1 : addOrderOf (1 : F) ∣ 5 := hF ▸ addOrderOf_dvd_natCard (1 : F)
    have h2' : addOrderOf (1 : F) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa using h)
    have h3 : addOrderOf (1 : F) = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h1 h2')
    exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h3)
  obtain ⟨t, ht2, ht1, huniq⟩ := s16c1_G47_sl2five_unique_involution hX
  have hcommt : ∀ x : ↥X, x * t = t * x := by
    intro x
    have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    rcases huniq (x * t * x⁻¹) hsq with h | h
    · exact absurd (by
        have hx : x * t = x := by
          have := congrArg (fun y => y * x) h
          simpa [mul_assoc] using this
        have h1 := congrArg (fun y => x⁻¹ * y) hx
        simpa [mul_assoc] using h1) ht1
    · have := congrArg (fun y => y * x) h
      simpa [mul_assoc] using this
  let T : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL (t : SL(3, F))
  have hTdef : T = Matrix.SpecialLinearGroup.toGL (t : SL(3, F)) := rfl
  have hT2 : T * T = 1 := by
    rw [hTdef, ← map_mul, ← Subgroup.coe_mul, ht2, Subgroup.coe_one, map_one]
  have hT1 : T ≠ 1 := by
    intro h
    apply ht1
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [Subgroup.coe_one, map_one]
    exact h
  have hTdet : ((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h := congrArg Units.val (Matrix.SpecialLinearGroup.coeToGL_det (t : SL(3, F)))
    simpa [hTdef] using h
  obtain ⟨P, hP⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 hT2 hT1 hTdet
  have hxT : ∀ x : ↥X, Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * T =
      T * Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) := by
    intro x
    have h' : (x : SL(3, F)) * (t : SL(3, F)) = (t : SL(3, F)) * (x : SL(3, F)) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcommt x]
    have h'' := congrArg Matrix.SpecialLinearGroup.toGL h'
    simpa [hTdef, map_mul] using h''
  have hex : ∀ x : ↥X, ∃ A : GL (Fin 2) F,
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk A =
        P⁻¹ * Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * P := by
    intro x
    refine CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.exists_blk_of_commute h2 ?_ ?_
    · rw [← hP]
      calc P⁻¹ * Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * P * (P⁻¹ * T * P)
          = P⁻¹ * (Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * T) * P := by group
        _ = P⁻¹ * (T * Matrix.SpecialLinearGroup.toGL (x : SL(3, F))) * P := by
              rw [hxT x]
        _ = P⁻¹ * T * P * (P⁻¹ * Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * P) := by
              group
    · rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']
      exact congrArg Units.val (Matrix.SpecialLinearGroup.coeToGL_det (x : SL(3, F)))
  choose g₀ hg₀ using hex
  have hone : g₀ 1 = 1 := by
    apply CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk_injective
    rw [hg₀ 1, map_one]
    show P⁻¹ * Matrix.SpecialLinearGroup.toGL ((1 : ↥X) : SL(3, F)) * P = 1
    rw [Subgroup.coe_one, map_one]
    group
  have hmul : ∀ x y : ↥X, g₀ (x * y) = g₀ x * g₀ y := by
    intro x y
    apply CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk_injective
    rw [hg₀ (x * y), map_mul, hg₀ x, hg₀ y, Subgroup.coe_mul, map_mul]
    group
  let ρ₀ : ↥X →* GL (Fin 2) F :=
    { toFun := g₀, map_one' := hone, map_mul' := hmul }
  haveI hperf : Group.IsPerfect ↥X :=
    Group.isPerfect_def.2 (by
      show ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤
      exact (s16c1_sl2five_facts hX).2.1)
  let δ : ↥X →* Fˣ := Matrix.GeneralLinearGroup.det.comp ρ₀
  have hδ : δ = 1 := by
    haveI : Group.IsPerfect δ.range := Group.IsPerfect.range δ
    haveI : Subsingleton δ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    apply MonoidHom.ext
    intro x
    exact Subtype.ext_iff.mp (Subsingleton.elim (⟨δ x, ⟨x, rfl⟩⟩ : δ.range) 1)
  have hdetρ : ∀ x : ↥X,
      ((g₀ x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro x
    have h := congrArg (fun f : ↥X →* Fˣ => f x) hδ
    change Matrix.GeneralLinearGroup.det (g₀ x) = 1 at h
    exact congrArg Units.val h
  let ρ : ↥X →* SL(2, F) :=
    { toFun := fun x => ⟨(g₀ x : Matrix (Fin 2) (Fin 2) F), hdetρ x⟩
      map_one' := Subtype.ext (by
        show ((ρ₀ 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        rw [map_one, Units.val_one, Matrix.SpecialLinearGroup.coe_one])
      map_mul' x y := Subtype.ext (by
        show ((ρ₀ (x * y) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          ((ρ₀ x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((ρ₀ y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        rw [map_mul, Units.val_mul]) }
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have h1 : g₀ x = g₀ y := Units.ext (congrArg Subtype.val hxy)
    have h2 : P⁻¹ * Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) * P =
        P⁻¹ * Matrix.SpecialLinearGroup.toGL (y : SL(3, F)) * P := by
      rw [← hg₀ x, ← hg₀ y, h1]
    have h3 : Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) =
        Matrix.SpecialLinearGroup.toGL (y : SL(3, F)) := by
      have h := congrArg (fun z : GL (Fin 3) F => P * z * P⁻¹) h2
      simpa [mul_assoc] using h
    exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective h3)
  refine ⟨P, ρ, hρinj, fun x => ?_⟩
  have hx : Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) =
      P * CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk (g₀ x) * P⁻¹ := by
    rw [hg₀ x]; group
  calc ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
      = ((Matrix.SpecialLinearGroup.toGL (x : SL(3, F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := rfl
    _ = ((P * CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk (g₀ x) * P⁻¹ :
          GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hx]
    _ = (P : Matrix (Fin 3) (Fin 3) F) *
          ((CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk (g₀ x) : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [Units.val_mul, Units.val_mul]
    _ = (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat
            ((g₀ x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            ((g₀ x : Matrix (Fin 2) (Fin 2) F)).det⁻¹ *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.coe_blk]
    _ = (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat
            ((g₀ x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [hdetρ x, inv_one]
    _ = (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat
            ((ρ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl

theorem s16c1_G47_L3_std {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) :
    ∃ P : GL (Fin 3) F, ∀ x : SL(3, F), x ∈ X ↔
      ∃ A : SL(2, F), (x : Matrix (Fin 3) (Fin 3) F) =
        (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 *
            ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨P, ρ, hρ, hform⟩ := s16c1_G47_L3_embed hF hX
  have hX120 : Nat.card ↥X = 120 := (s16c1_sl2five_facts hX).1
  have hSL : Nat.card SL(2, F) = 120 := by
    rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_two, hF]
    norm_num
  haveI : Finite SL(2, F) := Nat.finite_of_card_ne_zero (by omega)
  have hbij : Function.Bijective ρ :=
    (Nat.bijective_iff_injective_and_card ρ).mpr ⟨hρ, hX120.trans hSL.symm⟩
  refine ⟨P, fun x => ⟨fun hx => ⟨ρ ⟨x, hx⟩, hform ⟨x, hx⟩⟩, fun ⟨A, hA⟩ => ?_⟩⟩
  obtain ⟨y, hy⟩ := hbij.2 A
  have h := hform y
  rw [hy] at h
  have hxy : ((y : ↥X) : SL(3, F)) = x := Subtype.ext (h.trans hA.symm)
  rw [← hxy]
  exact y.2

theorem s16c1_G47_L3_std_mem {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {X : Subgroup SL(3, F)} (hX : IsSL2Prime ↥X 5) :
    ∃ P : GL (Fin 3) F,
      (∀ x ∈ X, ∃ A : SL(2, F), (x : Matrix (Fin 3) (Fin 3) F) =
        (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 *
            ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
      ∀ A : SL(2, F), ∃ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F) =
        (P : Matrix (Fin 3) (Fin 3) F) *
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 *
            ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨P, hP⟩ := s16c1_G47_L3_std hF hX
  refine ⟨P, fun x hx => (hP x).1 hx, fun A => ?_⟩
  have hdet : ((P : Matrix (Fin 3) (Fin 3) F) *
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat (A : Matrix (Fin 2) (Fin 2) F) 1 *
        ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_units_conj, CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.det_blkMat, A.2, one_mul]
  exact ⟨⟨_, hdet⟩, (hP _).2 ⟨A, rfl⟩, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
