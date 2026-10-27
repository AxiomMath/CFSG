module

public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed
public import CFSG.RankThree.PartOne.KE.SigmaMain

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise MatrixGroups

section Diagonal

variable {L : Type} [Field L]

@[expose] def diagGL3 (d : Fin 3 → Lˣ) : GL (Fin 3) L :=
  ⟨Matrix.diagonal fun i => (d i : L), Matrix.diagonal fun i => ((d i)⁻¹ : Lˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

@[expose] def conjDiag3 (d : Fin 3 → Lˣ) (A : SL(3, L)) : SL(3, L) :=
  ⟨(diagGL3 d : Matrix (Fin 3) (Fin 3) L) * A * ((diagGL3 d)⁻¹ : GL (Fin 3) L),
    by
      rw [det_mul, det_mul, A.2]
      have h := congrArg Matrix.det (Units.mul_inv (diagGL3 d : GL (Fin 3) L))
      rw [det_mul, det_one] at h
      simpa using h⟩

theorem coe_conjDiag3 (d : Fin 3 → Lˣ) (A : SL(3, L)) :
    ((conjDiag3 d A : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      (diagGL3 d : Matrix (Fin 3) (Fin 3) L) * A * ((diagGL3 d)⁻¹ : GL (Fin 3) L) :=
  rfl

@[expose] def conjDiag3Hom (d : Fin 3 → Lˣ) : SL(3, L) →* SL(3, L) where
  toFun := conjDiag3 d
  map_one' := by
    apply Subtype.ext
    rw [coe_conjDiag3]
    change (diagGL3 d : Matrix (Fin 3) (Fin 3) L) * 1 * ((diagGL3 d)⁻¹ : GL (Fin 3) L) = 1
    rw [mul_one]
    exact congrArg Units.val (mul_inv_cancel (diagGL3 d))
  map_mul' A B := by
    apply Subtype.ext
    rw [coe_conjDiag3]
    change (diagGL3 d : Matrix (Fin 3) (Fin 3) L) * (A * B : SL(3, L)) *
      ((diagGL3 d)⁻¹ : GL (Fin 3) L) = (conjDiag3 d A * conjDiag3 d B : SL(3, L))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_conjDiag3,
      coe_conjDiag3]
    have h : ((diagGL3 d)⁻¹ : GL (Fin 3) L) * (diagGL3 d : GL (Fin 3) L) = 1 := inv_mul_cancel _
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_one] at h'
    calc (diagGL3 d : Matrix (Fin 3) (Fin 3) L) * ((A : Matrix (Fin 3) (Fin 3) L) * B) *
          ((diagGL3 d)⁻¹ : GL (Fin 3) L)
        = (diagGL3 d : Matrix (Fin 3) (Fin 3) L) * A * 1 * B * ((diagGL3 d)⁻¹ : GL (Fin 3) L) := by
          rw [mul_one, mul_assoc _ (A : Matrix (Fin 3) (Fin 3) L)]
      _ = _ := by rw [← h']; simp only [mul_assoc]

theorem conjDiag3Hom_apply (d : Fin 3 → Lˣ) (A : SL(3, L)) : conjDiag3Hom d A = conjDiag3 d A :=
  rfl

theorem conjDiag3_transvection (d : Fin 3 → Lˣ) {i j : Fin 3} (hij : i ≠ j) (t : L) :
    conjDiag3 d (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij ((d i : L) * t * ((d j)⁻¹ : Lˣ)) := by
  apply Subtype.ext
  rw [coe_conjDiag3]
  have h := CFSG.LinearGroups.diagonal_mul_toMatrix_mul_diagonal_inv (K := L)
    (d := fun k => (d k : L)) (fun k => (d k).ne_zero) ⟨i, j, hij, t⟩
  change (Matrix.diagonal fun k => (d k : L)) * (1 + Matrix.single i j t) *
    (Matrix.diagonal fun k => (((d k)⁻¹ : Lˣ) : L)) = 1 + Matrix.single i j _
  simp only [TransvectionStruct.toMatrix_mk, Matrix.transvection,
    CFSG.LinearGroups.transvectionDiagConj, Units.val_inv_eq_inv_val] at h ⊢
  rw [h]

end Diagonal


section Fixed

variable {Ω : Type} [Field Ω]

theorem mem_scalar_range_of_conj (H' g : GL (Fin 3) Ω)
    (h : H'⁻¹ * g * H' ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :
    g ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  have hgA : g = H' * (H'⁻¹ * g * H') * H'⁻¹ := by group
  rw [hgA, ← ha]
  have hsc : H' * (Matrix.GeneralLinearGroup.scalar (Fin 3)) a =
      (Matrix.GeneralLinearGroup.scalar (Fin 3)) a * H' := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (a : Ω) (fun r => Commute.all _ r) _).eq.symm
  rw [hsc]
  group

theorem centralizer_fix_split {k : Type} [Field k] [Algebra k Ω] (Φ : SL(3, Ω) ≃* SL(3, Ω))
    (H : SL(3, Ω))
    (hH : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹) :
    Subgroup.centralizer (((fixSubgroup Φ).map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 3) Ω)) : Set (GL (Fin 3) Ω)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
  ext g
  constructor
  · intro hg
    set H' : GL (Fin 3) Ω := Matrix.SpecialLinearGroup.toGL H with hH'
    set A : GL (Fin 3) Ω := H'⁻¹ * g * H' with hAdef
    have hAs : A ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
      refine CFSG.RankThree.Classical.mem_range_scalar_of_commute_elementary _ fun i j hij => ?_
      set T : SL(3, Ω) := Matrix.SpecialLinearGroup.map (algebraMap k Ω)
        (Matrix.SpecialLinearGroup.transvection hij (1 : k)) with hT
      set X : SL(3, Ω) := H * T * H⁻¹ with hX
      have hXf : X ∈ fixSubgroup Φ := (hH X).2 ⟨_, rfl⟩
      have h := Subgroup.mem_centralizer_iff.1 hg (Matrix.SpecialLinearGroup.toGL X)
        ⟨X, hXf, rfl⟩
      have hXG : Matrix.SpecialLinearGroup.toGL X =
          H' * Matrix.SpecialLinearGroup.toGL T * H'⁻¹ := by
        rw [hX, hH', map_mul, map_mul, map_inv]
      have hcomm : Matrix.SpecialLinearGroup.toGL T * A = A * Matrix.SpecialLinearGroup.toGL T := by
        calc Matrix.SpecialLinearGroup.toGL T * A
            = H'⁻¹ * ((H' * Matrix.SpecialLinearGroup.toGL T * H'⁻¹) * g) * H' := by
              rw [hAdef]; group
          _ = H'⁻¹ * (g * (H' * Matrix.SpecialLinearGroup.toGL T * H'⁻¹)) * H' := by
            rw [← hXG, h]
          _ = A * Matrix.SpecialLinearGroup.toGL T := by rw [hAdef]; group
      have hTm : ((Matrix.SpecialLinearGroup.toGL T : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + Matrix.single i j 1 := by
        rw [hT]
        change ((Matrix.transvection i j (1 : k)).map (algebraMap k Ω) : Matrix (Fin 3) (Fin 3) Ω)
          = _
        ext a b
        simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
          Matrix.single_apply]
        split_ifs <;> simp
      have h2 := congrArg Units.val hcomm
      have e1 : ((Matrix.SpecialLinearGroup.toGL T * A : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          ((Matrix.SpecialLinearGroup.toGL T : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) *
            (A : Matrix (Fin 3) (Fin 3) Ω) := Units.val_mul _ _
      have e2 : ((A * Matrix.SpecialLinearGroup.toGL T : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          (A : Matrix (Fin 3) (Fin 3) Ω) *
            ((Matrix.SpecialLinearGroup.toGL T : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) :=
        Units.val_mul _ _
      rw [e1, e2, hTm] at h2
      exact h2
    exact mem_scalar_range_of_conj H' g hAs
  · rintro ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun X _ => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (a : Ω) (fun r => Commute.all _ r) _).eq.symm

theorem centralizer_fix_unitary {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    {q : ℕ} (hq : Nat.card k = q) (Φ : SL(3, Ω) ≃* SL(3, Ω)) (H : SL(3, Ω))
    (hH : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔
      ∃ Y ∈ unitarySet q 3, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    Subgroup.centralizer (((fixSubgroup Φ).map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 3) Ω)) : Set (GL (Fin 3) Ω)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
  ext g
  constructor
  · intro hg
    set H' : GL (Fin 3) Ω := Matrix.SpecialLinearGroup.toGL H with hH'
    refine mem_scalar_range_of_conj H' g ?_
    rw [← centralizer_unitary_eq_range_scalar hq (n := 3) le_rfl]
    rw [Subgroup.mem_centralizer_iff]
    intro Y hY
    set Z : GL (Fin 3) Ω := H' * Y * H'⁻¹ with hZ
    have hdetZ : ((Z : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det = 1 := by
      have h1 : ((Y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det = 1 := hY.2.1
      have h2 : ((H' : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det *
          ((H'⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det = 1 := by
        rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      calc ((Z : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det
          = ((H' * Y * H'⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det := rfl
        _ = ((H' : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det *
            ((Y : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det *
              ((H'⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det := by
            rw [Units.val_mul, Units.val_mul, det_mul, det_mul]
        _ = 1 := by rw [h1, mul_one, h2]
    set X : SL(3, Ω) := ⟨(Z : Matrix (Fin 3) (Fin 3) Ω), hdetZ⟩ with hX
    have hXZ : Matrix.SpecialLinearGroup.toGL X = Z := Units.ext rfl
    have hXf : X ∈ fixSubgroup Φ := (hH X).2 ⟨Y, hY, by rw [hXZ]⟩
    have h := Subgroup.mem_centralizer_iff.1 hg (Matrix.SpecialLinearGroup.toGL X) ⟨X, hXf, rfl⟩
    rw [hXZ] at h
    calc Y * (H'⁻¹ * g * H') = H'⁻¹ * ((H' * Y * H'⁻¹) * g) * H' := by group
      _ = H'⁻¹ * (g * (H' * Y * H'⁻¹)) * H' := by rw [← hZ, h]
      _ = (H'⁻¹ * g * H') * Y := by group
  · rintro ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun X _ => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (a : Ω) (fun r => Commute.all _ r) _).eq.symm

end Fixed


section Core

variable {τ : Tag} {L : Type} [Field L]

@[expose] def IsSigmaFamily {ι' : Type} (n : ModGL τ L) (Fr : L →+* L)
    (S : Set (Fin τ.rank → ℤ)) (P : ι' → Subgroup (ModGL τ L)) : Prop :=
  (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧ (∀ i, P i ≤ rootSpan τ L S) ∧
    (∀ i, P i ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
    (∀ i, P i ≤ adjointGroup τ L) ∧
    (∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
      y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) → ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
    (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S,
      y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
      (∀ i, ∀ u ∈ P i, y * u = u * y) →
      y ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) S)

theorem toGL_conjDiag3 (d : Fin 3 → Lˣ) (B : SL(3, L)) :
    Matrix.SpecialLinearGroup.toGL (conjDiag3 d B) =
      diagGL3 d * Matrix.SpecialLinearGroup.toGL B * (diagGL3 d)⁻¹ :=
  Units.ext rfl

theorem a2_family_core [IsAlgClosed L] {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    [hfin : Finite (fixSubgroup Φ')] (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hz : Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 3) L)) : Set (GL (Fin 3) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 3)).range) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Rs := twistedFixedPoints n Φ with hRs
  set S := fixSubgroup Φ' with hS
  set P₀ : Subgroup (ModGL τ L) := ρ.range ⊓ Rs with hP₀
  have hP₀S : P₀ = S.map ρ := by
    ext u
    constructor
    · rintro ⟨⟨X, rfl⟩, hu2⟩
      refine ⟨X, ?_, rfl⟩
      have h : ρ (Φ' X) = ρ X := by rw [← hΦ' X]; exact hu2
      exact hρinj h
    · rintro ⟨X, hX, rfl⟩
      refine ⟨⟨X, rfl⟩, ?_⟩
      have h : Φ' X = X := hX
      change n * Φ (ρ X) * n⁻¹ = ρ X
      rw [hΦ' X, h]
  have hPe : S ≃* P₀ :=
    (Subgroup.equivMapOfInjective S ρ hρinj).trans (MulEquiv.subgroupCongr hP₀S.symm)
  have hPq : CFSG.IsQuasisimple P₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hq
  have hPfin : Finite P₀ := Finite.of_equiv S hPe.toEquiv
  have hS3' : ∀ r ∈ S3, IsRoot τ r := hS3
  have hN : torusGroup τ L ⊔ rootSpan τ L S3 ≤ Subgroup.normalizer (ρ.range : Set (ModGL τ L)) := by
    rw [hrange]
    exact sup_le (torusGroup_le_normalizer_rootSpan hS3') Subgroup.le_normalizer
  refine ⟨fun _ => P₀, ?_⟩
  unfold IsSigmaFamily
  refine ⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => inf_le_right,
    fun _ => ?_, fun _ y hy hyR u hu => ?_, fun y hy hyR hcomm => ?_⟩
  · rw [← hrange]
    exact inf_le_left
  · exact (inf_le_left : P₀ ≤ ρ.range).trans (by rw [hrange]; exact rootSpan_le_adjointGroup L S3)
  · have hu' : u ∈ P₀ := hu
    have hR : y * u * y⁻¹ ∈ Rs := mul_mem (mul_mem hyR hu'.2) (inv_mem hyR)
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN hy) u).1 hu'.1, hR⟩
  · have hSf : ∀ X, X ∈ S ↔ Φ' X = X := fun X => Iff.rfl
    have hinj : Function.Injective
        (Matrix.SpecialLinearGroup.toGL : SL(3, L) →* GL (Fin 3) L) := fun B B' h =>
      Subtype.ext (congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h)
    have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
      (rootSpan τ L S3) (torusGroup_le_normalizer_rootSpan hS3')
    have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S3 : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hy
    rw [e] at hy'
    obtain ⟨t, ht, q, hq, rfl⟩ := hy'
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [SetLike.mem_coe, ← hrange] at hq
    obtain ⟨A, rfl⟩ := hq
    obtain ⟨d, hd⟩ := htor b
    set M : GL (Fin 3) L := diagGL3 d * Matrix.SpecialLinearGroup.toGL A with hM
    have hconj : ∀ X : SL(3, L), X ∈ S → conjDiag3 d (A * X * A⁻¹) = X := by
      intro X hX
      apply hρinj
      rw [← hd]
      have hXP : ρ X ∈ P₀ := by
        rw [hP₀S]
        exact ⟨X, hX, rfl⟩
      have h := hcomm () _ hXP
      calc rootDiagUnit τ b * ρ (A * X * A⁻¹) * (rootDiagUnit τ b)⁻¹
          = (rootDiagUnit τ b * ρ A) * ρ X * (rootDiagUnit τ b * ρ A)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = ρ X := by rw [h, mul_inv_cancel_right]
    have hMcomm : ∀ X ∈ S, M * Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL X * M := by
      intro X hX
      have h := congrArg Matrix.SpecialLinearGroup.toGL (hconj X hX)
      rw [toGL_conjDiag3, map_mul, map_mul, map_inv] at h
      have h2 : M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ = Matrix.SpecialLinearGroup.toGL X := by
        calc M * Matrix.SpecialLinearGroup.toGL X * M⁻¹
            = diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X := h
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hMs : M ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
      rw [← hz, Subgroup.mem_centralizer_iff]
      rintro _ ⟨X, hX, rfl⟩
      exact (hMcomm X hX).symm
    obtain ⟨c, hc⟩ := hMs
    have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
      intro i j hij
      have h := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L) i j) hc
      simp only [hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, diagGL3,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.diagonal_mul, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij] at h
      have hdi : ((d i : Lˣ) : L) ≠ 0 := (d i).ne_zero
      exact (mul_eq_zero.1 h.symm).resolve_left hdi
    have hρA : ρ A ∈ torusGroup τ L := hdiag A hoff
    have hyH : rootDiagUnit τ b * ρ A ∈ torusGroup τ L := mul_mem ht hρA
    have hcZ : rootDiagUnit τ b * ρ A ∈ Subgroup.centralizer
        ((rootSpan τ L S3 : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, ← hrange] at hg
      obtain ⟨X', rfl⟩ := hg
      have hsc : M * Matrix.SpecialLinearGroup.toGL X' = Matrix.SpecialLinearGroup.toGL X' * M := by
        rw [← hc]
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact (Matrix.scalar_commute (c : L) (fun r => Commute.all _ r) _).eq
      have hc' : conjDiag3 d (A * X' * A⁻¹) = X' := by
        apply hinj
        rw [toGL_conjDiag3, map_mul, map_mul, map_inv]
        calc diagGL3 d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X' *
              (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGL3 d)⁻¹
            = M * Matrix.SpecialLinearGroup.toGL X' * M⁻¹ := by rw [hM]; group
          _ = Matrix.SpecialLinearGroup.toGL X' := by rw [hsc, mul_inv_cancel_right]
      have h4 : (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹ = ρ X' := by
        calc (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹
            = rootDiagUnit τ b * ρ (A * X' * A⁻¹) * (rootDiagUnit τ b)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
              group
          _ = ρ (conjDiag3 d (A * X' * A⁻¹)) := hd _
          _ = ρ X' := by rw [hc']
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end Core


section Wrappers

variable {τ : Tag} {L : Type} [Field L]

theorem a2_family_split [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f)) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P := by
  obtain ⟨-, ⟨H, hH⟩, -, hfin, hq, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_split hℓ hf hk π Φ' b
      hshape
  have := hfin
  exact a2_family_core hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_split Φ' H hH)

theorem a2_family_unitary [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hq2 : 2 < ℓ ^ f)
    {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(3, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin 3 → Lˣ, ∀ A : SL(3, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 d A))
    (hdiag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(3, L) ≃* SL(3, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ)
    (hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f)) :
    ∃ P : Unit → Subgroup (ModGL τ L), IsSigmaFamily n Fr S3 P := by
  obtain ⟨-, ⟨H, hH⟩, -, hfin, hbig⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ hf hk π Φ' b
      hshape
  have := hfin
  obtain ⟨hq, -, -, -⟩ := hbig hq2
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  exact a2_family_core hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_unitary hk Φ' H hH)

end Wrappers

end CFSG.RankThree.PartOne.KE
