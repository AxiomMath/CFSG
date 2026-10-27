module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KE.SLnFamily

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise

section Block

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem an_centralizer_block {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(ν, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(ν, L), (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (S : Subgroup (SL(ν, L)))
    (hz : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin ν) L)) : Set (GL (Fin ν) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin ν)).range)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L S3)
    (hcomm : ∀ u ∈ S.map ρ, y * u = u * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S3 : Set (ModGL τ L)) := by
  classical
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.toGL : SL(ν, L) →* GL (Fin ν) L) := fun B B' h =>
    Subtype.ext (congrArg (fun G : GL (Fin ν) L => (G : Matrix (Fin ν) (Fin ν) L)) h)
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
    (rootSpan τ L S3) (KE.torusGroup_le_normalizer_rootSpan hS3)
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S3 : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq, rfl⟩ := hy'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [SetLike.mem_coe, ← hrange] at hq
  obtain ⟨A, rfl⟩ := hq
  obtain ⟨d, hd⟩ := htor b
  set M : GL (Fin ν) L := diagGLn d * Matrix.SpecialLinearGroup.toGL A with hM
  have hconj : ∀ X : SL(ν, L), X ∈ S → conjDiagn d (A * X * A⁻¹) = X := by
    intro X hX
    apply hρinj
    rw [← hd]
    have h := hcomm (ρ X) ⟨X, hX, rfl⟩
    calc rootDiagUnit τ b * ρ (A * X * A⁻¹) * (rootDiagUnit τ b)⁻¹
        = (rootDiagUnit τ b * ρ A) * ρ X * (rootDiagUnit τ b * ρ A)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          group
      _ = ρ X := by rw [h, mul_inv_cancel_right]
  have hMcomm : ∀ X ∈ S, M * Matrix.SpecialLinearGroup.toGL X =
      Matrix.SpecialLinearGroup.toGL X * M := by
    intro X hX
    have h := congrArg Matrix.SpecialLinearGroup.toGL (hconj X hX)
    rw [toGL_conjDiagn, map_mul, map_mul, map_inv] at h
    have h2 : M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ = Matrix.SpecialLinearGroup.toGL X := by
      calc M * Matrix.SpecialLinearGroup.toGL X * M⁻¹
          = diagGLn d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X *
            (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGLn d)⁻¹ := by rw [hM]; group
        _ = Matrix.SpecialLinearGroup.toGL X := h
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hMs : M ∈ (Matrix.GeneralLinearGroup.scalar (Fin ν)).range := by
    rw [← hz, Subgroup.mem_centralizer_iff]
    rintro _ ⟨X, hX, rfl⟩
    exact (hMcomm X hX).symm
  obtain ⟨c, hc⟩ := hMs
  have hoff : ∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0 := by
    intro i j hij
    have h := congrArg (fun G : GL (Fin ν) L => (G : Matrix (Fin ν) (Fin ν) L) i j) hc
    simp only [hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, diagGLn,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.diagonal_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij] at h
    have hdi : ((d i : Lˣ) : L) ≠ 0 := (d i).ne_zero
    exact (mul_eq_zero.1 h.symm).resolve_left hdi
  have hρA : ρ A ∈ torusGroup τ L := hdiag A hoff
  have hyH : rootDiagUnit τ b * ρ A ∈ torusGroup τ L := mul_mem ht hρA
  refine ⟨hyH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, ← hrange] at hg
  obtain ⟨X', rfl⟩ := hg
  have hsc : M * Matrix.SpecialLinearGroup.toGL X' = Matrix.SpecialLinearGroup.toGL X' * M := by
    rw [← hc]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : L) (fun r => Commute.all _ r) _).eq
  have hc' : conjDiagn d (A * X' * A⁻¹) = X' := by
    apply hinj
    rw [toGL_conjDiagn, map_mul, map_mul, map_inv]
    calc diagGLn d * (Matrix.SpecialLinearGroup.toGL A * Matrix.SpecialLinearGroup.toGL X' *
          (Matrix.SpecialLinearGroup.toGL A)⁻¹) * (diagGLn d)⁻¹
        = M * Matrix.SpecialLinearGroup.toGL X' * M⁻¹ := by rw [hM]; group
      _ = Matrix.SpecialLinearGroup.toGL X' := by rw [hsc, mul_inv_cancel_right]
  have h4 : (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹ = ρ X' := by
    calc (rootDiagUnit τ b * ρ A) * ρ X' * (rootDiagUnit τ b * ρ A)⁻¹
        = rootDiagUnit τ b * ρ (A * X' * A⁻¹) * (rootDiagUnit τ b)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          group
      _ = ρ (conjDiagn d (A * X' * A⁻¹)) := hd _
      _ = ρ X' := by rw [hc']
  exact (mul_inv_eq_iff_eq_mul.1 h4).symm

theorem an_block_core [IsAlgClosed L] {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(ν, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(ν, L), (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    [hfin : Finite (fixSubgroup Φ')] (hq : CFSG.IsQuasisimple (fixSubgroup Φ'))
    (hz : Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin ν) L)) : Set (GL (Fin ν) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin ν)).range) :
    Finite ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      CFSG.IsQuasisimple ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S3,
        (∀ u ∈ ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)), y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S3 : Set (ModGL τ L)) := by
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
  refine ⟨Finite.of_equiv S hPe.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hq,
    fun y hy hcomm => ?_⟩
  exact an_centralizer_block hS3 ρ hρinj hrange htor hdiag S hz hy (by rw [← hP₀S]; exact hcomm)

theorem an_block_split [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν)
    {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(ν, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(ν, L), (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin ν)) (b : Fin ν → Fin ν → Lˣ)
    (hshape : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f)) :
    Finite ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      CFSG.IsQuasisimple ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S3,
        (∀ u ∈ ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)), y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S3 : Set (ModGL τ L)) := by
  obtain ⟨-, ⟨H, hH⟩, hfin, hq, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hk hν π Φ' b hshape
  have := hfin
  exact an_block_core hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_split_n Φ' H hH)

theorem an_block_unitary [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type}
    [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hq2 : ν ≠ 3 ∨ 2 < ℓ ^ f)
    (hν : 3 ≤ ν) {S3 : Set (Fin τ.rank → ℤ)} (hS3 : ∀ r ∈ S3, IsRoot τ r)
    (ρ : SL(ν, L) →* ModGL τ L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S3)
    (htor : ∀ b : Fin τ.rank → Lˣ, ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(ν, L), (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) L) i j = 0) →
      ρ A ∈ torusGroup τ L)
    (Fr : L →+* L) (n : ModGL τ L) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (ρ X) * n⁻¹ = ρ (Φ' X))
    (π : Equiv.Perm (Fin ν)) (b : Fin ν → Fin ν → Lˣ)
    (hshape : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f)) :
    Finite ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      CFSG.IsQuasisimple ↥(ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S3,
        (∀ u ∈ ρ.range ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)), y * u = u * y) →
        y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer (rootSpan τ L S3 : Set (ModGL τ L)) := by
  obtain ⟨-, ⟨H, hH⟩, hfin, hbig, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk hν π Φ' b hshape
  have := hfin
  obtain ⟨hq, -, -⟩ := hbig (by
    intro h
    have h1 : ν = 3 := (Prod.mk.inj h).1
    have h2 : ℓ ^ f = 2 := (Prod.mk.inj h).2
    rcases hq2 with h3 | h3 <;> omega)
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  exact an_block_core hS3 ρ hρinj hrange htor hdiag Fr n Φ' hΦ' hq
    (centralizer_fix_unitary_n hk hν Φ' H hH)

end Block

end CFSG.RankThree.PartOne.TCX.E
