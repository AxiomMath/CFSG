module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofSubfield

public section

namespace CFSG.RankThree.PartTwo.KFacts

namespace KS116Proof

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply)

theorem card_fixing_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (X : Set G) :
    Nat.card {φ : MulAut G // ∀ x ∈ X, φ x = x} =
      Nat.card {ψ : MulAut H // ∀ y ∈ e '' X, ψ y = y} := by
  apply Nat.card_congr
  refine
    { toFun := fun φ => ⟨MulAut.congr e φ.1, ?_⟩
      invFun := fun ψ => ⟨MulAut.congr e.symm ψ.1, ?_⟩
      left_inv := fun φ => Subtype.ext (MulEquiv.ext fun x => by
        simp [MulAut.congr_apply])
      right_inv := fun ψ => Subtype.ext (MulEquiv.ext fun y => by
        simp [MulAut.congr_apply]) }
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply, φ.2 x hx]
  · intro x hx
    have h := ψ.2 (e x) ⟨x, hx, rfl⟩
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, h,
      MulEquiv.symm_apply_apply]

section Fixing

variable {F : Type} [Field F]

theorem slFieldAut_uu (σ : F ≃+* F) (b : F) : slFieldAut F σ (uu b) = uu (σ b) := by
  apply Subtype.ext
  ext i j
  rw [slFieldAut_apply, coe_uu, coe_uu]
  fin_cases i <;> fin_cases j <;> simp

theorem slFieldAut_ll (σ : F ≃+* F) (b : F) : slFieldAut F σ (ll b) = ll (σ b) := by
  apply Subtype.ext
  ext i j
  rw [slFieldAut_apply, coe_ll, coe_ll]
  fin_cases i <;> fin_cases j <;> simp

variable [CharP F 2]

theorem eq_one_of_commute_uu_ll {M : SL(2, F)} (hu : M * uu 1 = uu 1 * M)
    (hl : M * ll 1 = ll 1 * M) : M = 1 := by
  have hM := eq_uu_of_commute hu
  rw [hM] at hl
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hl
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_ll, Matrix.mul_fin_two] at h00
  simp at h00
  rw [hM, h00, uu_zero]

variable [Finite F]

theorem card_fixing_map {K₀ : Type} [Field K₀] (β : K₀ →+* F) :
    Nat.card {ψ : MulAut SL(2, F) //
        ∀ y ∈ Set.range (Matrix.SpecialLinearGroup.map β), ψ y = y} =
      Nat.card {σ : F ≃+* F // ∀ x, σ (β x) = β x} := by
  symm
  apply Nat.card_eq_of_bijective
    (fun σ => ⟨slFieldAut F σ.1, by
      rintro _ ⟨A, rfl⟩
      apply Subtype.ext
      ext i j
      rw [slFieldAut_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, σ.2]⟩)
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply RingEquiv.ext
    intro x
    have h1 := DFunLike.congr_fun (congrArg Subtype.val h) (uu x)
    simp only [slFieldAut_uu] at h1
    exact uu_injective h1
  · rintro ⟨ψ, hψ⟩
    obtain ⟨M, σ, rfl⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut ψ
    have hfix : ∀ A : SL(2, K₀), M * slFieldAut F σ (Matrix.SpecialLinearGroup.map β A) * M⁻¹ =
        Matrix.SpecialLinearGroup.map β A := fun A => hψ _ ⟨A, rfl⟩
    have hu := hfix (uu 1)
    have hl := hfix (ll 1)
    rw [map_uu, map_one, slFieldAut_uu, map_one] at hu
    rw [map_ll, map_one, slFieldAut_ll, map_one] at hl
    have hM : M = 1 := eq_one_of_commute_uu_ll
      (by rw [← mul_inv_eq_iff_eq_mul, hu]) (by rw [← mul_inv_eq_iff_eq_mul, hl])
    subst hM
    have hσ : ∀ x, σ (β x) = β x := by
      intro x
      have h := hfix (uu x)
      rw [map_uu, slFieldAut_uu, one_mul, inv_one, mul_one] at h
      exact uu_injective h
    refine ⟨⟨σ, hσ⟩, ?_⟩
    apply Subtype.ext
    simp only [map_one, one_mul]

end Fixing

theorem card_ringEquiv_fixing {F K₀ : Type} [Field F] [Finite F] [Field K₀] (β : K₀ →+* F)
    {d : ℕ} (hd : Nat.card F = Nat.card K₀ ^ d) (hK : 2 ≤ Nat.card K₀) :
    Nat.card {σ : F ≃+* F // ∀ x, σ (β x) = β x} = d := by
  let : Algebra K₀ F := β.toAlgebra
  have e : {σ : F ≃+* F // ∀ x, σ (β x) = β x} ≃ (F ≃ₐ[K₀] F) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ.1) σ.2
      invFun := fun τ => ⟨τ.toRingEquiv, fun x => τ.commutes x⟩
      left_inv := fun σ => by
        apply Subtype.ext
        rfl
      right_inv := fun τ => by
        ext x
        rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank]
  have h := Module.natCard_eq_pow_finrank (K := K₀) (V := F)
  rw [hd] at h
  exact (Nat.pow_right_injective hK h).symm

end KS116Proof

open KS116Proof Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

theorem factZL2Even :
    ∀ (m : ℕ), 2 ≤ m → ∀ S : Subgroup (projSL 2 (GaloisField 2 (3 * m))),
      Nonempty (S ≃* projSL 2 (GaloisField 2 m)) →
        Nat.card {φ : MulAut (projSL 2 (GaloisField 2 (3 * m))) // ∀ s ∈ S, φ s = s} = 3 := by
  intro m hm S ⟨e⟩
  set F := GaloisField 2 (3 * m)
  set K₀ := GaloisField 2 m
  have hF : Nat.card F = 2 ^ (3 * m) := GaloisField.card 2 (3 * m) (by omega)
  have hK : Nat.card K₀ = 2 ^ m := GaloisField.card 2 m (by omega)
  have h4 : 4 ≤ Nat.card K₀ := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set EF := projSLEquiv F
  set EK := projSLEquiv K₀
  let ι : SL(2, K₀) →* SL(2, F) :=
    EF.symm.toMonoidHom.comp (S.subtype.comp (e.symm.toMonoidHom.comp EK.toMonoidHom))
  have hιapply : ∀ A, ι A = EF.symm (e.symm (EK A) : projSL 2 F) := fun A => rfl
  have hι : Function.Injective ι := by
    intro A B h
    rw [hιapply, hιapply] at h
    exact EK.injective (e.symm.injective (Subtype.ext (EF.symm.injective h)))
  obtain ⟨β, c, hβc⟩ := exists_conj_eq_map h4 ι hι
  have himage : EF.symm '' (S : Set (projSL 2 F)) = Set.range ι := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨EK.symm (e ⟨s, hs⟩), ?_⟩
      rw [hιapply, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    · rintro ⟨A, rfl⟩
      exact ⟨_, (e.symm (EK A)).2, rfl⟩
  have himage2 : (MulAut.conj c⁻¹) '' Set.range ι =
      Set.range (Matrix.SpecialLinearGroup.map β) := by
    ext y
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      refine ⟨A, ?_⟩
      rw [MulAut.conj_apply, hβc]
      group
    · rintro ⟨A, rfl⟩
      refine ⟨ι A, ⟨A, rfl⟩, ?_⟩
      rw [MulAut.conj_apply, hβc]
      group
  have h3 : Nat.card F = Nat.card K₀ ^ 3 := by rw [hF, hK, ← pow_mul, mul_comm]
  calc Nat.card {φ : MulAut (projSL 2 F) // ∀ s ∈ S, φ s = s}
      = Nat.card {φ : MulAut (projSL 2 F) // ∀ s ∈ (S : Set (projSL 2 F)), φ s = s} := rfl
    _ = Nat.card {ψ : MulAut SL(2, F) // ∀ y ∈ Set.range ι, ψ y = y} := by
        rw [card_fixing_congr EF.symm, himage]
    _ = Nat.card {ψ : MulAut SL(2, F) //
          ∀ y ∈ Set.range (Matrix.SpecialLinearGroup.map β), ψ y = y} := by
        rw [card_fixing_congr (MulAut.conj c⁻¹), himage2]
    _ = Nat.card {σ : F ≃+* F // ∀ x, σ (β x) = β x} := card_fixing_map β
    _ = 3 := card_ringEquiv_fixing β h3 (by omega)

end CFSG.RankThree.PartTwo.KFacts
