module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeFaithfulA
public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitField

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful

open CFSG.RankThree.PartTwo.KFacts.KS116Proof (toProjSL)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Wreathed.CentralSL2
open scoped MatrixGroups

theorem exists_quadratic_extension' (F : Type) [Field F] (b : Fˣ) (hb : ¬ IsSquare b) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E), Nonempty (Module.Basis (Fin 2) F E) := by
  set f : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (b : F) with hf
  have hirr : Irreducible f := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro c hc
    apply hb
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hc
      exact b.ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_mul, Units.val_mk0, ← hc, sq])⟩
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hf0 with hpb
  have hdim : pb.dim = 2 := by
    rw [hpb, AdjoinRoot.powerBasis_dim, hf, Polynomial.natDegree_X_pow_sub_C]
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, ⟨pb.basis.reindex (finCongr hdim)⟩⟩

theorem exists_dihedral_pair {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card F + 1) :
    ∃ h s : projSL 2 F, h ^ ℓ = 1 ∧ h ≠ 1 ∧ s * s = 1 ∧ s ≠ 1 ∧ h * s * h = s := by
  classical
  have := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := fun hc => h2 (by
    have := (ringChar.spec F 2).mpr (by rw [hc])
    exact_mod_cast this)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := F) hchar
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  obtain ⟨E, _, _, ⟨basis⟩⟩ := exists_quadratic_extension' F (Units.mk0 a ha0)
    (fun ⟨y, hy⟩ => ha ⟨y, by simpa using congrArg Units.val hy⟩)
  haveI : Finite E := finite_of_basis F E basis
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' ℓ (G := normOne F E)
    (by rw [card_normOne F E basis]; exact hdvd)
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis (-1)
  have hz' : (z : E) * (z : E) ^ Nat.card F = algebraMap F E (-1) := by
    rw [hz]; simp
  set q := Nat.card F with hq
  have hdetz : (mulMatrix F E basis (z : E)).det = -1 := by
    apply (algebraMap F E).injective
    rw [algebraMap_det_mulMatrix, hz']
  let s₀ : SL(2, F) := ⟨mulMatrix F E basis (z : E) * frobMatrix F E basis, by
    rw [Matrix.det_mul, hdetz, det_frobMatrix F E basis h2]; norm_num⟩
  let h₀ : SL(2, F) := mulSL F E basis t
  have hs₀ : (s₀ : Matrix (Fin 2) (Fin 2) F) =
      mulMatrix F E basis (z : E) * frobMatrix F E basis := rfl
  have hh₀ : (h₀ : Matrix (Fin 2) (Fin 2) F) = mulMatrix F E basis ((t : Eˣ) : E) := rfl
  have hs₀sq : ((s₀ * s₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hs₀]
    have e1 := frobMatrix_mul_mulMatrix F E basis (z : E)
    calc mulMatrix F E basis (z : E) * frobMatrix F E basis *
          (mulMatrix F E basis (z : E) * frobMatrix F E basis)
        = mulMatrix F E basis (z : E) * (frobMatrix F E basis * mulMatrix F E basis (z : E)) *
            frobMatrix F E basis := by simp only [Matrix.mul_assoc]
      _ = mulMatrix F E basis (z : E) * (mulMatrix F E basis ((z : E) ^ q) *
            frobMatrix F E basis) * frobMatrix F E basis := by rw [e1]
      _ = mulMatrix F E basis ((z : E) * (z : E) ^ q) *
            (frobMatrix F E basis * frobMatrix F E basis) := by
          simp only [map_mul, Matrix.mul_assoc]
      _ = (-1 : F) • 1 := by
          rw [frobMatrix_mul_self, hz', mulMatrix_algebraMap, Matrix.mul_one, Matrix.scalar_apply,
            Matrix.smul_one_eq_diagonal]
  have hrel : h₀ * s₀ * h₀ = s₀ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hh₀, hs₀]
    have e1 := frobMatrix_mul_mulMatrix F E basis ((t : Eˣ) : E)
    have e2 : ((t : Eˣ) : E) * ((t : Eˣ) : E) ^ q = 1 := (mem_normOne_iff F E t).mp t.2
    calc mulMatrix F E basis ((t : Eˣ) : E) *
          (mulMatrix F E basis (z : E) * frobMatrix F E basis) *
          mulMatrix F E basis ((t : Eˣ) : E)
        = mulMatrix F E basis ((t : Eˣ) : E) * mulMatrix F E basis (z : E) *
            (frobMatrix F E basis * mulMatrix F E basis ((t : Eˣ) : E)) := by
          simp only [Matrix.mul_assoc]
      _ = mulMatrix F E basis ((t : Eˣ) : E) * mulMatrix F E basis (z : E) *
            (mulMatrix F E basis (((t : Eˣ) : E) ^ q) * frobMatrix F E basis) := by rw [e1]
      _ = mulMatrix F E basis (((t : Eˣ) : E) * (z : E) * ((t : Eˣ) : E) ^ q) *
            frobMatrix F E basis := by simp only [map_mul, Matrix.mul_assoc]
      _ = mulMatrix F E basis (z : E) * frobMatrix F E basis := by
          congr 2
          calc ((t : Eˣ) : E) * (z : E) * ((t : Eˣ) : E) ^ q
              = (z : E) * (((t : Eˣ) : E) * ((t : Eˣ) : E) ^ q) := by ring
            _ = (z : E) := by rw [e2, mul_one]
  have hh₀ℓ : h₀ ^ ℓ = 1 := by
    rw [← map_pow]
    have := pow_orderOf_eq_one t
    rw [ht] at this
    rw [this, map_one]
  have hord : orderOf h₀ = ℓ := by
    rw [← ht]
    exact orderOf_injective (mulSL F E basis) (mulSL_injective F E basis) t
  refine ⟨toProjSL F h₀, toProjSL F s₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hh₀ℓ, map_one]
  · intro h
    obtain ⟨r, hr, hr'⟩ := eq_scalar_of_toProjSL_eq_one h
    have hsq : h₀ ^ 2 = 1 := by
      apply Subtype.ext
      rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hr', Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_one, smul_smul, ← sq, hr, one_smul, Matrix.SpecialLinearGroup.coe_one]
    have h2d : ℓ ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one hsq
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp h2d)
  · rw [← map_mul]
    exact toProjSL_eq_one_of_scalar (r := -1) (by norm_num) hs₀sq
  · intro h
    obtain ⟨r, hr, hr'⟩ := eq_scalar_of_toProjSL_eq_one h
    have h1 : ((s₀ * s₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hr', Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← sq, hr, one_smul]
    rw [hs₀sq] at h1
    have h00 := congrFun (congrFun h1 0) 0
    simp at h00
    apply h2
    linear_combination -h00
  · rw [← map_mul, ← map_mul, hrel]

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful
