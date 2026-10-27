module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2SL3
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public noncomputable section

namespace CFSG.StandardType.TwE6FixedA2SL3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.TCX.E
open scoped MatrixGroups

theorem baseChangeGL_fixedA2Rho {K L : Type} [Field K] [Field L] (f : K →+* L)
    (A : SL(3, K)) :
    baseChangeGL f (fixedA2Rho K A) =
      fixedA2Rho L (Matrix.SpecialLinearGroup.map f A) := by
  have hstd : baseChangeGL f (e6rhoA2₁ K A) =
      e6rhoA2₁ L (Matrix.SpecialLinearGroup.map f A) := by
    let x : subsystemGroup Tag.E6 K support13 := (a2Equiv₁ K).symm A
    let y : subsystemGroup Tag.E6 L support13 :=
      ⟨baseChangeGL f x, baseChangeGL_mem_subsystemGroupE6 f x.2⟩
    have hx : a2Mat₁ (x : ModGL Tag.E6 K) = (A : Matrix (Fin 3) (Fin 3) K) := by
      change ((a2Equiv₁ K) x : Matrix (Fin 3) (Fin 3) K) = _
      exact congrArg (fun B : SL(3, K) => (B : Matrix (Fin 3) (Fin 3) K))
        ((a2Equiv₁ K).apply_symm_apply A)
    have hy : (a2Equiv₁ L) y = Matrix.SpecialLinearGroup.map f A := by
      apply Subtype.ext
      change a2Mat₁ (baseChangeGL f (x : ModGL Tag.E6 K)) =
        (A : Matrix (Fin 3) (Fin 3) K).map f
      rw [a2Mat₁_baseChangeGL f x.2, hx]
    have hy' : y = (a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.map f A) := by
      exact (a2Equiv₁ L).injective (by rw [hy, MulEquiv.apply_symm_apply])
    exact congrArg Subtype.val hy'
  change baseChangeGL f
      (canonicalRep (coxeterSystem Tag.E6) K fixedA2V * e6rhoA2₁ K A *
        (canonicalRep (coxeterSystem Tag.E6) K fixedA2V)⁻¹) =
    canonicalRep (coxeterSystem Tag.E6) L fixedA2V *
      e6rhoA2₁ L (Matrix.SpecialLinearGroup.map f A) *
        (canonicalRep (coxeterSystem Tag.E6) L fixedA2V)⁻¹
  rw [map_mul, map_mul, map_inv, baseChangeGL_canonicalRep, hstd]

theorem exists_preimage_fixedA2Rho_of_fixedField {K L : Type} [Field K] [Field L]
    (ι : K →+* L) (σ : L →+* L)
    (hfix : ∀ b : L, σ b = b ↔ ∃ a : K, ι a = b)
    (X : ModGL Tag.E6 K) (B : SL(3, L))
    (hX : baseChangeGL ι X = fixedA2Rho L B) :
    ∃ A : SL(3, K), fixedA2Rho K A = X ∧ Matrix.SpecialLinearGroup.map ι A = B := by
  classical
  have hσι : σ.comp ι = ι := by
    ext a
    exact (hfix (ι a)).2 ⟨a, rfl⟩
  have hσX := congrArg (baseChangeGL σ) hX
  rw [baseChangeGL_baseChangeGL, hσι, hX, baseChangeGL_fixedA2Rho] at hσX
  have hB : Matrix.SpecialLinearGroup.map σ B = B :=
    (fixedA2Rho_injective L) hσX.symm
  have hentry : ∀ i j : Fin 3, ∃ a : K, ι a = (B : Matrix (Fin 3) (Fin 3) L) i j := by
    intro i j
    apply (hfix _).1
    exact congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) i j) hB
  choose entry hM using hentry
  let M : Matrix (Fin 3) (Fin 3) K := entry
  have hmap : Matrix.map M ι = (B : Matrix (Fin 3) (Fin 3) L) := by
    funext i j
    exact hM i j
  have hdet : Matrix.det M = 1 := by
    apply ι.injective
    rw [map_one, RingHom.map_det]
    change (M.map ι).det = 1
    rw [hmap]
    exact B.property
  let A : SL(3, K) := ⟨M, hdet⟩
  have hAB : Matrix.SpecialLinearGroup.map ι A = B := Subtype.ext hmap
  refine ⟨A, ?_, hAB⟩
  apply baseChangeGL_injective ι
  rw [baseChangeGL_fixedA2Rho, hAB, hX]

theorem fixedField_iff_frobenius_eq {K L : Type} [Field K] [Finite K] [Field L]
    (ι : K →+* L) (σ : L →+* L) (hσ : ∀ b : L, σ b = b ^ Nat.card K) :
    ∀ b : L, σ b = b ↔ ∃ a : K, ι a = b := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro b
  rw [hσ]
  constructor
  · intro hb
    let S : Finset L := Finset.univ.image ι
    have hS : ∀ x ∈ S, x ^ Nat.card K = x := by
      rintro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hcard : Nat.card K ≤ S.card := by
      rw [show S = Finset.univ.image ι from rfl,
        Finset.card_image_of_injective _ ι.injective, Finset.card_univ,
        Nat.card_eq_fintype_card]
    have hlarge : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp
      (mem_of_pow_eq_self_of_le_card hlarge hS hcard hb)
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end CFSG.StandardType.TwE6FixedA2SL3
