module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafCore

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))

lemma gram_det (n f : ℕ) : IsUnit (Gm n f).det :=
  nbrpom_isUnit_det (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) (minusCoeffs_irr 2 f))

lemma gram_transpose (n f : ℕ) :
    Matrix.transpose ((Gm n f).map (RingHom.id (GaloisField 2 f))) = Gm n f := by
  simpa using nbrpom_polar_matrix_transpose_eq
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)

lemma gram_iso (n f : ℕ) {s : GL (Ix n) (GaloisField 2 f)} (hs : s ∈ (ρm n f).range) :
    Matrix.transpose ((s : Mx n f).map (RingHom.id (GaloisField 2 f))) * Gm n f * (s : Mx n f) =
      Gm n f := by
  obtain ⟨gs, rfl⟩ := hs
  simpa using nbrpom_spinMatrix_gram
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) gs

lemma rank_le_of_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hab : a * b = a) (hba : b * a = a) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) ≤
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  by_cases h : a = b
  · rw [h]
  · exact (rank_lt_of_mul_eq ha hab hba h).le

lemma notSU {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    {S S' : Set (GL ι F)} (hSe : S' ⊆ S) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {e_J e' : Matrix ι ι F} (heJ : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S')) e')
    (htie : e_J * e' = e_J)
    (hdegJ : blockDegree (Algebra.adjoin F (Units.val '' S)) e_J < 2)
    (hdeg' : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S')) e') : False := by
  obtain ⟨Kf, hKf, hKa, hKfin, π, hπs, hπk, -⟩ := exists_blockField (S := S') hS' hodd' he'
  letI : Field Kf := hKf
  letI : Algebra F Kf := hKa
  have hfield := blockField_inv π hπs hπk
  have hAA' : Algebra.adjoin F (Units.val '' S') ≤ Algebra.adjoin F (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hle := blockDegree_le_of_mul (A := Algebra.adjoin F (Units.val '' S))
    (A' := Algebra.adjoin F (Units.val '' S')) hAA'
    (fun a b ha hb => (adjoin_comm hS a ha b hb).eq) heJ htie hfield
  omega

lemma notSL {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] (G : Matrix ι ι F)
    (hG : IsUnit G.det) {S S' : Set (GL ι F)} (hSe : S' ⊆ S)
    (hSiso : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J e' ε' : Matrix ι ι F} (heJ : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e_J)
    (hadjJ : formAdj (RingHom.id F) G e_J = e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S')) e')
    (hsplit' : e' ≠ ε' ∧ formAdj (RingHom.id F) G e' ≠ e' ∧
      ε' = e' + formAdj (RingHom.id F) G e')
    (htie : e_J * ε' = e_J) : False := by
  have he'A : e' ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hstarA : formAdj (RingHom.id F) G e' ∈ Algebra.adjoin F (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG hSiso he'A
  have hle : e_J * (e' + formAdj (RingHom.id F) G e') = e_J := by
    rw [← hsplit'.2.2]; exact htie
  exact selfDual_not_below_dualPair G hG (fun a b ha hb => (adjoin_comm hS a ha b hb).eq) heJ
    hadjJ he'A hstarA he'.2.1 hle

end CFSG.StandardType.ClassicalPosition.NbrLeaf
