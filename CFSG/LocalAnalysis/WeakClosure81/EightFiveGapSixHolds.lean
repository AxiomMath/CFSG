module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSix
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Core
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Transport
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Orthogonal
open Matrix

private lemma natCast_three_eq_zero_of_card_eq_three {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) : (3 : F) = 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 3 := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨p, hchar, n, hpprime, hpow⟩ := FiniteField.card' F
  have hpow3 : 3 = p ^ (n : ℕ) := by rw [← hpow, hcard]
  have hpdvd : p ∣ 3 := hpow3 ▸ dvd_pow_self p n.pos.ne'
  have hp3 : p = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hpdvd with h | h
    · exact absurd h hpprime.ne_one
    · exact h
  haveI : CharP F 3 := hp3 ▸ hchar
  exact CharP.cast_eq_zero F 3

private lemma map_mulAut_symm_map {G : Type*} [Group G] (H : Subgroup G) (e : MulAut G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private lemma map_orthogonalMinus_eq_map_conj {F : Type*} [Field F] {b c : F}
    (P : GL Orth6Minus.Six F)
    (hP : ∀ v : Orth6Minus.Six → F,
      CFSG.PGLModel.minusQuadForm 2 b c
        ((P : Matrix Orth6Minus.Six Orth6Minus.Six F) *ᵥ v) = sumSqForm v) :
    (CFSG.PGLModel.orthogonalMinus 2 F b c).map Matrix.ProjGenLinGroup.mk =
      ((Orth6Minus.orthSix F).map Matrix.ProjGenLinGroup.mk).map
        (MulAut.conj (Matrix.ProjGenLinGroup.mk P)).toMonoidHom := by
  have horth : CFSG.PGLModel.orthogonalMinus 2 F b c =
      (Orth6Minus.orthSix F).map (MulAut.conj P).toMonoidHom := by
    rw [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup_eq_map_conj P hP]
  rw [horth, Subgroup.map_map, Subgroup.map_map]
  have hcomp : Matrix.ProjGenLinGroup.mk.comp (MulAut.conj P).toMonoidHom =
      (MulAut.conj (Matrix.ProjGenLinGroup.mk P)).toMonoidHom.comp
        Matrix.ProjGenLinGroup.mk := by
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [hcomp]

private lemma map_projOmegaMinus_eq_map_conj {F : Type*} [Field F] {b c : F}
    (P : GL Orth6Minus.Six F)
    (hP : ∀ v : Orth6Minus.Six → F,
      CFSG.PGLModel.minusQuadForm 2 b c
        ((P : Matrix Orth6Minus.Six Orth6Minus.Six F) *ᵥ v) = sumSqForm v) :
    CFSG.PGLModel.projOmegaMinus 2 F b c =
      (CFSG.PGLModel.projImage ⁅Orth6Minus.orthSix F, Orth6Minus.orthSix F⁆).map
        (MulAut.conj (Matrix.ProjGenLinGroup.mk P)).toMonoidHom := by
  have horth : CFSG.PGLModel.orthogonalMinus 2 F b c =
      (Orth6Minus.orthSix F).map (MulAut.conj P).toMonoidHom := by
    rw [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup_eq_map_conj P hP]
  rw [CFSG.PGLModel.projOmegaMinus, horth, ← Subgroup.map_commutator,
    CFSG.PGLModel.projImage_map_conj]

theorem orth6MinusOddTranspFact_holds : Orth6MinusOddTranspFact := by
  intro Y _ _ hY d _ hd
  obtain ⟨F, hField, hFinite, hFcard, b, c, hbc, N, hOmegaN, hNhi, ⟨e⟩⟩ := hY
  obtain ⟨P, hP⟩ := Orth6Minus.exists_minusQuadForm_mulVec_eq_sumSqForm hFcard hbc
  let ca : MulAut (Matrix.ProjGenLinGroup Orth6Minus.Six F) :=
    MulAut.conj (Matrix.ProjGenLinGroup.mk P)
  let f : Y →* Matrix.ProjGenLinGroup Orth6Minus.Six F :=
    ca.symm.toMonoidHom.comp (N.subtype.comp e.toMonoidHom)
  have hfr : f.range = N.map ca.symm.toMonoidHom := by
    change (ca.symm.toMonoidHom.comp (N.subtype.comp e.toMonoidHom)).range =
      N.map ca.symm.toMonoidHom
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top, Subgroup.range_subtype]
  have hlo : CFSG.PGLModel.projImage ⁅Orth6Minus.orthSix F, Orth6Minus.orthSix F⁆ ≤
      f.range := by
    have hmap : (CFSG.PGLModel.projImage ⁅Orth6Minus.orthSix F,
        Orth6Minus.orthSix F⁆).map ca.toMonoidHom ≤ N := by
      rw [← map_projOmegaMinus_eq_map_conj P hP]
      exact hOmegaN
    have hconj := Subgroup.map_mono (f := ca.symm.toMonoidHom) hmap
    rw [map_mulAut_symm_map] at hconj
    rwa [hfr]
  have hhi : f.range ≤ (Orth6Minus.orthSix F).map Matrix.ProjGenLinGroup.mk := by
    have hmap : N ≤ ((Orth6Minus.orthSix F).map Matrix.ProjGenLinGroup.mk).map
        ca.toMonoidHom := by
      rw [← map_orthogonalMinus_eq_map_conj P hP]
      exact hNhi
    have hconj := Subgroup.map_mono (f := ca.symm.toMonoidHom) hmap
    rw [map_mulAut_symm_map] at hconj
    rwa [hfr]
  exact Orth6Minus.even_index_centralizer_of_isOddTransp
    (natCast_three_eq_zero_of_card_eq_three hFcard) f (by
      intro x y hxy
      exact e.injective (Subtype.ext (ca.symm.injective hxy))) hlo hhi d hd.2.1

theorem w3Lem85TwoGap6_holds : W3Lem85TwoGap6 :=
  w3Lem85TwoGap6_of_fact orth6MinusOddTranspFact_holds

end CFSG.LocalAnalysis.WeakClosure81
