module

public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem spUCited_normalizer_map_eq {G : Type} [Group G] (α : MulAut G) (H : Subgroup G) :
    (Subgroup.normalizer (H : Set G)).map α.toMonoidHom =
      Subgroup.normalizer ((H.map α.toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H α

private lemma spUCited_map_map_inv {G : Type} [Group G] (α : MulAut G) (H : Subgroup G) :
    (H.map α.toMonoidHom).map α⁻¹.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (α⁻¹).toMonoidHom.comp α.toMonoidHom = MonoidHom.id G := by
    ext x
    simpa using α.inv_apply_self x
  rw [h, Subgroup.map_id]

private lemma spUCited_map_inv_map {G : Type} [Group G] (α : MulAut G) (H : Subgroup G) :
    (H.map α⁻¹.toMonoidHom).map α.toMonoidHom = H := by
  simpa using spUCited_map_map_inv (G := G) (α⁻¹) H

theorem spUCited_map_eq_of_unique_cover {G : Type} [Group G] {U R P : Subgroup G}
    (hBP : Subgroup.normalizer (U : Set G) ≤ P)
    (hcov : ∀ A : Subgroup G, Subgroup.normalizer (U : Set G) ≤ A → A ≤ P →
      A = Subgroup.normalizer (U : Set G) ∨ A = P)
    (hnot : ¬ P ≤ Subgroup.normalizer (R : Set G))
    (huniq : ∀ P' : Subgroup G, Subgroup.normalizer (U : Set G) ≤ P' →
      (∀ A : Subgroup G, Subgroup.normalizer (U : Set G) ≤ A → A ≤ P' →
        A = Subgroup.normalizer (U : Set G) ∨ A = P') →
      ¬ P' ≤ Subgroup.normalizer (R : Set G) → P' = P)
    (α : MulAut G) (hU : U.map α.toMonoidHom = U) (hR : R.map α.toMonoidHom = R) :
    P.map α.toMonoidHom = P := by
  let B : Subgroup G := Subgroup.normalizer (U : Set G)
  let N : Subgroup G := Subgroup.normalizer (R : Set G)
  have hB : B.map α.toMonoidHom = B := by
    rw [spUCited_normalizer_map_eq α U, hU]
  have hN : N.map α.toMonoidHom = N := by
    rw [spUCited_normalizer_map_eq α R, hR]
  have hBinv : B.map α⁻¹.toMonoidHom = B := by
    calc B.map α⁻¹.toMonoidHom = (B.map α.toMonoidHom).map α⁻¹.toMonoidHom := by rw [hB]
      _ = B := spUCited_map_map_inv α B
  have hNinv : N.map α⁻¹.toMonoidHom = N := by
    calc N.map α⁻¹.toMonoidHom = (N.map α.toMonoidHom).map α⁻¹.toMonoidHom := by rw [hN]
      _ = N := spUCited_map_map_inv α N
  have hBP' : B ≤ P.map α.toMonoidHom := by
    calc B = B.map α.toMonoidHom := hB.symm
      _ ≤ P.map α.toMonoidHom := Subgroup.map_mono hBP
  have hcov' : ∀ A : Subgroup G, B ≤ A → A ≤ P.map α.toMonoidHom →
      A = B ∨ A = P.map α.toMonoidHom := by
    intro A hBA hAP
    have hB₀ : B ≤ A.map α⁻¹.toMonoidHom := by
      calc B = B.map α⁻¹.toMonoidHom := hBinv.symm
        _ ≤ A.map α⁻¹.toMonoidHom := Subgroup.map_mono hBA
    have hA₀P : A.map α⁻¹.toMonoidHom ≤ P := by
      calc A.map α⁻¹.toMonoidHom ≤ (P.map α.toMonoidHom).map α⁻¹.toMonoidHom :=
            Subgroup.map_mono hAP
        _ = P := spUCited_map_map_inv α P
    rcases hcov (A.map α⁻¹.toMonoidHom) hB₀ hA₀P with h | h
    · left
      calc A = (A.map α⁻¹.toMonoidHom).map α.toMonoidHom :=
            (spUCited_map_inv_map α A).symm
        _ = B.map α.toMonoidHom := by rw [h]
        _ = B := hB
    · right
      calc A = (A.map α⁻¹.toMonoidHom).map α.toMonoidHom :=
            (spUCited_map_inv_map α A).symm
        _ = P.map α.toMonoidHom := by rw [h]
  have hnot' : ¬ P.map α.toMonoidHom ≤ N := by
    intro h
    apply hnot
    calc P = (P.map α.toMonoidHom).map α⁻¹.toMonoidHom :=
          (spUCited_map_map_inv α P).symm
      _ ≤ N.map α⁻¹.toMonoidHom := Subgroup.map_mono h
      _ = N := hNinv
  exact huniq (P.map α.toMonoidHom) hBP' hcov' hnot'

end CFSG.LocalAnalysis.WeakClosure81

end
