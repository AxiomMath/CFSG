module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow subgroups of PSL(2,q)

This module isolates the cardinality and upper-unitriangular calculation used
to identify Sylow subgroups in Dickson's classification.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups

universe u

/-- The field exponent in Huppert II.8.27 is nonzero. -/
public theorem huppert_II_8_27_field_exponent_ne_zero
    {F : Type u} [Field F] [Finite F] {p f : ℕ}
    (hFcard : Nat.card F = p ^ f) :
    f ≠ 0 := by
  intro hf
  subst f
  have hcard : Nat.card F = 1 := by
    simpa using hFcard
  exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard

/-- Huppert II.8.2(a): every Sylow `p`-subgroup of `PSL(2,p^f)` is
isomorphic to the additive group of the defining field. -/
public theorem huppert_II_8_2_a_sylow_equiv_additive
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (Q : Sylow p (PSL2MatrixGroup F)) :
    Nonempty (Multiplicative F ≃* Q) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
        Nat.card (rootsOfUnity 2 F) =
          Nat.gcd (Nat.card F - 1) 2 := by
      let e :=
        Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
          Units.val_injective
      have he :
          Nat.card (rootsOfUnity 2 F) =
            Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
        Nat.card_congr e
      rw [Units.val_set_image_rootsOfUnity_two] at he
      by_cases hp_two : p = 2
      · have htwo : (2 : F) = 0 := by
          subst p
          exact CharP.cast_eq_zero F 2
        have hneg_one : (-1 : F) = 1 := by
          apply (neg_eq_iff_add_eq_zero).2
          have hone_add_one : (1 : F) + 1 = 0 := by
            rw [show (1 : F) + 1 = 2 by norm_num, htwo]
          exact hone_add_one
        have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
          simpa [hneg_one] using he
        have hq_even : Even (Nat.card F) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
          rw [hFcard, hp_two, hk, pow_succ]
          use 2 ^ k
          ring
        have hq_sub_one_odd : Odd (Nat.card F - 1) := by
          rw [← Nat.not_even_iff_odd]
          intro heven
          have hparity :=
            (Nat.even_sub (show 1 ≤ Nat.card F from (Finite.one_lt_card (α := F)).le)).mp
              heven
          exact Nat.not_even_one (hparity.mp hq_even)
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
        rw [hleft, hgcd]
      · have hring_char_ne_two : ringChar F ≠ 2 := by
          rw [ringChar.eq F p]
          exact hp_two
        have hneg_one : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
        have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
          simpa [hneg_one, Ne.symm hneg_one] using he
        have hq_odd : Odd (Nat.card F) := by
          rw [hFcard]
          exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
        have htwo_dvd : 2 ∣ Nat.card F - 1 := by
          rcases hq_odd with ⟨k, hk⟩
          use k
          omega
        have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
          Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
        rw [hleft, hgcd]
  have hcard_psl :
      Nat.card (PSL2MatrixGroup F) * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F * (Nat.card F ^ 2 - 1) := by
    have hcard_sl :
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
          Nat.card F * (Nat.card F ^ 2 - 1) := by
      have hdet_range_top :
          (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ := by
        ext u
        constructor
        · intro _
          simp
        · intro _
          let diagonalGL : GL (Fin 2) F :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              (Matrix.diagonal ![(u : F), 1]) (by
                simp [Matrix.det_diagonal, Fin.prod_univ_two])
          refine ⟨diagonalGL, ?_⟩
          ext
          simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
      have hGL :
          Nat.card (GL (Fin 2) F) =
            (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
        simpa [Fin.prod_univ_two] using
          (Matrix.card_GL_field (𝔽 := F) 2)
      let detHom :=
        Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
      have hRange :
          Nat.card detHom.range = Nat.card F - 1 := by
        rw [hdet_range_top]
        simpa using (Fintype.card_units (α := F))
      have hmul :
          Nat.card detHom.range * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) F) := by
        rw [← Subgroup.index_ker detHom]
        exact detHom.ker.index_mul_card
      have hker :
          Nat.card detHom.ker =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        have hq : 1 < Nat.card F := Finite.one_lt_card
        have hdiff :
            Nat.card F ^ 2 - Nat.card F =
              Nat.card F * (Nat.card F - 1) := by
          rw [pow_two]
          calc
            Nat.card F * Nat.card F - Nat.card F =
                Nat.card F * Nat.card F - Nat.card F * 1 := by simp
            _ = Nat.card F * (Nat.card F - 1) :=
              (Nat.mul_sub_left_distrib _ _ _).symm
        have hcancel :
            (Nat.card F - 1) * Nat.card detHom.ker =
              (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
          calc
            (Nat.card F - 1) * Nat.card detHom.ker =
                Nat.card (GL (Fin 2) F) := by
              rw [hRange] at hmul
              exact hmul
            _ = (Nat.card F ^ 2 - 1) *
                (Nat.card F ^ 2 - Nat.card F) := hGL
            _ = (Nat.card F - 1) *
                (Nat.card F * (Nat.card F ^ 2 - 1)) := by
              rw [hdiff]
              ring
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F))) hcancel
      calc
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
            Nat.card detHom.ker := by
          let slEquivDetKer :
              Matrix.SpecialLinearGroup (Fin 2) F ≃ detHom.ker := by
            refine Equiv.ofBijective
              (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
                exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
            constructor
            · intro A B h
              apply Matrix.SpecialLinearGroup.toGL_injective
              exact congrArg Subtype.val h
            · intro A
              refine ⟨⟨(A : GL (Fin 2) F), ?_⟩, ?_⟩
              · have hmem := A.property
                change
                  Matrix.GeneralLinearGroup.det
                    (A : GL (Fin 2) F) = 1 at hmem
                exact Units.ext_iff.mp hmem
              · apply Subtype.ext
                apply Matrix.GeneralLinearGroup.ext
                intro i j
                rfl
          exact Nat.card_congr slEquivDetKer
        _ = Nat.card F * (Nat.card F ^ 2 - 1) := hker

    have hcard_center :
        Nat.card
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) =
          Nat.gcd (Nat.card F - 1) 2 := by
      rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
          (R := F) (n := Fin 2) 0).toEquiv]
      simpa using hcard_roots
    calc
      Nat.card (PSL2MatrixGroup F) *
          Nat.gcd (Nat.card F - 1) 2 =
          Nat.card (PSL2MatrixGroup F) *
            Nat.card
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) := by
            rw [hcard_center]
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))).symm
      _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_sl
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    projectiveUnipotentAddChar F
  have h_unipotent_injective : Function.Injective unipotent :=
    projectiveUnipotentAddChar_injective F
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_index_not_dvd : ¬ p ∣ U.index := by
    have hindex_card : U.index * Nat.card U = Nat.card (PSL2MatrixGroup F) :=
      U.index_mul_card
    have hindex_gcd :
        U.index * Nat.gcd (Nat.card F - 1) 2 = Nat.card F ^ 2 - 1 := by
      have hmul :
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
            Nat.card F * (Nat.card F ^ 2 - 1) := by
        calc
          Nat.card F * (U.index * Nat.gcd (Nat.card F - 1) 2) =
              (U.index * Nat.card U) * Nat.gcd (Nat.card F - 1) 2 := by
                rw [hUcard]
                ring
          _ = Nat.card (PSL2MatrixGroup F) *
                Nat.gcd (Nat.card F - 1) 2 := by rw [hindex_card]
          _ = Nat.card F * (Nat.card F ^ 2 - 1) := hcard_psl
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    intro hp_index
    have hp_bad : p ∣ Nat.card F ^ 2 - 1 := by
      rw [← hindex_gcd]
      exact dvd_mul_of_dvd_left hp_index _
    have hf_ne_zero : f ≠ 0 :=
      huppert_II_8_27_field_exponent_ne_zero hFcard
    have hp_card : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p hf_ne_zero
    have hp_sq : p ∣ Nat.card F ^ 2 := dvd_pow hp_card (by norm_num)
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_sq hp_bad
      have hpos : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
      have hsub : Nat.card F ^ 2 - (Nat.card F ^ 2 - 1) = 1 := by omega
      rw [hsub] at h
      exact h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  let ambientSylow : Sylow p (PSL2MatrixGroup F) :=
    hU_isPGroup.toSylow hU_index_not_dvd
  let eU : Multiplicative F ≃* U :=
    MulEquiv.ofBijective unipotent.toMonoidHom.rangeRestrict
      ⟨by
        intro a b hab
        exact h_unipotent_injective (congrArg Subtype.val hab),
        MonoidHom.rangeRestrict_surjective _⟩
  have hAmbient : (ambientSylow : Subgroup (PSL2MatrixGroup F)) = U := rfl
  let eAmbient : Multiplicative F ≃* ambientSylow :=
    eU.trans (MulEquiv.subgroupCongr hAmbient.symm)
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq
      (α := Sylow p (PSL2MatrixGroup F))
      (PSL2MatrixGroup F) ambientSylow Q
  let eConj : ambientSylow ≃*
      (g • ambientSylow : Sylow p (PSL2MatrixGroup F)) :=
    (MulAut.conj g).subgroupMap ambientSylow
  rw [hg] at eConj
  exact ⟨eAmbient.trans eConj⟩

end Dickson
end CFSG.Glauberman
