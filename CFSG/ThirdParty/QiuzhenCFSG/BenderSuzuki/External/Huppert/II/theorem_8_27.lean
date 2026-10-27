module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

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
  let _ : Fintype F := Fintype.ofFinite F
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
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add_eq_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        change (!![1, a + b; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
          ((!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) *
            (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F)) i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, add_comm]
    }
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).compAddChar
        unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    intro a b hab
    have hdiff : unipotent (a - b) = 1 := by
      rw [sub_eq_add_neg, unipotent.map_add_eq_mul,
        unipotent.map_neg_eq_inv, hab, mul_inv_cancel]
    have hcenter :
        unipotentSL (a - b) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      exact (QuotientGroup.eq_one_iff (unipotentSL (a - b))).mp hdiff
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
    have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    have hentry :
        (↑(unipotentSL (a - b)) : Matrix (Fin 2) (Fin 2) F) 0 1 = a - b := by
      change (!![1, a - b; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 1 = a - b
      rfl
    apply sub_eq_zero.mp
    simpa [Matrix.scalar_apply, hentry] using hab0.symm
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

private theorem hsplit_matrix_diag_or_antidiag
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (a b : Fˣ) (r : F)
    (ha_ne_inv : (a : F) ≠ (a⁻¹ : F))
    (heq :
      !![(b : F), 0; 0, (b⁻¹ : F)] * Matrix.scalar (Fin 2) r *
          (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          !![(a : F), 0; 0, (a⁻¹ : F)]) :
    (A 0 1 = 0 ∧ A 1 0 = 0) ∨
      (A 0 0 = 0 ∧ A 1 1 = 0) := by
  have h00 := congrFun (congrFun heq (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun heq (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun heq (1 : Fin 2)) (1 : Fin 2)
  simp [Matrix.mul_apply] at h00 h01 h10 h11
  by_cases hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · right
    refine ⟨hA00, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA00, zero_mul, zero_sub] at hdet
    have hA01 : A 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul, neg_zero] at hdet
      exact zero_ne_one hdet
    have hA10 : A 1 0 ≠ 0 := by
      intro h
      rw [h, mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    by_contra hA11
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)
  · left
    have hbr_a : (b : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA00
      simpa [mul_assoc, mul_comm] using h00
    have hA01 : A 0 1 = 0 := by
      by_contra hA01
      have hbr_ainv : (b : F) * r = (a⁻¹ : F) := by
        apply mul_right_cancel₀ hA01
        simpa [mul_assoc, mul_comm] using h01
      exact ha_ne_inv (hbr_a.symm.trans hbr_ainv)
    refine ⟨hA01, ?_⟩
    have hdet := A.property
    rw [Matrix.det_fin_two, hA01, zero_mul, sub_zero] at hdet
    have hA11 : A 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have hbinvr_ainv : (b⁻¹ : F) * r = (a⁻¹ : F) := by
      apply mul_right_cancel₀ hA11
      simpa [mul_assoc, mul_comm] using h11
    by_contra hA10
    have hbinvr_a : (b⁻¹ : F) * r = (a : F) := by
      apply mul_right_cancel₀ hA10
      simpa [mul_assoc, mul_comm] using h10
    exact ha_ne_inv (hbinvr_a.symm.trans hbinvr_ainv)


set_option maxHeartbeats 1000000 in

private theorem h84_nonsplit_torus_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) =
        2 * Nat.card S ∧
      (∃ w : PSL2MatrixGroup F,
        w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
        w ∉ S ∧
        w * w = 1 ∧
        (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
        Nat.card (S ⊔ Subgroup.zpowers w :
          Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
        ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S ⊔ Subgroup.zpowers w) ∧
      (∀ y : PSL2MatrixGroup F, y ∈ S → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ S →
            g ∈ Subgroup.normalizer
              (S : Set (PSL2MatrixGroup F))) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F) →
        (¬ ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) →
        ∃ g : PSL2MatrixGroup F,
          (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            S.map (MulAut.conj g).toMonoidHom := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
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
  have hreflection_candidate_data
      (T : Subgroup (PSL2MatrixGroup F)) (w : PSL2MatrixGroup F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) : Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card T := by
    let Z : Subgroup (PSL2MatrixGroup F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      let _ : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (PSL2MatrixGroup F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    let _ : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : PSL2MatrixGroup F) ∈ T ⊓ Z := by
        change (x : PSL2MatrixGroup F) ∈ T ∧ (x : PSL2MatrixGroup F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : PSL2MatrixGroup F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (PSL2MatrixGroup F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul_card.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let E := FiniteField.Extension F p 2
  let _ : Fintype E := Fintype.ofFinite E
  let normUnits : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let K : Subgroup Eˣ := normUnits.ker
  have hnormUnits_surjective : Function.Surjective normUnits := by
    exact FiniteField.unitsMap_norm_surjective F E
  have hnormUnits_range : normUnits.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hnormUnits_surjective
  have hK_index : K.index = Nat.card F - 1 := by
    calc
      K.index = Nat.card normUnits.range := Subgroup.index_ker normUnits
      _ = Nat.card Fˣ := by rw [hnormUnits_range]; simp
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hE_card : Nat.card E = Nat.card F ^ 2 := by
    exact FiniteField.natCard_extension F p 2
  have hK_mul_card :
      (Nat.card F - 1) * Nat.card K = Nat.card F ^ 2 - 1 := by
    calc
      (Nat.card F - 1) * Nat.card K = K.index * Nat.card K := by rw [hK_index]
      _ = Nat.card Eˣ := K.index_mul_card
      _ = Nat.card E - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := E))
      _ = Nat.card F ^ 2 - 1 := by rw [hE_card]
  have hq_factor :
      (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa [mul_comm] using
      (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have hdegree_exp :
      (Nat.card E - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [hE_card, ← hq_factor]
    simpa [mul_comm] using Nat.mul_div_left (Nat.card F + 1)
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
  have hfrob_inv (x : K) :
      FiniteField.Extension.frob F p 2 (x.1 : E) = ((x.1 : E)⁻¹) := by
    have hxker := x.property
    change normUnits x.1 = 1 at hxker
    have hxnorm := congrArg Units.val hxker
    change Algebra.norm F (x.1 : E) = 1 at hxnorm
    have hpow : (x.1 : E) ^ (Nat.card F + 1) = 1 := by
      have h := FiniteField.algebraMap_norm_eq_pow
        (K := F) (K' := E) (x := (x.1 : E))
      rw [hxnorm, map_one, hdegree_exp] at h
      exact h.symm
    rw [FiniteField.Extension.frob_apply]
    apply mul_right_cancel₀ (x.1.ne_zero)
    calc
      (x.1 : E) ^ Nat.card F * (x.1 : E) =
          (x.1 : E) ^ (Nat.card F + 1) := (pow_succ _ _).symm
      _ = 1 := hpow
      _ = (x.1 : E)⁻¹ * (x.1 : E) := by
        rw [inv_mul_cancel₀ x.1.ne_zero]
  have hK_card : Nat.card K = Nat.card F + 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
    exact hK_mul_card.trans hq_factor.symm
  have hK_cyclic : IsCyclic K := isCyclic_subgroup_units K
  have hidx :
      Fintype.card (Module.Free.ChooseBasisIndex F E) =
        Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Fintype.card_fin]
    simpa [E] using (FiniteField.finrank_extension F p 2)
  let eidx : Module.Free.ChooseBasisIndex F E ≃ Fin 2 :=
    Fintype.equivOfCardEq hidx
  let b : Module.Basis (Fin 2) F E :=
    (Module.Free.chooseBasis F E).reindex eidx
  let nonsplitSL : K →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun x =>
        ⟨Algebra.leftMulMatrix b (x.1 : E), by
          rw [← Algebra.norm_eq_matrix_det b]
          have hxker := x.property
          change normUnits x.1 = 1 at hxker
          simpa [normUnits] using congrArg Units.val hxker⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (Algebra.leftMulMatrix b) ((x.1 : E) * (y.1 : E)) =
          (Algebra.leftMulMatrix b) (x.1 : E) * (Algebra.leftMulMatrix b) (y.1 : E)
        exact (Algebra.leftMulMatrix b).map_mul _ _ }
  have hnonsplitSL_injective : Function.Injective nonsplitSL := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    apply Algebra.leftMulMatrix_injective b
    have hmat := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F)) hxy
    change Algebra.leftMulMatrix b (x.1 : E) =
      Algebra.leftMulMatrix b (y.1 : E) at hmat
    exact hmat
  let nonsplitTorus : K →* PSL2MatrixGroup F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        nonsplitSL
  have hnonsplit_mem_ker_iff (x : K) :
      x ∈ nonsplitTorus.ker ↔
        ∃ r : F, r ^ 2 = 1 ∧ algebraMap F E r = (x.1 : E) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hcenter : nonsplitSL x ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (nonsplitSL x)).mp hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hcenter
      rcases hcenter with ⟨r, hr, hscalar⟩
      refine ⟨r, by simpa using hr, ?_⟩
      apply Algebra.leftMulMatrix_injective b
      calc
        Algebra.leftMulMatrix b (algebraMap F E r) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r :=
          (Algebra.leftMulMatrix b).commutes r
        _ = Matrix.scalar (Fin 2) r := rfl
        _ = (nonsplitSL x : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
        _ = Algebra.leftMulMatrix b (x.1 : E) := rfl
    · rintro ⟨r, hr, hxr⟩
      apply (QuotientGroup.eq_one_iff (nonsplitSL x)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨r, by simpa using hr, ?_⟩
      change Matrix.scalar (Fin 2) r = Algebra.leftMulMatrix b (x.1 : E)
      rw [← hxr]
      calc
        Matrix.scalar (Fin 2) r =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E r) :=
          ((Algebra.leftMulMatrix b).commutes r).symm
  let RootF := {r : F // r ^ 2 = 1}
  let kerScalar (x : nonsplitTorus.ker) : F :=
    Classical.choose ((hnonsplit_mem_ker_iff x.1).mp x.property)
  have hkerScalar_spec (x : nonsplitTorus.ker) :
      kerScalar x ^ 2 = 1 ∧
        algebraMap F E (kerScalar x) = (x.1.1 : E) :=
    Classical.choose_spec ((hnonsplit_mem_ker_iff x.1).mp x.property)
  let scalarK (r : RootF) : K :=
    ⟨Units.map (algebraMap F E)
        (Units.mk0 r.1 (by
          intro hr0
          have hr := r.property
          simp [hr0] at hr)), by
      change normUnits
        (Units.map (algebraMap F E)
          (Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr))) = 1
      apply Units.ext
      change Algebra.norm F (algebraMap F E r.1) = 1
      rw [Algebra.norm_algebraMap_of_basis b]
      simpa using r.property⟩
  let scalarKer (r : RootF) : nonsplitTorus.ker :=
    ⟨scalarK r, (hnonsplit_mem_ker_iff (scalarK r)).mpr
      ⟨r.1, r.property, by simp [scalarK]⟩⟩
  let eKerRoot : nonsplitTorus.ker ≃ RootF :=
    { toFun := fun x => ⟨kerScalar x, (hkerScalar_spec x).1⟩
      invFun := scalarKer
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        simpa [scalarKer, scalarK] using (hkerScalar_spec x).2
      right_inv := by
        intro r
        apply Subtype.ext
        apply (algebraMap F E).injective
        calc
          algebraMap F E (kerScalar (scalarKer r)) =
              ((scalarKer r).1.1 : E) :=
            (hkerScalar_spec (scalarKer r)).2
          _ = algebraMap F E r.1 := by simp [scalarKer, scalarK] }
  let rootVal : rootsOfUnity 2 F ≃ RootF :=
    { toFun := fun a =>
        ⟨(a.1 : F), by simpa using congrArg Units.val a.property⟩
      invFun := fun r =>
        ⟨Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr),
          by
            rw [mem_rootsOfUnity]
            apply Units.ext
            simpa using r.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }
  have hnonsplit_ker_card :
      Nat.card nonsplitTorus.ker =
        Nat.gcd (Nat.card F - 1) 2 := by
    calc
      Nat.card nonsplitTorus.ker = Nat.card RootF :=
        Nat.card_congr eKerRoot
      _ = Nat.card (rootsOfUnity 2 F) :=
        (Nat.card_congr rootVal).symm
      _ = Nat.gcd (Nat.card F - 1) 2 := hcard_roots
  have hnonsplit_range_mul :
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F + 1 := by
    calc
      Nat.card nonsplitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          nonsplitTorus.ker.index * Nat.card nonsplitTorus.ker := by
        rw [Subgroup.index_ker, hnonsplit_ker_card]
      _ = Nat.card K := nonsplitTorus.ker.index_mul_card
      _ = Nat.card F + 1 := hK_card
  have hnonsplit_range_card :
      Nat.card nonsplitTorus.range =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hnonsplit_range_mul
  have hnonsplitTorus_cyclic : IsCyclic nonsplitTorus.range := by
    let _ : IsCyclic K := hK_cyclic
    exact isCyclic_of_surjective nonsplitTorus.rangeRestrict
      nonsplitTorus.rangeRestrict_surjective
  let sigma : E ≃ₐ[F] E :=
    FiniteField.Extension.frob F p 2
  have hsigma_sq (x : E) : sigma (sigma x) = x := by
    change FiniteField.Extension.frob F p 2
      (FiniteField.Extension.frob F p 2 x) = x
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
      ← pow_mul]
    have hcard : Nat.card F * Nat.card F = Fintype.card E := by
      rw [← pow_two, ← FiniteField.natCard_extension F p 2,
        Nat.card_eq_fintype_card]
    rw [hcard]
    exact FiniteField.pow_card x
  have hsigma_ne_one : sigma ≠ 1 := by
    intro hsigma
    change FiniteField.Extension.frob F p 2 = 1 at hsigma
    have hall : ∀ g : E ≃ₐ[F] E, g = 1 := by
      intro g
      obtain ⟨i, hi, hpow⟩ :=
        FiniteField.Extension.exists_frob_pow_eq
          (k := F) (p := p) (n := 2) g
      rw [← hpow, hsigma, one_pow]
    let _ : Subsingleton (E ≃ₐ[F] E) :=
      ⟨fun a d => (hall a).trans (hall d).symm⟩
    have hone : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_unique
    have htwo : Nat.card (E ≃ₐ[F] E) = 2 :=
      FiniteField.natCard_algEquiv_extension F p 2
    omega
  let sigmaMat : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix b b sigma.toLinearEquiv
  have hsigma_inv (x : K) :
      sigma (x.1 : E) = ((x⁻¹ : K).1 : E) := by
    rw [show sigma = FiniteField.Extension.frob F p 2 from rfl,
      hfrob_inv x]
    simp
  have hsigmaMat_mul (x : E) :
      sigmaMat * Algebra.leftMulMatrix b x =
        Algebra.leftMulMatrix b (sigma x) * sigmaMat := by
    dsimp [sigmaMat]
    rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext y
    simp [LinearMap.comp_apply, Algebra.lmul]
  have hsigmaMat_sq : sigmaMat * sigmaMat = 1 := by
    dsimp [sigmaMat]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext x
    exact hsigma_sq x
  have hsigma_det_unit : IsUnit (Matrix.det sigmaMat) := by
    simpa [sigmaMat] using
      (LinearEquiv.isUnit_det sigma.toLinearEquiv b b)
  have hsigma_det_ne : Matrix.det sigmaMat ≠ 0 :=
    hsigma_det_unit.ne_zero
  obtain ⟨c, hc⟩ :=
    FiniteField.norm_surjective F E (Matrix.det sigmaMat)⁻¹
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst c
    simp only [Algebra.norm_zero] at hc
    exact hsigma_det_ne (inv_eq_zero.mp hc.symm)
  let frobSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨Algebra.leftMulMatrix b c * sigmaMat, by
      rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b, hc]
      exact inv_mul_cancel₀ hsigma_det_ne⟩
  have hc_sigma :
      c * sigma c = algebraMap F E (Algebra.norm F c) := by
    have h := FiniteField.algebraMap_norm_eq_pow
      (K := F) (K' := E) (x := c)
    rw [hdegree_exp] at h
    calc
      c * sigma c = c * c ^ Nat.card F := by
        change c * FiniteField.Extension.frob F p 2 c = _
        rw [FiniteField.Extension.frob_apply]
      _ = c ^ (Nat.card F + 1) := by rw [pow_succ, mul_comm]
      _ = algebraMap F E (Algebra.norm F c) := h.symm
  have hfrobSL_sq_matrix :
      ((frobSL * frobSL : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b
          (algebraMap F E (Algebra.norm F c)) := by
    change (Algebra.leftMulMatrix b c * sigmaMat) *
        (Algebra.leftMulMatrix b c * sigmaMat) =
      Algebra.leftMulMatrix b
        (algebraMap F E (Algebra.norm F c))
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          (Algebra.leftMulMatrix b c * sigmaMat) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b c) * sigmaMat := by
              simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma c) * sigmaMat) *
              sigmaMat := by rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma c)) *
              (sigmaMat * sigmaMat) := by
                simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b (c * sigma c) := by
            rw [hsigmaMat_sq, mul_one, ← map_mul]
      _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) := by rw [hc_sigma]
  have hfrobSL_sq_center :
      frobSL * frobSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨Algebra.norm F c, ?_, ?_⟩
    · have hdet := (frobSL * frobSL).property
      rw [hfrobSL_sq_matrix] at hdet
      have hscalar :
          Algebra.leftMulMatrix b
              (algebraMap F E (Algebra.norm F c)) =
            Matrix.scalar (Fin 2) (Algebra.norm F c) := by
        calc
          _ = algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) :=
            (Algebra.leftMulMatrix b).commutes (Algebra.norm F c)
          _ = _ := rfl
      rw [hscalar] at hdet
      simpa [Matrix.det_fin_two, pow_two] using hdet
    · calc
        Matrix.scalar (Fin 2) (Algebra.norm F c) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) := rfl
        _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) :=
          ((Algebra.leftMulMatrix b).commutes (Algebra.norm F c)).symm
        _ = ((frobSL * frobSL :
            Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := hfrobSL_sq_matrix.symm
  have hleftMul_comm (a d : E) :
      Algebra.leftMulMatrix b a * Algebra.leftMulMatrix b d =
        Algebra.leftMulMatrix b d * Algebra.leftMulMatrix b a := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hfrobSL_mul (x : K) :
      frobSL * nonsplitSL x = nonsplitSL x⁻¹ * frobSL := by
    apply Subtype.ext
    change (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
        Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
          (Algebra.leftMulMatrix b c * sigmaMat)
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b (x.1 : E)) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma (x.1 : E)) * sigmaMat) := by
              rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma (x.1 : E))) * sigmaMat := by
              rw [Matrix.mul_assoc]
      _ = (Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            Algebra.leftMulMatrix b c) * sigmaMat := by
              rw [hleftMul_comm]
      _ = Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [hsigma_inv]
  have hfrobSL_conj (x : K) :
      frobSL * nonsplitSL x * frobSL⁻¹ = nonsplitSL x⁻¹ := by
    calc
      frobSL * nonsplitSL x * frobSL⁻¹ =
          nonsplitSL x⁻¹ * (frobSL * frobSL⁻¹) := by
        rw [hfrobSL_mul, mul_assoc]
      _ = nonsplitSL x⁻¹ := by rw [mul_inv_cancel, mul_one]
  let frobPSL : PSL2MatrixGroup F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL
  have hfrobPSL_sq : frobPSL ^ 2 = 1 := by
    change (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL) ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (frobSL ^ 2)).mpr
    simpa [pow_two] using hfrobSL_sq_center
  have hfrobPSL_not_mem_torus :
      frobPSL ∉ nonsplitTorus.range := by
    rintro ⟨x, hx⟩
    change (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          (nonsplitSL x) =
      (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          frobSL at hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hx with
      ⟨z, hz_center, hz_eq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar' :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
    have hmat := congrArg Subtype.val hz_eq
    change Algebra.leftMulMatrix b (x.1 : E) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix b c * sigmaMat at hmat
    rw [← hscalar'] at hmat
    have hscalarLM :
        Matrix.scalar (Fin 2) r =
          Algebra.leftMulMatrix b (algebraMap F E r) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes r).symm
    rw [hscalarLM, ← map_mul] at hmat
    rw [Algebra.leftMulMatrix_apply] at hmat
    change (LinearMap.toMatrix b b)
        (Algebra.lmul F E ((x.1 : E) * algebraMap F E r)) =
      Algebra.leftMulMatrix b c *
        (LinearMap.toMatrix b b) sigma.toLinearEquiv at hmat
    rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff] at hmat
    have hone := LinearMap.congr_fun hmat (1 : E)
    have hxr : (x.1 : E) * algebraMap F E r = c := by
      simpa [LinearMap.comp_apply, Algebra.lmul] using hone
    have hall : ∀ y : E, sigma y = y := by
      intro y
      have hy := LinearMap.congr_fun hmat y
      change ((x.1 : E) * algebraMap F E r) * y =
        c * sigma y at hy
      rw [hxr] at hy
      exact (mul_left_cancel₀ hc_ne hy).symm
    apply hsigma_ne_one
    ext y
    exact hall y
  have hfrobPSL_conj (x : K) :
      frobPSL * nonsplitTorus x * frobPSL⁻¹ =
        nonsplitTorus x⁻¹ := by
    simpa [frobPSL, nonsplitTorus] using congrArg
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F)))
      (hfrobSL_conj x)
  have hfrobPSL_mem_normalizer :
      frobPSL ∈ Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, (hfrobPSL_conj x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      calc
        nonsplitTorus x⁻¹ =
            frobPSL⁻¹ *
              (frobPSL * nonsplitTorus x⁻¹ * frobPSL⁻¹) *
                frobPSL := by simp [mul_assoc]
        _ = frobPSL⁻¹ * nonsplitTorus x * frobPSL := by
          rw [hfrobPSL_conj]
          rw [inv_inv]
        _ = y := by rw [hx]; simp [mul_assoc]
  let nonsplitDihedralCandidate : Subgroup (PSL2MatrixGroup F) :=
    nonsplitTorus.range ⊔ Subgroup.zpowers frobPSL
  have hnonsplitCandidate_le_normalizer :
      nonsplitDihedralCandidate ≤
        Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    apply sup_le Subgroup.le_normalizer
    exact Subgroup.zpowers_le.2 hfrobPSL_mem_normalizer
  rcases hreflection_candidate_data nonsplitTorus.range frobPSL
      hfrobPSL_mem_normalizer (by simpa [pow_two] using hfrobPSL_sq)
        hfrobPSL_not_mem_torus with
    ⟨hfrob_zpowers_card, hnonsplit_torus_zpowers_disjoint,
      hnonsplitCandidate_card_raw⟩
  have hnonsplitCandidate_card :
      Nat.card nonsplitDihedralCandidate =
        2 * ((Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2) := by
    have hraw :
        Nat.card nonsplitDihedralCandidate =
          2 * Nat.card nonsplitTorus.range := by
      simpa [nonsplitDihedralCandidate] using hnonsplitCandidate_card_raw
    rw [hnonsplit_range_card] at hraw
    exact hraw
  have hnonsplit_lift_classification_of_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (aK : K) (haK_not_ker : aK ∉ nonsplitTorus.ker)
      (hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have haK_not_scalar (r : F) :
        algebraMap F E r ≠ (aK.1 : E) := by
      intro hr
      apply haK_not_ker
      apply (hnonsplit_mem_ker_iff aK).2
      refine ⟨r, ?_, hr⟩
      have hker := aK.property
      change normUnits aK.1 = 1 at hker
      have hv := congrArg Units.val hker
      change Algebra.norm F (aK.1 : E) = 1 at hv
      rw [← hr, Algebra.norm_algebraMap_of_basis b] at hv
      simpa using hv
    rcases hconj_mem with ⟨bK, hbK⟩
    have hq :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) (nonsplitSL bK) =
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)))
            (A * nonsplitSL aK * A⁻¹) := by
      simpa [nonsplitTorus] using hbK
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA : nonsplitSL bK * z * A = A * nonsplitSL aK := by
      calc
        nonsplitSL bK * z * A = (A * nonsplitSL aK * A⁻¹) * A := by
          rw [hzeq]
        _ = A * nonsplitSL aK := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    let rz : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalarLM :
        Matrix.scalar (Fin 2) rz =
          Algebra.leftMulMatrix b (algebraMap F E rz) := by
      calc
        Matrix.scalar (Fin 2) rz =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) rz := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E rz) :=
          ((Algebra.leftMulMatrix b).commutes rz).symm
    let yE : E := (bK.1 : E) * algebraMap F E rz
    have hmat :
        Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) := by
      have hm := congrArg Subtype.val hzeqA
      change Algebra.leftMulMatrix b (bK.1 : E) *
            (z : Matrix (Fin 2) (Fin 2) F) *
              (A : Matrix (Fin 2) (Fin 2) F) =
          (A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E) at hm
      rw [← hscalar] at hm
      rw [hscalarLM, ← map_mul] at hm
      exact hm
    have hAunit :
        IsUnit (Matrix.det (A : Matrix (Fin 2) (Fin 2) F)) := by
      rw [A.property]
      exact isUnit_one
    let Aeq : E ≃ₗ[F] E :=
      Matrix.toLinearEquiv b (A : Matrix (Fin 2) (Fin 2) F) hAunit
    have hA_intertwine (x : E) :
        Aeq ((aK.1 : E) * x) = yE * Aeq x := by
      have hfun := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) F => Matrix.toLin b b M x) hmat
      change Matrix.toLin b b (Algebra.leftMulMatrix b yE *
            (A : Matrix (Fin 2) (Fin 2) F)) x =
          Matrix.toLin b b ((A : Matrix (Fin 2) (Fin 2) F) *
            Algebra.leftMulMatrix b (aK.1 : E)) x at hfun
      rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b yE)
            (A : Matrix (Fin 2) (Fin 2) F) x,
        Matrix.toLin_mul_apply b b b (A : Matrix (Fin 2) (Fin 2) F)
            (Algebra.leftMulMatrix b (aK.1 : E)) x] at hfun
      simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix] at hfun
      change yE * Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) x =
          Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F)
            ((aK.1 : E) * x) at hfun
      simpa [Aeq, Matrix.toLinearEquiv_apply] using hfun.symm
    have hfin : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    have hcoeff : ∀ z : E, ∃ u v : F,
        u • (aK.1 : E) + v • (1 : E) = z := by
      have hLI : LinearIndependent F
          (![(aK.1 : E), 1] : Fin 2 → E) := by
        rw [linearIndependent_fin2]
        exact ⟨one_ne_zero, by
          intro r hr
          exact haK_not_scalar r (by simpa [Algebra.smul_def] using hr)⟩
      have hspan :
          Submodule.span F
              (Set.range (![(aK.1 : E), 1] : Fin 2 → E)) = ⊤ :=
        hLI.span_eq_top_of_card_eq_finrank (by simpa using hfin.symm)
      have hrange :
          Set.range (![(aK.1 : E), 1] : Fin 2 → E) =
            ({(aK.1 : E), 1} : Set E) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hz
          rcases hz with (rfl | hz)
          · exact ⟨0, by simp⟩
          · have : z = 1 := hz
            exact ⟨1, by simp [this]⟩
      intro z
      rw [hrange] at hspan
      apply Submodule.mem_span_pair.mp
      rw [hspan]
      exact Submodule.mem_top
    let d : E := Aeq 1
    have hd : d ≠ 0 := by
      intro hd0
      have h10 : (1 : E) = 0 := Aeq.injective (by simp [d, hd0])
      exact one_ne_zero h10
    let du : Eˣ := Units.mk0 d hd
    let phiLin : E →ₗ[F] E :=
      (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).toLinearMap
    have hphi_apply (z : E) : phiLin z = d⁻¹ * Aeq z := by
      change ((du.mulLeftLinearEquiv F E).symm) (Aeq z) = _
      rw [Units.symm_mulLeftLinearEquiv_apply]
      rfl
    have hphi_one : phiLin 1 = 1 := by
      rw [hphi_apply]
      change d⁻¹ * d = 1
      exact inv_mul_cancel₀ hd
    have hphi_a : phiLin (aK.1 : E) = yE := by
      rw [hphi_apply]
      have ha1 := hA_intertwine 1
      simp only [mul_one] at ha1
      rw [ha1]
      change d⁻¹ * (yE * d) = yE
      calc
        d⁻¹ * (yE * d) = d⁻¹ * (d * yE) := by rw [mul_comm yE d]
        _ = (d⁻¹ * d) * yE := by rw [mul_assoc]
        _ = yE := by rw [inv_mul_cancel₀ hd, one_mul]
    have hphi_a_mul (z : E) :
        phiLin ((aK.1 : E) * z) = phiLin (aK.1 : E) * phiLin z := by
      rw [hphi_apply, hphi_a, hphi_apply, hA_intertwine]
      ac_rfl
    have hphi_mul (z w : E) :
        phiLin (z * w) = phiLin z * phiLin w := by
      obtain ⟨u, v, hz⟩ := hcoeff z
      rw [← hz]
      simp only [add_mul, smul_mul_assoc, map_add, map_smul, hphi_a_mul,
        one_mul, hphi_one]
    let phiHom : E →ₐ[F] E := AlgHom.ofLinearMap phiLin hphi_one hphi_mul
    have hbij : Function.Bijective phiHom := by
      change Function.Bijective phiLin
      exact (Aeq.trans ((du⁻¹).mulLeftLinearEquiv F E)).bijective
    let phi : E ≃ₐ[F] E := AlgEquiv.ofBijective phiHom hbij
    have hphi (z : E) : phi z = d⁻¹ * Aeq z := by
      simpa [phi, phiHom] using hphi_apply z
    obtain ⟨i, hi, hpow⟩ :=
      FiniteField.Extension.exists_frob_pow_eq
        (k := F) (p := p) (n := 2) phi
    have hphi_cases : phi = 1 ∨ phi = sigma := by
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl
      · left
        simpa using hpow.symm
      · right
        simpa [sigma] using hpow.symm
    have hAeq_linear : Aeq.toLinearMap =
        Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) := by
      ext z
      simp [Aeq, Matrix.toLinearEquiv_apply]
    have hAeq_matrix :
        LinearMap.toMatrix b b Aeq.toLinearMap =
          (A : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAeq_linear]
      exact LinearMap.toMatrix_toLin b b _
    rcases hphi_cases with hphi_id | hphi_sigma
    · have hAeq_mul (z : E) : Aeq z = d * z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * z := by rw [hphi_id]; rfl
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d := by
        rw [← hAeq_matrix, Algebra.leftMulMatrix_apply]
        apply congrArg (LinearMap.toMatrix b b)
        ext z
        simpa [Algebra.lmul] using hAeq_mul z
      have hd_norm : Algebra.norm F d = 1 := by
        have hdet := A.property
        rw [hAmatrix, ← Algebra.norm_eq_matrix_det b] at hdet
        exact hdet
      let x : K :=
        ⟨Units.mk0 d hd, by
          change normUnits (Units.mk0 d hd) = 1
          apply Units.ext
          simpa [normUnits] using hd_norm⟩
      left
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change (A : Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b d
      exact hAmatrix
    · have hAeq_mul_sigma (z : E) : Aeq z = d * sigma z := by
        calc
          Aeq z = d * (d⁻¹ * Aeq z) := by
            rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
          _ = d * phi z := by rw [hphi]
          _ = d * sigma z := by rw [hphi_sigma]
      have hAmatrix :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b d * sigmaMat := by
        apply (Matrix.toLin b b).injective
        ext z
        rw [Matrix.toLin_mul_apply b b b (Algebra.leftMulMatrix b d)
          sigmaMat z]
        simp only [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
        change Matrix.toLin b b (A : Matrix (Fin 2) (Fin 2) F) z =
          d * Matrix.toLin b b sigmaMat z
        rw [show Matrix.toLin b b sigmaMat z = sigma z by
          simp [sigmaMat]]
        rw [← hAeq_mul_sigma z]
        rfl
      let u : E := d * c⁻¹
      have hu_ne : u ≠ 0 := mul_ne_zero hd (inv_ne_zero hc_ne)
      have hfactor :
          (A : Matrix (Fin 2) (Fin 2) F) =
            Algebra.leftMulMatrix b u *
              (frobSL : Matrix (Fin 2) (Fin 2) F) := by
        rw [hAmatrix]
        change Algebra.leftMulMatrix b d * sigmaMat =
          Algebra.leftMulMatrix b u *
            (Algebra.leftMulMatrix b c * sigmaMat)
        calc
          Algebra.leftMulMatrix b d * sigmaMat =
              Algebra.leftMulMatrix b ((d * c⁻¹) * c) * sigmaMat := by
                rw [show (d * c⁻¹) * c = d by
                  rw [mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]]
          _ = (Algebra.leftMulMatrix b (d * c⁻¹) *
              Algebra.leftMulMatrix b c) * sigmaMat := by rw [map_mul]
          _ = Algebra.leftMulMatrix b (d * c⁻¹) *
              (Algebra.leftMulMatrix b c * sigmaMat) := by
                rw [Matrix.mul_assoc]
      have hu_norm : Algebra.norm F u = 1 := by
        have hdet := congrArg Matrix.det hfactor
        rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b,
          A.property, frobSL.property, mul_one] at hdet
        exact hdet.symm
      let x : K :=
        ⟨Units.mk0 u hu_ne, by
          change normUnits (Units.mk0 u hu_ne) = 1
          apply Units.ext
          simpa [normUnits] using hu_norm⟩
      right
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change (A : Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b u *
          (frobSL : Matrix (Fin 2) (Fin 2) F)
      exact hfactor
  have hnonsplit_normalizer_lift_classification
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA :
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
            Subgroup.normalizer (nonsplitTorus.range : Set _)) :
      (∃ x : K, A = nonsplitSL x) ∨
        ∃ x : K, A = nonsplitSL x * frobSL := by
    have hnonsplit_range_one_lt : 1 < Nat.card nonsplitTorus.range := by
      rw [hnonsplit_range_card]
      have hq_one : 1 < Nat.card F := Finite.one_lt_card
      have hdpos : 0 < Nat.gcd (Nat.card F - 1) 2 :=
        Nat.gcd_pos_of_pos_right _ (by norm_num)
      by_cases hq2 : Nat.card F = 2
      · have hq2' : Fintype.card F = 2 := by
          simpa [Nat.card_eq_fintype_card] using hq2
        norm_num [hq2']
      · have hq3 : 3 ≤ Nat.card F := by omega
        have hdle : Nat.gcd (Nat.card F - 1) 2 ≤ 2 :=
          Nat.gcd_le_right _ (by norm_num)
        have hmul :
            2 * Nat.gcd (Nat.card F - 1) 2 ≤ Nat.card F + 1 := by omega
        have htwo :
            2 ≤ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 :=
          (Nat.le_div_iff_mul_le hdpos).2 hmul
        omega
    let _ : IsCyclic nonsplitTorus.range := hnonsplitTorus_cyclic
    obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := nonsplitTorus.range)
    have ht_ne : t ≠ 1 := by
      intro ht_one
      have hall_one : ∀ u : nonsplitTorus.range, u = 1 := by
        intro u
        simpa [ht_one] using ht u
      have : Subsingleton nonsplitTorus.range :=
        ⟨fun u v => (hall_one u).trans (hall_one v).symm⟩
      have hcard_one : Nat.card nonsplitTorus.range = 1 := Nat.card_unique
      omega
    rcases t.property with ⟨aK, haK⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro hak
      apply ht_ne
      apply Subtype.ext
      change (t : PSL2MatrixGroup F) = 1
      rw [← haK]
      exact hak
    have hconj_mem :
        (QuotientGroup.mk' (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) F))) A *
              nonsplitTorus aK *
                ((QuotientGroup.mk' (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F))) A)⁻¹ ∈
          nonsplitTorus.range :=
      (Subgroup.mem_normalizer_iff.mp hA (nonsplitTorus aK)).mp
        ⟨aK, rfl⟩
    exact hnonsplit_lift_classification_of_conj
      A aK haK_not_ker hconj_mem
  have hnonsplit_normalizer_sub_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) ≤
        nonsplitDihedralCandidate := by
    intro g hg
    refine QuotientGroup.induction_on g ?_ hg
    intro A hA
    rcases hnonsplit_normalizer_lift_classification A hA with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      exact (show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
        le_sup_left) hxT
    · have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hfrob : frobPSL ∈ Subgroup.zpowers frobPSL :=
        Subgroup.mem_zpowers frobPSL
      change (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
          nonsplitDihedralCandidate
      rw [hx]
      change nonsplitTorus x * frobPSL ∈ nonsplitDihedralCandidate
      exact nonsplitDihedralCandidate.mul_mem
        ((show nonsplitTorus.range ≤ nonsplitDihedralCandidate from
          le_sup_left) hxT)
        ((show Subgroup.zpowers frobPSL ≤ nonsplitDihedralCandidate from
          le_sup_right) hfrob)
  have hnonsplit_normalizer_eq_candidate :
      Subgroup.normalizer (nonsplitTorus.range : Set _) =
        nonsplitDihedralCandidate :=
    le_antisymm hnonsplit_normalizer_sub_candidate
      hnonsplitCandidate_le_normalizer
  have hnonsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ nonsplitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ nonsplitTorus.range →
            g ∈ Subgroup.normalizer
              (nonsplitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨aK, rfl⟩
    have haK_not_ker : aK ∉ nonsplitTorus.ker := by
      intro haK
      apply hy_ne
      exact haK
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hnonsplit_lift_classification_of_conj
        A aK haK_not_ker hAconj with ⟨x, hx⟩ | ⟨x, hx⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      exact Subgroup.le_normalizer ⟨x, rfl⟩
    · change (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F))) A ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      rw [hx]
      change nonsplitTorus x * frobPSL ∈
        Subgroup.normalizer (nonsplitTorus.range : Set _)
      have hxT : nonsplitTorus x ∈ nonsplitTorus.range := ⟨x, rfl⟩
      have hxN : nonsplitTorus x ∈
          Subgroup.normalizer
            (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer hxT
      have hfrobN : frobPSL ∈ Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F)) :=
        hfrobPSL_mem_normalizer
      exact (Subgroup.normalizer
          (nonsplitTorus.range : Set (PSL2MatrixGroup F))).mul_mem
        hxN hfrobN
  have hnonsplit_comm {x y : PSL2MatrixGroup F}
      (hx : x ∈ nonsplitTorus.range)
      (hy : y ∈ nonsplitTorus.range) : Commute x y := by
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    change nonsplitTorus a * nonsplitTorus b =
      nonsplitTorus b * nonsplitTorus a
    simp only [← map_mul]
    rw [mul_comm]
  have hnonsplit_normalizer_eq_candidate_of_le
      (R : Subgroup (PSL2MatrixGroup F))
      (hR_le : R ≤ nonsplitTorus.range) (hR_ne : R ≠ ⊥) :
      Subgroup.normalizer (R : Set _) =
        nonsplitDihedralCandidate := by
    apply le_antisymm
    · intro g hg
      apply hnonsplit_normalizer_sub_candidate
      obtain ⟨r, hr_ne_one⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne
      have hr_ne_one' : (r : PSL2MatrixGroup F) ≠ 1 := by
        intro hr
        apply hr_ne_one
        apply Subtype.ext
        exact hr
      have hgr : g * (r : PSL2MatrixGroup F) * g⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hg (r : PSL2MatrixGroup F)).mp
          r.property
      exact hnonsplit_weakTI (r : PSL2MatrixGroup F)
        (hR_le r.property) hr_ne_one' g (hR_le hgr)
    · apply sup_le
      · intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hnonsplit_comm ht (hR_le hy)
          simpa [hcomm.eq, mul_assoc] using hy
        · intro hy
          have hy' : y = t⁻¹ * (t * y * t⁻¹) * t := by
            simp [mul_assoc]
          have hconjR : t * y * t⁻¹ ∈ R := hy
          have hcomm := hnonsplit_comm
            (nonsplitTorus.range.inv_mem ht) (hR_le hconjR)
          have hfixed :
              t⁻¹ * (t * y * t⁻¹) * t = t * y * t⁻¹ := by
            calc
              t⁻¹ * (t * y * t⁻¹) * t =
                  (t * y * t⁻¹) * t⁻¹ * t := by rw [hcomm.eq]
              _ = t * y * t⁻¹ := by group
          rw [hy', hfixed]
          exact hconjR
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rcases hR_le hy with ⟨a, ha⟩
          have hy_inv : y⁻¹ ∈ R := R.inv_mem hy
          have hconj : frobPSL * y * frobPSL⁻¹ = y⁻¹ := by
            rw [← ha]
            simpa using hfrobPSL_conj a
          rw [hconj]
          exact hy_inv
        · intro hy
          have hyT : frobPSL * y * frobPSL⁻¹ ∈
              nonsplitTorus.range := hR_le hy
          rcases hyT with ⟨a, ha⟩
          have hrecover : y = nonsplitTorus a⁻¹ := by
            calc
              y = frobPSL⁻¹ *
                  (frobPSL * y * frobPSL⁻¹) * frobPSL := by
                    simp [mul_assoc]
              _ = frobPSL⁻¹ * nonsplitTorus a * frobPSL := by
                    rw [← ha]
              _ = nonsplitTorus a⁻¹ := by
                have hfrob_inv : frobPSL⁻¹ = frobPSL :=
                  (eq_inv_of_mul_eq_one_left
                    (by simpa [pow_two] using hfrobPSL_sq)).symm
                simpa [hfrob_inv] using hfrobPSL_conj a
          have hy_inv : (frobPSL * y * frobPSL⁻¹)⁻¹ ∈ R :=
            R.inv_mem hy
          rw [hrecover]
          rw [← ha] at hy_inv
          simpa using hy_inv
  refine ⟨nonsplitTorus.range, hnonsplitTorus_cyclic,
    hnonsplit_range_card, ?_, ?_, hnonsplit_weakTI, ?_⟩
  · rw [hnonsplit_normalizer_eq_candidate, hnonsplitCandidate_card,
      hnonsplit_range_card]
  · refine ⟨frobPSL, hfrobPSL_mem_normalizer,
      hfrobPSL_not_mem_torus, ?_, ?_, ?_, ?_⟩
    · simpa [pow_two] using hfrobPSL_sq
    · intro t ht
      rcases ht with ⟨a, rfl⟩
      simpa using hfrobPSL_conj a
    · simpa [nonsplitDihedralCandidate] using
        hnonsplitCandidate_card_raw
    · intro R hR hRne
      simpa [nonsplitDihedralCandidate] using
        hnonsplit_normalizer_eq_candidate_of_le R hR hRne
  · intro A _hdisc_nonzero heigen
    let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
      QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F))
    let M : Matrix (Fin 2) (Fin 2) F := A
    let χ : Polynomial F := M.charpoly
    have hχdeg : χ.natDegree = 2 := by
      simp [χ, M]
    have hχne : χ ≠ 0 := by
      exact (Matrix.charpoly_monic M).ne_zero
    have hno_root (μ : F) : ¬ χ.IsRoot μ := by
      intro hroot
      have hdet_zero :
          (Matrix.scalar (Fin 2) μ - M).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact hroot
      obtain ⟨v, hv_ne, hv⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hv
      exact (sub_eq_zero.mp hv).symm
    have hχroots : χ.roots = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro μ hμ
      exact hno_root μ ((Polynomial.mem_roots hχne).mp hμ)
    have hχirreducible : Irreducible χ := by
      apply ((Matrix.charpoly_monic M).irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [hχdeg]) (by rw [hχdeg]; norm_num)).mpr
      exact hχroots
    have : Fact (Irreducible χ) := ⟨hχirreducible⟩
    let _ : Algebra F (AdjoinRoot χ) := AdjoinRoot.instAlgebra χ
    let _ : Module F (AdjoinRoot χ) := Algebra.toModule
    have hfinrankL : Module.finrank F (AdjoinRoot χ) = 2 := by
      calc
        Module.finrank F (AdjoinRoot χ) =
            (AdjoinRoot.powerBasis hχne).dim :=
          (AdjoinRoot.powerBasis hχne).finrank
        _ = χ.natDegree := AdjoinRoot.powerBasis_dim hχne
        _ = 2 := hχdeg
    let eL : AdjoinRoot χ ≃ₐ[F] E :=
      FiniteField.algEquivExtension F p 2 (AdjoinRoot χ) hfinrankL
    let α : E := eL (AdjoinRoot.root χ)
    have hα_root : (χ.map (algebraMap F E)).IsRoot α := by
      have hrootL := AdjoinRoot.isRoot_root χ
      have hrootE :
          ((χ.map (AdjoinRoot.of χ)).map eL.toRingEquiv.toRingHom).IsRoot
            (eL (AdjoinRoot.root χ)) := hrootL.map
      rw [Polynomial.map_map] at hrootE
      convert hrootE using 1
      congr 1
      ext r
      simp [eL]
    have hα_not_scalar (r : F) : algebraMap F E r ≠ α := by
      intro hr
      apply hno_root r
      apply (Polynomial.isRoot_map_iff
        ((algebraMap F E).injective)).mp
      rw [hr]
      exact hα_root
    have hdetA : M.det = 1 := by
      exact A.property
    have hα_poly : α ^ 2 - algebraMap F E (Matrix.trace M) * α + 1 = 0 := by
      have h := hα_root
      simpa [Polynomial.IsRoot, χ, Matrix.charpoly_fin_two, hdetA] using h
    have hα_sq : α * α = algebraMap F E (Matrix.trace M) * α - 1 := by
      rw [pow_two] at hα_poly
      linear_combination hα_poly
    let αfamily : Fin 2 → E := ![α, 1]
    have hαLI : LinearIndependent F αfamily := by
      rw [linearIndependent_fin2]
      refine ⟨one_ne_zero, ?_⟩
      intro r hr
      exact hα_not_scalar r (by
        simpa [αfamily, Algebra.smul_def] using hr)
    have hfinrankE : Module.finrank F E = 2 := by
      simpa [E] using FiniteField.finrank_extension F p 2
    let bα : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hαLI (by
        simp [hfinrankE])
    let v : Fin 2 → F := ![1, 0]
    let w : Fin 2 → F := M.mulVec v
    have hv_ne : v ≠ 0 := by
      intro hv
      have := congrFun hv 0
      simp [v] at this
    let Afamily : Fin 2 → (Fin 2 → F) := ![w, v]
    have hALI : LinearIndependent F Afamily := by
      rw [linearIndependent_fin2]
      refine ⟨hv_ne, ?_⟩
      intro μ hμ
      apply heigen
      refine ⟨μ, v, hv_ne, ?_⟩
      simpa [Afamily, w] using hμ.symm
    let bA : Module.Basis (Fin 2) F (Fin 2 → F) :=
      basisOfLinearIndependentOfCardEqFinrank hALI (by simp)
    have hbα_zero : bα 0 = α := by
      simp [bα, αfamily]
    have hbα_one : bα 1 = 1 := by
      simp [bα, αfamily]
    have hbA_zero : bA 0 = w := by
      simp [bA, Afamily]
    have hbA_one : bA 1 = v := by
      simp [bA, Afamily]
    let H : E ≃ₗ[F] (Fin 2 → F) := bα.equiv bA (Equiv.refl (Fin 2))
    have hH_basis (i : Fin 2) : H (bα i) = bA i := by
      simp [H]
    have hH_alpha : H α = w := by
      rw [← hbα_zero, hH_basis, hbA_zero]
    have hH_one : H 1 = v := by
      rw [← hbα_one, hH_basis, hbA_one]
    have hdet_coord :
        M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hdetA
    have hAw : M.mulVec w = Matrix.trace M • w - v := by
      ext i
      fin_cases i
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        linear_combination -hdet_coord
      · simp [w, v, Matrix.mulVec, dotProduct, Matrix.trace_fin_two]
        ring
    have hlin :
        H.toLinearMap.comp (Algebra.lmul F E α) =
          M.mulVecLin.comp H.toLinearMap := by
      apply Module.Basis.ext bα
      intro i
      fin_cases i
      · change H (α * bα 0) = M.mulVec (H (bα 0))
        rw [hbα_zero, hH_alpha]
        calc
          H (α * α) = H (algebraMap F E (Matrix.trace M) * α - 1) :=
            congrArg H hα_sq
          _ = Matrix.trace M • H α - H 1 := by
            change H (Matrix.trace M • α - 1) = _
            rw [map_sub, map_smul]
          _ = Matrix.trace M • w - v := by rw [hH_alpha, hH_one]
          _ = M.mulVec w := hAw.symm
      · change H (α * bα 1) = M.mulVec (H (bα 1))
        rw [hbα_one, mul_one, hH_alpha, hH_one]
    let std : Module.Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
    let D : Matrix (Fin 2) (Fin 2) F :=
      LinearMap.toMatrix b std H.toLinearMap
    let B : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b α
    have hMmatrix : LinearMap.toMatrix std std M.mulVecLin = M := by
      change LinearMap.toMatrix' (Matrix.toLin' M) = M
      exact LinearMap.toMatrix'_toLin' M
    have hMD : M * D = D * B := by
      calc
        M * D =
            LinearMap.toMatrix std std M.mulVecLin *
              LinearMap.toMatrix b std H.toLinearMap := by rw [hMmatrix]
        _ = LinearMap.toMatrix b std
            (M.mulVecLin.comp H.toLinearMap) :=
          (LinearMap.toMatrix_comp b std std M.mulVecLin H.toLinearMap).symm
        _ = LinearMap.toMatrix b std
            (H.toLinearMap.comp (Algebra.lmul F E α)) := by rw [hlin]
        _ = LinearMap.toMatrix b std H.toLinearMap *
            LinearMap.toMatrix b b (Algebra.lmul F E α) :=
          LinearMap.toMatrix_comp b b std H.toLinearMap (Algebra.lmul F E α)
        _ = D * B := by rfl
    have hDunit : IsUnit D.det := by
      change IsUnit (LinearMap.toMatrix b std H.toLinearMap).det
      exact H.isUnit_det b std
    have hDne : D.det ≠ 0 := hDunit.ne_zero
    have hdet_eq := congrArg Matrix.det hMD
    rw [Matrix.det_mul, Matrix.det_mul] at hdet_eq
    have hBdet : B.det = 1 := by
      apply mul_left_cancel₀ hDne
      calc
        D.det * B.det = M.det * D.det := hdet_eq.symm
        _ = 1 * D.det := by rw [hdetA]
        _ = D.det * 1 := by simp
    have hnormα : Algebra.norm F α = 1 := by
      calc
        Algebra.norm F α = B.det := by
          simpa [B] using Algebra.norm_eq_matrix_det b α
        _ = 1 := hBdet
    have hαne : α ≠ 0 := by
      intro hα
      have := hnormα
      rw [hα, Algebra.norm_zero] at this
      exact zero_ne_one this
    let αunit : Eˣ := Units.mk0 α hαne
    let xK : K := ⟨αunit, by
      change normUnits αunit = 1
      apply Units.ext
      simpa [normUnits, αunit] using hnormα⟩
    obtain ⟨d, hd⟩ := hDunit
    obtain ⟨c, hc⟩ := hnormUnits_surjective d⁻¹
    have hcval : Algebra.norm F (c : E) = (d⁻¹ : Fˣ) := by
      have hc' := congrArg Units.val hc
      simpa [normUnits] using hc'
    let Lc : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix b (c : E)
    let Gmat : Matrix (Fin 2) (Fin 2) F := D * Lc
    have hGdet : Gmat.det = 1 := by
      change (D * Lc).det = 1
      rw [Matrix.det_mul]
      change D.det * (Algebra.leftMulMatrix b (c : E)).det = 1
      rw [← Algebra.norm_eq_matrix_det b, hcval, ← hd]
      exact Units.mul_inv d
    let G : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Gmat, hGdet⟩
    have hBLc : B * Lc = Lc * B := by
      calc
        B * Lc = Algebra.leftMulMatrix b (α * (c : E)) := by
          simp [B, Lc]
        _ = Algebra.leftMulMatrix b ((c : E) * α) := by rw [mul_comm]
        _ = Lc * B := by simp [B, Lc]
    have hMG : M * Gmat = Gmat * B := by
      calc
        M * Gmat = (M * D) * Lc := by simp [Gmat, Matrix.mul_assoc]
        _ = (D * B) * Lc := by rw [hMD]
        _ = D * (B * Lc) := by rw [Matrix.mul_assoc]
        _ = D * (Lc * B) := by rw [hBLc]
        _ = (D * Lc) * B := by rw [Matrix.mul_assoc]
        _ = Gmat * B := rfl
    have hxB :
        (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F) =
          ⟨B, hBdet⟩ := by
      apply Subtype.ext
      rfl
    have hMGsl : A * G = G * nonsplitSL xK := by
      apply Subtype.ext
      change M * Gmat = Gmat * (nonsplitSL xK : Matrix.SpecialLinearGroup (Fin 2) F).1
      rw [hxB]
      exact hMG
    have hA_factor : A = G * nonsplitSL xK * G⁻¹ := by
      calc
        A = (A * G) * G⁻¹ := by simp
        _ = (G * nonsplitSL xK) * G⁻¹ := by rw [hMGsl]
    refine ⟨qSL G, ?_⟩
    refine ⟨nonsplitTorus xK, ⟨xK, rfl⟩, ?_⟩
    change qSL G * nonsplitTorus xK * (qSL G)⁻¹ = qSL A
    rw [hA_factor]
    simp [nonsplitTorus, qSL]
set_option maxHeartbeats 1000000 in

/-- Huppert II.8.4(a,b), retaining the Frobenius reflection and its inversion
action on the standard nonsplit torus. -/
public theorem huppert_II_8_4_nonsplit_torus_reflection_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      ∃ w : PSL2MatrixGroup F,
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      w ∉ S ∧
      w * w = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers w :
        Subgroup (PSL2MatrixGroup F)) = 2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers w := by
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer,
      ⟨w, hwN, hwS, hwsq, hwinv, hcandidate_card, hnormalizer⟩,
      _hweakTI, _hcover⟩ := h84_nonsplit_torus_data hFcard
  exact ⟨S, w, hS_cyclic, hS_card, hwN, hwS, hwsq, hwinv,
    hcandidate_card, hnormalizer⟩

/-- Huppert II.8.4(a,b), for the canonical nonsplit torus and its normalizer. -/
public theorem huppert_II_8_4_nonsplit_torus_normalizer_card
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ S : Subgroup (PSL2MatrixGroup F),
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) =
        2 * Nat.card S := by
  obtain ⟨S, hS_cyclic, hS_card, hS_normalizer, _, _, _⟩ :=
    h84_nonsplit_torus_data hFcard
  exact ⟨S, hS_cyclic, hS_card, hS_normalizer⟩

private theorem hmem_eq_one_of_coprime_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horder_A : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horder_B : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horder_A horder_B)

private theorem hq_coprime_split_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q - 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q - 1) 2)

private theorem hq_coprime_nonsplit_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q + 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  apply Nat.div_dvd_of_dvd
  convert Nat.dvd_add (Nat.gcd_dvd_left (q - 1) 2)
    (Nat.gcd_dvd_right (q - 1) 2) using 1
  all_goals omega

public theorem hsplit_nonsplit_order_coprime (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime
      ((q - 1) / Nat.gcd (q - 1) 2)
      ((q + 1) / Nat.gcd (q - 1) 2) := by
  by_cases hq_even : Even q
  · have hq_sub_one_odd : Odd (q - 1) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have hparity := (Nat.even_sub (by omega : 1 ≤ q)).mp heven
      exact Nat.not_even_one (hparity.mp hq_even)
    have hgcd : Nat.gcd (q - 1) 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
    rw [hgcd]
    simp only [Nat.div_one]
    have hcop : Nat.Coprime (q - 1) ((q - 1) + 2) :=
      (Nat.coprime_self_add_right).mpr hq_sub_one_odd.coprime_two_right
    convert hcop using 1
    all_goals omega
  · have hq_odd : Odd q := Nat.not_even_iff_odd.mp hq_even
    have htwo_dvd : 2 ∣ q - 1 := by
      rcases hq_odd with ⟨k, hk⟩
      use k
      omega
    have hgcd : Nat.gcd (q - 1) 2 = 2 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
    rcases hq_odd with ⟨k, hk⟩
    rw [hgcd]
    have hsub : q - 1 = 2 * k := by omega
    have hadd : q + 1 = 2 * (k + 1) := by omega
    rw [hsub, hadd]
    rw [Nat.mul_div_cancel_left k (by omega),
      Nat.mul_div_cancel_left (k + 1) (by omega)]
    exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right k)
private theorem hconjugate_family_unique_of_weak_ti
    {G : Type u} [Group G] (U : Subgroup G)
    (hweakTI : ∀ y : G, y ∈ U → y ≠ 1 → ∀ g : G,
      g * y * g⁻¹ ∈ U → g ∈ Subgroup.normalizer (U : Set G)) :
    ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom := by
  intro x hx g₁ g₂ hx₁ hx₂
  rcases hx₁ with ⟨a, haU, ha⟩
  rcases hx₂ with ⟨b, hbU, hb⟩
  have ha' : g₁ * a * g₁⁻¹ = x := by
    simpa [MulAut.conj_apply] using ha
  have hb' : g₂ * b * g₂⁻¹ = x := by
    simpa [MulAut.conj_apply] using hb
  have ha_ne : a ≠ 1 := by
    intro ha_one
    apply hx
    rw [← ha']
    simp [ha_one]
  have hb_ne : b ≠ 1 := by
    intro hb_one
    apply hx
    rw [← hb']
    simp [hb_one]
  let g : G := g₁⁻¹ * g₂
  have hconj : g * b * g⁻¹ = a := by
    change (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ = a
    calc
      (g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹ =
          g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * x * g₁ := by rw [hb']
      _ = a := by rw [← ha']; group
  have hgN : g ∈ Subgroup.normalizer (U : Set G) :=
    hweakTI b hbU hb_ne g (by simpa [hconj] using haU)
  have hmapg :
      U.map (MulAut.conj g).toMonoidHom = U := by
    rw [← Subgroup.conjAct_pointwise_smul_iff] at hgN
    change U.map (MulAut.conj g).toMonoidHom = U at hgN
    exact hgN
  have hgprod : g₁ * g = g₂ := by
    simp [g]
  calc
    U.map (MulAut.conj g₁).toMonoidHom =
        (U.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g₁).toMonoidHom := by rw [hmapg]
    _ = U.map (MulAut.conj (g₁ * g)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    _ = U.map (MulAut.conj g₂).toMonoidHom := by rw [hgprod]
private theorem hthree_family_unique_of_same_family
    {G : Type u} [Group G] [Finite G]
    (P U S : Subgroup G)
    (hPU : Nat.Coprime (Nat.card P) (Nat.card U))
    (hPS : Nat.Coprime (Nat.card P) (Nat.card S))
    (hUS : Nat.Coprime (Nat.card U) (Nat.card S))
    (hsameP : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ P.map (MulAut.conj g₁).toMonoidHom →
      x ∈ P.map (MulAut.conj g₂).toMonoidHom →
      P.map (MulAut.conj g₁).toMonoidHom =
        P.map (MulAut.conj g₂).toMonoidHom)
    (hsameU : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ U.map (MulAut.conj g₁).toMonoidHom →
      x ∈ U.map (MulAut.conj g₂).toMonoidHom →
      U.map (MulAut.conj g₁).toMonoidHom =
        U.map (MulAut.conj g₂).toMonoidHom)
    (hsameS : ∀ x : G, x ≠ 1 → ∀ g₁ g₂,
      x ∈ S.map (MulAut.conj g₁).toMonoidHom →
      x ∈ S.map (MulAut.conj g₂).toMonoidHom →
      S.map (MulAut.conj g₁).toMonoidHom =
        S.map (MulAut.conj g₂).toMonoidHom) :
    ∀ x : G, x ≠ 1 →
      ∀ T₁ T₂ : Subgroup G, x ∈ T₁ → x ∈ T₂ →
      ((∃ g, T₁ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
      ((∃ g, T₂ = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
      T₁ = T₂ := by
  intro x hx T₁ T₂ hx₁ hx₂ hT₁ hT₂
  rcases hT₁ with ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ | ⟨g₁, rfl⟩ <;>
    rcases hT₂ with ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩ | ⟨g₂, rfl⟩
  · exact hsameP x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPU.symm) hx₁ hx₂)).elim
  · exact hsameU x hx g₁ g₂ hx₁ hx₂
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hPS.symm) hx₁ hx₂)).elim
  · exact (hx (hmem_eq_one_of_coprime_card _ _ (by
      rw [Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj g₁).toMonoidHom) (MulAut.conj g₁).injective,
        Subgroup.card_map_of_injective (K := U)
          (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective]
      exact hUS.symm) hx₁ hx₂)).elim
  · exact hsameS x hx g₁ g₂ hx₁ hx₂

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Huppert II.8.5(a), with the covering and TI uniqueness clauses tied to
the same standard split and nonsplit tori. -/
public theorem huppert_II_8_5_a_psl2_cover
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_add_eq_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, add_comm] }
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    intro a b hab
    have hdiff : unipotent (a - b) = 1 := by
      rw [sub_eq_add_neg, unipotent.map_add_eq_mul,
        unipotent.map_neg_eq_inv, hab, mul_inv_cancel]
    have hcenter :
        unipotentSL (a - b) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff (unipotentSL (a - b))).mp hdiff
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
    have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
    apply sub_eq_zero.mp
    simpa [unipotentSL] using hab0.symm
  let U₀ : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hU₀card : Nat.card U₀ = Nat.card F := by
    let e : Multiplicative F ≃ U₀ :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU₀_isPGroup : IsPGroup p U₀ := by
    apply IsPGroup.of_card
    rw [hU₀card, hFcard]
  obtain ⟨Q, hU₀_le_Q⟩ := hU₀_isPGroup.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU₀_eq_Q : U₀ = (Q : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU₀_le_Q (by rw [hQcard, hU₀card])
  obtain ⟨kP, hkP⟩ := MulAction.exists_smul_eq
    (α := Sylow p (PSL2MatrixGroup F)) (PSL2MatrixGroup F) P Q
  have hP_to_U₀ :
      (P : Subgroup (PSL2MatrixGroup F)).map
        (MulAut.conj kP).toMonoidHom = U₀ := by
    have hkP' := congrArg
      (fun R : Sylow p (PSL2MatrixGroup F) =>
        (R : Subgroup (PSL2MatrixGroup F))) hkP
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      ← hU₀_eq_Q] at hkP'
    exact hkP'
  have hupper_unipotent_conj
      (A : Matrix.SpecialLinearGroup (Fin 2) F)
      (hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
      (t : F) :
      A * unipotentSL t * A⁻¹ =
        unipotentSL
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
    have hdet :
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have h := A.property
      rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
      exact h
    have hdet' :
        (A : Matrix (Fin 2) (Fin 2) F) 1 1 *
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      rw [mul_comm, hdet]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [unipotentSL, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, hA10, hdet, hdet',
      pow_two]
    all_goals ring
  have hU₀_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ U₀ → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ U₀ →
            g ∈ Subgroup.normalizer (U₀ : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_zero : a.toAdd ≠ 0 := by
      intro ha_zero
      apply hy_ne
      change unipotent a.toAdd = 1
      rw [ha_zero]
      exact unipotent.map_zero_eq_one
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (unipotentSL b.toAdd) =
          qSL (A * unipotentSL a.toAdd * A⁻¹) := by
      simpa [qSL, unipotent] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        unipotentSL b.toAdd * z * A =
          A * unipotentSL a.toAdd := by
      calc
        unipotentSL b.toAdd * z * A =
            (A * unipotentSL a.toAdd * A⁻¹) * A := by rw [hzeq]
        _ = A * unipotentSL a.toAdd := by group
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := by
      simpa [r] using
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (unipotentSL b.toAdd : Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        (unipotentSL a.toAdd : Matrix (Fin 2) (Fin 2) F) at hmat
    rw [← hscalar] at hmat
    have h10 := congrFun (congrFun hmat (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hmat (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hr_one : r = 1 := by
      by_cases hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      · have hA11_ne :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
          intro hA11
          have hdet := A.property
          rw [Matrix.det_fin_two, hA10, hA11, mul_zero, mul_zero,
            sub_zero] at hdet
          exact zero_ne_one hdet
        apply mul_right_cancel₀ hA11_ne
        simpa [hA10, mul_assoc] using h11
      · apply mul_right_cancel₀ hA10
        simpa [mul_assoc] using h10
    have hA10 :
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have hprod :
          (A : Matrix (Fin 2) (Fin 2) F) 1 0 * a.toAdd = 0 := by
        simpa [hr_one, mul_comm, mul_left_comm, mul_assoc] using h11
      exact (mul_eq_zero.mp hprod).resolve_right ha_ne_zero
    have hmap_le :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom ≤ U₀ := by
      intro v hv
      rcases hv with ⟨w, hw, rfl⟩
      rcases hw with ⟨t, rfl⟩
      refine ⟨Multiplicative.ofAdd
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd), ?_⟩
      change unipotent
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t.toAdd) =
        (MulAut.conj (qSL A)).toMonoidHom (unipotent t.toAdd)
      have hc := congrArg qSL
        (hupper_unipotent_conj A hA10 t.toAdd)
      simpa [qSL, unipotent, MulAut.conj_apply] using hc.symm
    have hmap_eq :
        U₀.map (MulAut.conj (qSL A)).toMonoidHom = U₀ := by
      apply Subgroup.eq_of_le_of_card_ge hmap_le
      rw [Subgroup.card_map_of_injective
        (K := U₀) (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    exact hmap_eq
  have hU₀_same_family :=
    hconjugate_family_unique_of_weak_ti U₀ hU₀_weakTI
  have hprojective_TI_P :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom := by
    have hmap (g : PSL2MatrixGroup F) :
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom =
          U₀.map (MulAut.conj (g * kP⁻¹)).toMonoidHom := by
      rw [← hP_to_U₀, Subgroup.map_map]
      congr 1
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    intro x hx g₁ g₂ hx₁ hx₂
    rw [hmap g₁] at hx₁ ⊢
    rw [hmap g₂] at hx₂ ⊢
    exact hU₀_same_family x hx (g₁ * kP⁻¹) (g₂ * kP⁻¹) hx₁ hx₂
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun a => ⟨!![(a : F), 0; 0, (a⁻¹ : F)], by
          simp [Matrix.det_fin_two]⟩
      map_one' := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, mul_comm] }
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  have hsplit_props :
      IsCyclic splitTorus.range ∧
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
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
    have hsplit_mem_ker_iff (a : Fˣ) :
        a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
      rw [MonoidHom.mem_ker, mem_rootsOfUnity]
      constructor
      · intro ha
        have hcenter :
            splitTorusSL a ∈
              Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
          (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
        have hscalar :=
          Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
        have ha_inv_val := congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
        have ha_inv : a = a⁻¹ := by
          apply Units.ext
          simpa [splitTorusSL] using ha_inv_val
        simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
      · intro ha
        apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
        rw [Matrix.SpecialLinearGroup.mem_center_iff]
        refine ⟨(a : F), ?_, ?_⟩
        · simpa using congrArg Units.val ha
        · have ha_inv : a = a⁻¹ :=
            eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
          have ha_inv_val : (a : F) = (a⁻¹ : F) := by
            simpa using congrArg Units.val ha_inv
          change Matrix.scalar (Fin 2) (a : F) =
            !![(a : F), 0; 0, (a⁻¹ : F)]
          ext i j
          fin_cases i <;> fin_cases j
          · rfl
          · rfl
          · rfl
          · exact ha_inv_val
    have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
      ext a
      exact hsplit_mem_ker_iff a
    have hsplit_ker_card :
        Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
      rw [hsplit_ker_eq, hcard_roots]
    have hsplit_range_mul :
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          Nat.card F - 1 := by
      calc
        Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
            splitTorus.ker.index * Nat.card splitTorus.ker := by
          rw [Subgroup.index_ker, hsplit_ker_card]
        _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
        _ = Nat.card F - 1 := by
          simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
    have hsplit_range_card :
        Nat.card splitTorus.range =
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
      apply Nat.eq_div_of_mul_eq_left
      · rw [← hcard_roots]
        exact Nat.ne_of_gt Nat.card_pos
      · exact hsplit_range_mul
    have hsplit_range_cyclic : IsCyclic splitTorus.range := by
      have hUnitsCyclic : IsCyclic Fˣ := by
        let _ : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
        exact isCyclic_of_surjective
          ((⊤ : Subgroup Fˣ).subtype) (by
            intro a
            exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
      let _ : IsCyclic Fˣ := hUnitsCyclic
      exact isCyclic_of_surjective splitTorus.rangeRestrict
        splitTorus.rangeRestrict_surjective
    exact ⟨hsplit_range_cyclic, hsplit_range_card⟩
  have h85_split_semisimple
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hdisc_nonzero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 ≠ (4 : F))
    (heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) :
    ∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 ≠ (4 : F) at hdisc_nonzero
    rcases heigen with ⟨μ, v, hv_ne, hAv⟩
    have hμ_ne : μ ≠ 0 := by
      intro hμ
      subst μ
      have hzero :
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = 0 := by
        simpa using hAv
      have hrecover :
          ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).mulVec
              ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
        calc
          _ = (((A⁻¹ * A : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec v) :=
            Matrix.mulVec_mulVec v _ _
          _ = v := by rw [inv_mul_cancel]; simp
      apply hv_ne
      calc
        v = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := hrecover.symm
        _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F).mulVec 0 := by rw [hzero]
        _ = 0 := by simp
    let a : Fˣ := Units.mk0 μ hμ_ne
    have hdetA :
        Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 := A.property
    have hkernel :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).mulVec v = 0 := by
      rw [Matrix.sub_mulVec]
      have hscalar :
          (Matrix.scalar (Fin 2) μ).mulVec v = μ • v := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [hscalar, hAv, sub_self]
    have hdet_zero :
        (Matrix.scalar (Fin 2) μ -
          (A : Matrix (Fin 2) (Fin 2) F)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hkernel⟩
    have hdet_formula (x : F) :
        (Matrix.scalar (Fin 2) x -
          (A : Matrix (Fin 2) (Fin 2) F)).det =
            x ^ 2 - trA * x + 1 := by
      calc
        _ = x ^ 2 - trA * x +
            Matrix.det (A : Matrix (Fin 2) (Fin 2) F) := by
              simp [Matrix.det_fin_two, Matrix.trace_fin_two, trA]
              have hdetCoord := hdetA
              rw [Matrix.det_fin_two] at hdetCoord
              linear_combination hdetCoord
        _ = _ := by rw [hdetA]
    have hpoly : μ ^ 2 - trA * μ + 1 = 0 := by
      rw [← hdet_formula]
      exact hdet_zero
    have htrace_mu : trA = μ + μ⁻¹ := by
      apply mul_right_cancel₀ hμ_ne
      calc
        trA * μ = μ ^ 2 + 1 := by
          linear_combination -hpoly
        _ = (μ + μ⁻¹) * μ := by
          field_simp [hμ_ne]
    have hμ_ne_inv : μ ≠ μ⁻¹ := by
      intro hμ
      apply hdisc_nonzero
      have hμ_sq : μ ^ 2 = 1 := by
        calc
          μ ^ 2 = μ * μ := by rw [pow_two]
          _ = μ * μ⁻¹ := congrArg (fun z : F => μ * z) hμ
          _ = 1 := mul_inv_cancel₀ hμ_ne
      rw [htrace_mu, ← hμ]
      calc
        (μ + μ) ^ 2 = 4 * μ ^ 2 := by ring
        _ = 4 := by rw [hμ_sq, mul_one]
    have hother_eigen :
        ∃ w : Fin 2 → F, w ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec w = μ⁻¹ • w := by
      have hpoly_inv : (μ⁻¹) ^ 2 - trA * μ⁻¹ + 1 = 0 := by
        rw [htrace_mu]
        field_simp [hμ_ne]
        ring
      have hdet_inv :
          (Matrix.scalar (Fin 2) μ⁻¹ -
            (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
        rw [hdet_formula]
        exact hpoly_inv
      obtain ⟨w, hw_ne, hw⟩ :=
        Matrix.exists_mulVec_eq_zero_iff.mpr hdet_inv
      refine ⟨w, hw_ne, ?_⟩
      have hscalar :
          (Matrix.scalar (Fin 2) μ⁻¹).mulVec w = μ⁻¹ • w := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      rw [Matrix.sub_mulVec, hscalar] at hw
      exact (sub_eq_zero.mp hw).symm
    rcases hother_eigen with ⟨w, hw_ne, hAw⟩
    have hbasis_conjugates :
        ∃ G : Matrix.SpecialLinearGroup (Fin 2) F,
          A = G * splitTorusSL a * G⁻¹ := by
      let fA : Module.End F (Fin 2 → F) :=
        Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F)
      let eigenvalue : Fin 2 → F := ![μ, μ⁻¹]
      let eigenvector : Fin 2 → (Fin 2 → F) := ![v, w]
      have heigenvalue_injective : Function.Injective eigenvalue := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij)).elim
        · exact (hμ_ne_inv (by simpa [eigenvalue] using hij.symm)).elim
        · rfl
      have heigenvector :
          ∀ i, fA.HasEigenvector (eigenvalue i) (eigenvector i) := by
        intro i
        fin_cases i
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAv
          · simpa [eigenvector] using hv_ne
        · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
          · simpa [fA, eigenvalue, eigenvector,
              Matrix.mulVecLin_apply] using hAw
          · simpa [eigenvector] using hw_ne
      have hlinearIndependent :
          LinearIndependent F eigenvector :=
        Module.End.eigenvectors_linearIndependent' fA eigenvalue
          heigenvalue_injective eigenvector heigenvector
      let δ : F := v 0 * w 1 - w 0 * v 1
      have hδ_ne : δ ≠ 0 := by
        intro hδ
        have hcoeff := Fintype.linearIndependent_iff.mp hlinearIndependent
        by_cases hv1 : v 1 = 0
        · have hv0 : v 0 ≠ 0 := by
            intro hv0
            apply hv_ne
            funext i
            fin_cases i <;> assumption
          have hw1 : w 1 = 0 := by
            apply mul_left_cancel₀ hv0
            have : v 0 * w 1 = 0 := by
              simpa [δ, hv1] using hδ
            simpa using this
          let c : Fin 2 → F := ![w 0, -v 0]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j
            all_goals simp [Fin.sum_univ_two, c, eigenvector, hv1, hw1,
              mul_comm]
            all_goals ring
          have hc := hcoeff c hsum 1
          exact hv0 (by simpa [c] using neg_eq_zero.mp hc)
        · let c : Fin 2 → F := ![w 1, -v 1]
          have hsum : ∑ i, c i • eigenvector i = 0 := by
            funext j
            fin_cases j
            · simpa [Fin.sum_univ_two, c, eigenvector, δ,
                sub_eq_add_neg, mul_comm] using hδ
            · simp [Fin.sum_univ_two, c, eigenvector]
              ring
          have hc := hcoeff c hsum 1
          exact hv1 (by simpa [c] using neg_eq_zero.mp hc)
      let G : Matrix.SpecialLinearGroup (Fin 2) F :=
        ⟨!![v 0, δ⁻¹ * w 0; v 1, δ⁻¹ * w 1], by
          rw [Matrix.det_fin_two]
          change v 0 * (δ⁻¹ * w 1) -
            (δ⁻¹ * w 0) * v 1 = 1
          calc
            _ = δ⁻¹ * δ := by simp [δ]; ring
            _ = 1 := inv_mul_cancel₀ hδ_ne⟩
      have hAG : A * G = G * splitTorusSL a := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 0
        · have hw := congrFun hAw 0
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
        · simpa [G, splitTorusSL, Matrix.mul_apply, Matrix.mulVec,
            dotProduct, a, mul_comm] using congrFun hAv 1
        · have hw := congrFun hAw 1
          simp [Matrix.mulVec, dotProduct] at hw
          simp [G, splitTorusSL, Matrix.mul_apply, a]
          linear_combination δ⁻¹ * hw
      refine ⟨G, ?_⟩
      apply mul_right_cancel (b := G)
      calc
        A * G = G * splitTorusSL a := hAG
        _ = (G * splitTorusSL a * G⁻¹) * G := by group
    rcases hbasis_conjugates with ⟨G, hG⟩
    refine ⟨qSL G, ?_⟩
    refine ⟨splitTorus a, ⟨a, rfl⟩, ?_⟩
    change qSL G * splitTorus a * (qSL G)⁻¹ = qSL A
    rw [hG]
    simp [splitTorus, qSL]
  have h85_repeated_root
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA_one : qSL A ≠ 1)
    (hdisc_zero :
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)) :
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : PSL2MatrixGroup F,
      qSL A ∈ splitTorus.range.map (MulAut.conj g).toMonoidHom) := by
    classical
    let trA : F := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
    change trA ^ 2 = (4 : F) at hdisc_zero
    by_cases hA_split : qSL A ∈ splitTorus.range
    · right
      refine ⟨1, ?_⟩
      exact ⟨qSL A, hA_split, by simp⟩
    · have hA_parabolic :
          ((A : Matrix (Fin 2) (Fin 2) F).IsParabolic) := by
        refine ⟨?_, ?_⟩
        · rintro ⟨r, hr⟩
          apply hA_one
          apply (QuotientGroup.eq_one_iff A).mpr
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          refine ⟨r, ?_, ?_⟩
          · have hdet := A.property
            rw [← hr, Matrix.det_fin_two] at hdet
            change r ^ 2 = 1
            simpa [pow_two] using hdet
          · exact hr
        · have hdisc : (A : Matrix (Fin 2) (Fin 2) F).discr = trA ^ 2 - (4 : F) := by
            simp [Matrix.discr_fin_two, trA, A.property]
          rw [hdisc, hdisc_zero, sub_self]
      have h85_repeated_root_fixed_line :
          ∃ v : Fin 2 → F, v ≠ 0 ∧
            ∃ μ : F, ((A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v) := by
        have htrace :
            Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = (2 : F) ∨
              Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = -(2 : F) := by
          apply (sq_eq_sq_iff_eq_or_eq_neg).mp
          calc
            _ = (4 : F) := hdisc_zero
            _ = (2 : F) ^ 2 := by norm_num
        have hdet_coord :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
          have hdetA := A.property
          change Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = 1 at hdetA
          rw [Matrix.det_fin_two] at hdetA
          exact hdetA
        rcases htrace with htrace | htrace
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 -
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, 1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (1 : F)).mulVec v = (1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
        · have htrace_coord :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -2 := by
            simpa [Matrix.trace_fin_two] using htrace
          have hdet_zero :
              (Matrix.scalar (Fin 2) (-1 : F) -
                (A : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
            calc
              _ = 1 +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 +
                    (A : Matrix (Fin 2) (Fin 2) F) 1 1) +
                  ((A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
                    (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                      (A : Matrix (Fin 2) (Fin 2) F) 1 0) := by
                        simp [Matrix.det_fin_two]
                        ring
              _ = 0 := by rw [htrace_coord, hdet_coord]; ring
          obtain ⟨v, hv_ne, hv⟩ :=
            Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
          refine ⟨v, hv_ne, -1, ?_⟩
          have hscalar :
              (Matrix.scalar (Fin 2) (-1 : F)).mulVec v = (-1 : F) • v := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec, dotProduct]
          rw [Matrix.sub_mulVec, hscalar] at hv
          exact (sub_eq_zero.mp hv).symm
      have h85_repeated_root_jordan_basis :
          ∃ (G : Matrix.SpecialLinearGroup (Fin 2) F) (t : F),
            qSL A = qSL (G * unipotentSL t * G⁻¹) := by
        rcases h85_repeated_root_fixed_line with ⟨v, hv_ne, μ, heigen⟩
        have hw :
            ∃ w : Fin 2 → F, v 0 * w 1 - w 0 * v 1 = 1 := by
          by_cases hv0 : v 0 = 0
          · have hv1 : v 1 ≠ 0 := by
              intro hv1
              apply hv_ne
              funext i
              fin_cases i <;> assumption
            refine ⟨![(-(v 1)⁻¹), 0], ?_⟩
            simp [hv0, hv1]
          · refine ⟨![0, (v 0)⁻¹], ?_⟩
            simp [hv0]
        rcases hw with ⟨w, hw⟩
        let G : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![v 0, w 0; v 1, w 1], by
            simpa [Matrix.det_fin_two] using hw⟩
        let e0 : Fin 2 → F := ![1, 0]
        have hG_e0 :
            (G : Matrix (Fin 2) (Fin 2) F).mulVec e0 = v := by
          ext i
          fin_cases i <;>
            simp [G, e0, Matrix.mulVec, dotProduct]
        let B : Matrix.SpecialLinearGroup (Fin 2) F :=
          G⁻¹ * A * G
        have hGinv_v :
            (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v =
              e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0) := by
                  rw [hG_e0]
            _ = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 *
                (G : Matrix (Fin 2) (Fin 2) F)).mulVec e0) :=
                  Matrix.mulVec_mulVec e0 _ _
            _ = e0 := by
              change (((G⁻¹ * G : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F).mulVec e0) = e0
              rw [inv_mul_cancel]
              simp
        have hB_e0 :
            (B : Matrix (Fin 2) (Fin 2) F).mulVec e0 =
              μ • e0 := by
          calc
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec
                  ((G : Matrix (Fin 2) (Fin 2) F).mulVec e0)) := by
                    simp only [B, Matrix.SpecialLinearGroup.coe_mul]
                    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) := by
                  rw [hG_e0]
            _ = (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
                (μ • v) := by rw [heigen]
            _ = μ •
                (G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec v :=
                  Matrix.mulVec_smul _ _ _
            _ = μ • e0 := by rw [hGinv_v]
        have hB10 :
            (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          have h := congrFun hB_e0 1
          simpa [e0, Matrix.mulVec, dotProduct] using h
        have hB_parabolic :
            (B : Matrix (Fin 2) (Fin 2) F).IsParabolic := by
          have h := (Matrix.isParabolic_conj'_iff
            (Matrix.SpecialLinearGroup.toGL G)
            (m := (A : Matrix (Fin 2) (Fin 2) F))).mpr
              hA_parabolic
          rw [← Matrix.coe_units_inv] at h
          have hcoe_inv :
              ((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) =
                (((Matrix.SpecialLinearGroup.toGL G)⁻¹ :
                    GL (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) := by
            exact congrArg
              (fun X : GL (Fin 2) F =>
                (X : Matrix (Fin 2) (Fin 2) F))
              (map_inv
                (Matrix.SpecialLinearGroup.toGL
                  (n := Fin 2) (R := F)) G)
          rw [← hcoe_inv] at h
          simpa [B] using h
        have hBdiag :
            (B : Matrix (Fin 2) (Fin 2) F) 0 0 =
              (B : Matrix (Fin 2) (Fin 2) F) 1 1 :=
          (Matrix.isParabolic_iff_of_upperTriangular hB10).mp
            hB_parabolic |>.1
        let a : F := (B : Matrix (Fin 2) (Fin 2) F) 0 0
        have ha_sq : a ^ 2 = 1 := by
          have hdetB := B.property
          change Matrix.det (B : Matrix (Fin 2) (Fin 2) F) = 1
            at hdetB
          rw [Matrix.det_fin_two, hB10, mul_zero, sub_zero,
            ← hBdiag] at hdetB
          simpa [a, pow_two] using hdetB
        have ha_ne : a ≠ 0 := by
          intro ha
          rw [ha, zero_pow (by norm_num)] at ha_sq
          exact zero_ne_one ha_sq
        let t : F :=
          a⁻¹ * (B : Matrix (Fin 2) (Fin 2) F) 0 1
        let z : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨Matrix.scalar (Fin 2) a, by
            simpa [Matrix.det_fin_two, pow_two] using ha_sq⟩
        have hz_center :
            z ∈ Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [Matrix.SpecialLinearGroup.mem_center_iff]
          exact ⟨a, ha_sq, rfl⟩
        have hB_factor : B = z * unipotentSL t := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [z, t, unipotentSL, Matrix.mul_apply, a]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, ha_ne]
          · simp [z, t, unipotentSL, Matrix.mul_apply, hB10]
          · simp [z, t, unipotentSL, Matrix.mul_apply, a, hBdiag]
        have hqz : qSL z = 1 :=
          (QuotientGroup.eq_one_iff z).mpr hz_center
        have hqB : qSL B = qSL (unipotentSL t) := by
          rw [hB_factor, map_mul, hqz, one_mul]
        refine ⟨G, t, ?_⟩
        calc
          qSL A = qSL (G * B * G⁻¹) := by
            simp [B, mul_assoc]
          _ = qSL G * qSL B * qSL G⁻¹ := by simp
          _ = qSL G * qSL (unipotentSL t) * qSL G⁻¹ := by
            rw [hqB]
          _ = qSL (G * unipotentSL t * G⁻¹) := by simp
      have h85_repeated_root_nonsplit_unipotent :
          ∃ g : PSL2MatrixGroup F,
            qSL A ∈ U₀.map (MulAut.conj g).toMonoidHom := by
        rcases h85_repeated_root_jordan_basis with ⟨G, t, hG⟩
        refine ⟨qSL G, ?_⟩
        refine ⟨unipotent t, ⟨Multiplicative.ofAdd t, rfl⟩, ?_⟩
        rw [hG]
        change qSL G * qSL (unipotentSL t) * (qSL G)⁻¹ =
          qSL (G * unipotentSL t * G⁻¹)
        simp [qSL]
      exact Or.inl h85_repeated_root_nonsplit_unipotent
  obtain ⟨S, hS_cyclic, hS_card, _hS_normalizer, _hS_reflection,
      hS_weakTI,
      hS_noEigen⟩ :=
    h84_nonsplit_torus_data hFcard
  refine ⟨splitTorus.range, S, hsplit_props.1, hsplit_props.2,
    hS_cyclic, hS_card, ?_⟩
  have hprojective_cover :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        (∃ g, x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ splitTorus.range.map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, x ∈ S.map (MulAut.conj g).toMonoidHom) := by
    intro x hx
    refine QuotientGroup.induction_on x ?_ hx
    intro A hxA
    have hA_ne : qSL A ≠ 1 := by
      simpa [qSL] using hxA
    by_cases hdisc_zero :
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = (4 : F)
    · rcases h85_repeated_root A hA_ne hdisc_zero with hU₀ | hsplit
      · rcases hU₀ with ⟨g, hg⟩
        left
        refine ⟨g * kP, ?_⟩
        have hmap :
            U₀.map (MulAut.conj g).toMonoidHom =
              (P : Subgroup (PSL2MatrixGroup F)).map
                (MulAut.conj (g * kP)).toMonoidHom := by
          rw [← hP_to_U₀, Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
        rw [← hmap]
        exact hg
      · exact Or.inr (Or.inl hsplit)
    · by_cases heigen : ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
          (A : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v
      · exact Or.inr (Or.inl (h85_split_semisimple A hdisc_zero heigen))
      · exact Or.inr (Or.inr (by
          simpa [qSL] using hS_noEigen A hdisc_zero heigen))
  have hPcard :
      Nat.card (P : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P
    exact (Nat.card_congr eP.toEquiv).symm
  have hP_split_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card splitTorus.range) := by
    rw [hPcard, hsplit_props.2]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hP_nonsplit_coprime :
      Nat.Coprime (Nat.card (P : Subgroup (PSL2MatrixGroup F)))
        (Nat.card S) := by
    rw [hPcard, hS_card]
    exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
  have hsplit_nonsplit_coprime :
      Nat.Coprime (Nat.card splitTorus.range) (Nat.card S) := by
    rw [hsplit_props.2, hS_card]
    exact hsplit_nonsplit_order_coprime (Nat.card F)
      (Finite.one_lt_card (α := F))
  have hsplit_weakTI :
      ∀ y : PSL2MatrixGroup F, y ∈ splitTorus.range → y ≠ 1 →
        ∀ g : PSL2MatrixGroup F,
          g * y * g⁻¹ ∈ splitTorus.range →
            g ∈ Subgroup.normalizer
              (splitTorus.range : Set (PSL2MatrixGroup F)) := by
    intro y hy hy_ne g hgy
    rcases hy with ⟨a, rfl⟩
    have ha_ne_inv : (a : F) ≠ (a⁻¹ : F) := by
      intro hai
      apply hy_ne
      change qSL (splitTorusSL a) = 1
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      have haiU : a = a⁻¹ := by
        apply Units.ext
        simpa using hai
      have ha_sq : (a : F) ^ 2 = 1 := by
        have hsqU := congrArg (fun u : Fˣ => (u : F))
          (eq_inv_iff_mul_eq_one.mp haiU)
        simpa [pow_two] using hsqU
      refine ⟨(a : F), ha_sq, ?_⟩
      change Matrix.scalar (Fin 2) (a : F) =
        !![(a : F), 0; 0, (a⁻¹ : F)]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · rfl
      · rfl
      · exact hai
    refine QuotientGroup.induction_on g ?_ hgy
    intro A hAconj
    rcases hAconj with ⟨b, hb⟩
    have hq :
        qSL (splitTorusSL b) =
          qSL (A * splitTorusSL a * A⁻¹) := by
      simpa [qSL, splitTorus] using hb
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hq with
      ⟨z, hz, hzeq⟩
    have hzeqA :
        splitTorusSL b * z * A = A * splitTorusSL a := by
      calc
        splitTorusSL b * z * A =
            (A * splitTorusSL a * A⁻¹) * A := by rw [hzeq]
        _ = A * splitTorusSL a := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz (0 : Fin 2)
    have hmat := congrArg Subtype.val hzeqA
    change (!![(b : F), 0; 0, (b⁻¹ : F)] :
          Matrix (Fin 2) (Fin 2) F) *
        (z : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        !![(a : F), 0; 0, (a⁻¹ : F)] at hmat
    rw [← hscalar] at hmat
    rcases hsplit_matrix_diag_or_antidiag A a b
        ((z : Matrix (Fin 2) (Fin 2) F) 0 0)
        ha_ne_inv hmat with hdiag | hanti
    · rcases hdiag with ⟨h01, h10⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c * A := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [splitTorusSL, Matrix.mul_apply, h01, h10, mul_comm]
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
    · rcases hanti with ⟨h00, h11⟩
      have hmap_le :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom ≤
            splitTorus.range := by
        intro v hv
        rcases hv with ⟨w, hw, rfl⟩
        rcases hw with ⟨c, rfl⟩
        refine ⟨c⁻¹, ?_⟩
        have hcomm :
            A * splitTorusSL c = splitTorusSL c⁻¹ * A := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [splitTorusSL, Matrix.mul_apply, h00, h11, mul_comm]
        have hconj :
            A * splitTorusSL c * A⁻¹ = splitTorusSL c⁻¹ := by
          rw [hcomm]
          simp [mul_assoc]
        simpa [qSL, splitTorus, MulAut.conj_apply] using
          (congrArg qSL hconj).symm
      have hmap_eq :
          splitTorus.range.map
              (MulAut.conj (qSL A)).toMonoidHom =
            splitTorus.range := by
        apply Subgroup.eq_of_le_of_card_ge hmap_le
        rw [Subgroup.card_map_of_injective
          (K := splitTorus.range)
          (f := (MulAut.conj (qSL A)).toMonoidHom)
          (MulAut.conj (qSL A)).injective]
      rw [← Subgroup.conjAct_pointwise_smul_iff]
      exact hmap_eq
  have hprojective_TI_split :=
    hconjugate_family_unique_of_weak_ti splitTorus.range hsplit_weakTI
  have hprojective_TI_nonsplit :=
    hconjugate_family_unique_of_weak_ti S hS_weakTI
  have hprojective_TI_same_family :
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom →
        x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom →
        (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₁).toMonoidHom =
          (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ splitTorus.range.map (MulAut.conj g₁).toMonoidHom →
        x ∈ splitTorus.range.map (MulAut.conj g₂).toMonoidHom →
        splitTorus.range.map (MulAut.conj g₁).toMonoidHom =
          splitTorus.range.map (MulAut.conj g₂).toMonoidHom) ∧
      (∀ x : PSL2MatrixGroup F, x ≠ 1 → ∀ g₁ g₂,
        x ∈ S.map (MulAut.conj g₁).toMonoidHom →
        x ∈ S.map (MulAut.conj g₂).toMonoidHom →
        S.map (MulAut.conj g₁).toMonoidHom =
          S.map (MulAut.conj g₂).toMonoidHom) := by
    exact ⟨hprojective_TI_P, hprojective_TI_split,
      hprojective_TI_nonsplit⟩
  have hprojective_TI :
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∀ T₁ T₂ : Subgroup (PSL2MatrixGroup F),
          x ∈ T₁ → x ∈ T₂ →
          ((∃ g, T₁ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₁ = S.map (MulAut.conj g).toMonoidHom)) →
          ((∃ g, T₂ = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = splitTorus.range.map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T₂ = S.map (MulAut.conj g).toMonoidHom)) →
          T₁ = T₂ := by
    rcases hprojective_TI_same_family with
      ⟨hsameP, hsameSplit, hsameS⟩
    exact hthree_family_unique_of_same_family
      (P : Subgroup (PSL2MatrixGroup F)) splitTorus.range S
      hP_split_coprime hP_nonsplit_coprime hsplit_nonsplit_coprime
      hsameP hsameSplit hsameS
  intro x hx
  rcases hprojective_cover x hx with hP | hU | hS
  · let T := (P : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj hP.choose).toMonoidHom
    refine ⟨T, ⟨hP.choose_spec, Or.inl ⟨hP.choose, rfl⟩⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hP.choose_spec
      hT'.2 (Or.inl ⟨hP.choose, rfl⟩)
  · let T := splitTorus.range.map
      (MulAut.conj hU.choose).toMonoidHom
    refine ⟨T, ⟨hU.choose_spec, Or.inr (Or.inl ⟨hU.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hU.choose_spec
      hT'.2 (Or.inr (Or.inl ⟨hU.choose, rfl⟩))
  · let T := S.map (MulAut.conj hS.choose).toMonoidHom
    refine ⟨T, ⟨hS.choose_spec, Or.inr (Or.inr ⟨hS.choose, rfl⟩)⟩, ?_⟩
    intro T' hT'
    exact hprojective_TI x hx T' T hT'.1 hS.choose_spec
      hT'.2 (Or.inr (Or.inr ⟨hS.choose, rfl⟩))

/-- Huppert II.8.5(a): the nonidentity elements of PSL(2,p^f) are
partitioned by the conjugates of a Sylow p-subgroup and the split and
nonsplit cyclic tori. -/
public theorem huppert_II_8_5_a_psl2_partition
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) :
    ∃ U S : Subgroup (PSL2MatrixGroup F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : PSL2MatrixGroup F, x ≠ 1 →
        ∃! T : Subgroup (PSL2MatrixGroup F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  exact huppert_II_8_5_a_psl2_cover hFcard P


end External
end CFSG.BenderSuzuki
