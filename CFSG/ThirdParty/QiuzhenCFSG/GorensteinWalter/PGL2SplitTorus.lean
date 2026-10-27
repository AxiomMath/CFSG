module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import Mathlib.FieldTheory.Finite.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# The split reflected torus in `PGL₂`

The projective classes of `diag(k,1)` form a cyclic subgroup of order
`|K| - 1`.  The coordinate-swap matrix is an external involution that
inverts this subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The standard split torus of `PGL₂(K)`, together with its reflecting
involution. -/
public theorem pgl2_split_torus_reflection_data
    (K : Type u) [Field K] [Finite K] :
    ∃ U : Subgroup (PGL2 K), ∃ w : PGL2 K,
      IsCyclic U ∧ Nat.card U = Nat.card K - 1 ∧
      w ∉ U ∧ w * w = 1 ∧
      (∀ t : PGL2 K, t ∈ U → w * t * w⁻¹ = t⁻¹) ∧
      (Odd (Nat.card K) →
        ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let diagGL (k : Kˣ) : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(k : K), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two, k.ne_zero])
  let diagHom : Kˣ →* GL (Fin 2) K :=
    { toFun := diagGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [diagGL]
      map_mul' := by
        intro k l
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] }
  let torus : Kˣ →* PGL2 K :=
    Matrix.ProjGenLinGroup.mk.comp diagHom
  have htorus_injective : Function.Injective torus := by
    intro k l hkl
    change Matrix.ProjGenLinGroup.mk (diagHom k) =
      Matrix.ProjGenLinGroup.mk (diagHom l) at hkl
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hkl with ⟨a, ha⟩
    have h11 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1)) ha
    have h00 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) ha
    have ha1 : (a : K) = 1 := by
      simpa [diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using h11
    apply Units.ext
    simpa [diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, ha1] using h00
  let U : Subgroup (PGL2 K) := torus.range
  have hUcyclic : IsCyclic U := by
    let e : Kˣ ≃* U := MulEquiv.ofBijective torus.rangeRestrict
      ⟨by
        intro a b hab
        apply htorus_injective
        exact congrArg Subtype.val hab,
        MonoidHom.rangeRestrict_surjective torus⟩
    exact e.isCyclic.mp (inferInstance : IsCyclic Kˣ)
  have hUcard : Nat.card U = Nat.card K - 1 := by
    let e : Kˣ ≃* U := MulEquiv.ofBijective torus.rangeRestrict
      ⟨by
        intro a b hab
        apply htorus_injective
        exact congrArg Subtype.val hab,
        MonoidHom.rangeRestrict_surjective torus⟩
    calc
      Nat.card U = Nat.card Kˣ := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  let wGL : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
      simp [Matrix.det_fin_two])
  let w : PGL2 K := Matrix.ProjGenLinGroup.mk wGL
  have hw_not_mem : w ∉ U := by
    intro hw
    rcases hw with ⟨k, hk⟩
    have hk' := hk.symm
    change Matrix.ProjGenLinGroup.mk wGL =
      Matrix.ProjGenLinGroup.mk (diagHom k) at hk'
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hk' with ⟨a, ha⟩
    have h01 := congrArg (fun A : GL (Fin 2) K ↦
      ((A : Matrix (Fin 2) (Fin 2) K) 0 1)) ha
    simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hwGL_sq : wGL * wGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [wGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL *
      Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul, hwGL_sq, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hweyl_torus (k : Kˣ) :
      w * torus k * w⁻¹ = (torus k)⁻¹ := by
    rw [hw_inv]
    have hGL : wGL * diagHom k * wGL =
        Matrix.GeneralLinearGroup.scalar (Fin 2) k * diagHom k⁻¹ := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (diagHom k) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (diagHom k))⁻¹
    rw [← map_mul, ← map_mul, hGL, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    rw [map_inv diagHom k]
    exact map_inv Matrix.ProjGenLinGroup.mk (diagHom k)
  refine ⟨U, w, hUcyclic, hUcard, hw_not_mem, hw_sq, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨k, rfl⟩
    exact hweyl_torus k
  · intro hodd hUle
    have hchar : ringChar K ≠ 2 := by
      intro hchar
      have heven : Fintype.card K % 2 = 0 :=
        FiniteField.even_card_of_char_two hchar
      have hodd' : Odd (Fintype.card K) := by
        simpa [Nat.card_eq_fintype_card] using hodd
      exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact ha IsSquare.zero
    let k : Kˣ := Units.mk0 a ha0
    have hmemU : torus k ∈ U := ⟨k, rfl⟩
    have hmemPSL := hUle hmemU
    have hsq : IsSquare ((diagHom k).det : K) :=
      (pgl2_mk_mem_psl2_range_iff_det_isSquare (diagHom k)).mp hmemPSL
    apply ha
    simpa [diagHom, diagGL, Matrix.det_diagonal, Fin.prod_univ_two, k]
      using hsq

end CFSG.GorensteinWalter
