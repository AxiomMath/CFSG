module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 10
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

universe u

set_option maxHeartbeats 800000 in
/-- A quadratic map of binary vector spaces has a nonzero zero whenever the
source dimension is larger than twice the target dimension. This is the
Chevalley--Warning core used in Higman's Lemma 10. -/
public theorem lemma10_exists_nonzero_quadratic_zero
    (V W : Type*)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (q : V → W)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hq_zero : q 0 = 0)
    (hq_add : ∀ x y : V, q (x + y) = q x + q y + B x y)
    (hB_self : ∀ x : V, B x x = 0)
    (hdim : 2 * Module.finrank (ZMod 2) W <
      Module.finrank (ZMod 2) V) :
    ∃ x : V, x ≠ 0 ∧ q x = 0 := by
  classical
  let bV := Module.finBasis (ZMod 2) V
  let bW := Module.finBasis (ZMod 2) W
  have hadd_self (z : W) : z + z = 0 := by
    nth_rw 2 [← ZModModule.neg_eq_self z]
    exact add_neg_cancel z
  have hB_symm (x y : V) : B x y = B y x := by
    have hsum : B x y + B y x = 0 := by
      have h := hB_self (x + y)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hB_self, hB_self] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      B x y = B x y + (B y x + B y x) := by
        rw [hadd_self, add_zero]
      _ = (B x y + B y x) + B y x := by abel
      _ = B y x := by rw [hsum, zero_add]
  let A : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W :=
    bV.constr (S := ZMod 2) fun i =>
      bV.constr (S := ZMod 2) fun j =>
        if i < j then B (bV i) (bV j)
        else if i = j then q (bV i) else 0
  have hA_basis (i j : Fin (Module.finrank (ZMod 2) V)) :
      A (bV i) (bV j) =
        if i < j then B (bV i) (bV j)
        else if i = j then q (bV i) else 0 := by
    change
      (bV.constr (S := ZMod 2) fun i =>
        bV.constr (S := ZMod 2) fun j =>
          if i < j then B (bV i) (bV j)
          else if i = j then q (bV i) else 0) (bV i) (bV j) = _
    rw [bV.constr_basis, bV.constr_basis]
  have hA_polar : A + LinearMap.flip A = B := by
    apply bV.ext
    intro i
    apply bV.ext
    intro j
    simp only [LinearMap.add_apply, LinearMap.flip_apply]
    rw [hA_basis, hA_basis]
    by_cases hij : i = j
    · subst j
      simp [hB_self, hadd_self]
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hnji : ¬j < i := not_lt_of_ge hij.le
        have hji_ne : j ≠ i := ne_of_gt hij
        simp [hij, hnji, hji_ne]
      · have hnij : ¬i < j := not_lt_of_ge hji.le
        simp [hji, hnij, hij, hB_symm]
  let qA : V → W := fun x => A x x
  have hqA_add (x y : V) :
      qA (x + y) = qA x + qA y + B x y := by
    have hp := LinearMap.congr_fun (LinearMap.congr_fun hA_polar x) y
    change A x y + A y x = B x y at hp
    change A (x + y) (x + y) = A x x + A y y + B x y
    calc
      A (x + y) (x + y) =
          A x x + A y x + (A x y + A y y) := by
            simp only [map_add, LinearMap.add_apply]
      _ = A x x + A y y + B x y := by rw [← hp]; abel
  let d : V →ₗ[ZMod 2] W :=
    { toFun := fun x => q x - qA x
      map_add' := by
        intro x y
        rw [hq_add, hqA_add]
        abel
      map_smul' := by
        intro c x
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · left
            rfl
          · right
            rfl
        rcases hc with rfl | rfl
        · simp only [RingHom.id_apply, zero_smul]
          rw [hq_zero]
          simp [qA]
        · simp only [RingHom.id_apply, one_smul] }
  have hd_basis (i : Fin (Module.finrank (ZMod 2) V)) : d (bV i) = 0 := by
    simp [d, qA, hA_basis]
  have hd_zero : d = 0 := by
    apply bV.ext
    exact hd_basis
  have hq_eq (x : V) : q x = A x x := by
    have h := LinearMap.congr_fun hd_zero x
    change q x - qA x = 0 at h
    exact sub_eq_zero.mp h
  let alphaOf : (Fin (Module.finrank (ZMod 2) V) → ZMod 2) → V :=
    fun x => bV.equivFun.symm x
  let tau (i : Fin (Module.finrank (ZMod 2) W)) :
      W →ₗ[ZMod 2] ZMod 2 := bW.coord i
  let f :
      Fin (Module.finrank (ZMod 2) W) →
        MvPolynomial (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) :=
    fun i => ∑ j, ∑ k,
      MvPolynomial.C (tau i (A (bV k) (bV j))) *
        MvPolynomial.X j * MvPolynomial.X k
  have hpoly_degree (i : Fin (Module.finrank (ZMod 2) W)) :
      (f i).totalDegree ≤ 2 := by
    dsimp [f]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k _hk
    calc
      (MvPolynomial.C (tau i (A (bV k) (bV j))) *
              MvPolynomial.X j * MvPolynomial.X k).totalDegree
          ≤ (MvPolynomial.C (tau i (A (bV k) (bV j))) *
                MvPolynomial.X j).totalDegree +
              (MvPolynomial.X k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (tau i (A (bV k) (bV j)))).totalDegree +
              (MvPolynomial.X j).totalDegree) +
            (MvPolynomial.X k).totalDegree := by
        gcongr
        exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp
  have hpoly_eval
      (x : Fin (Module.finrank (ZMod 2) V) → ZMod 2)
      (i : Fin (Module.finrank (ZMod 2) W)) :
      MvPolynomial.eval x (f i) = tau i (q (alphaOf x)) := by
    have halpha_basis : alphaOf x = ∑ j, x j • bV j := by
      simp [alphaOf]
    rw [hq_eq, halpha_basis]
    simp [f, map_sum, smul_eq_mul, mul_comm, mul_left_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.mul_sum]
  have hnonzero_solution :
      ∃ x : Fin (Module.finrank (ZMod 2) V) → ZMod 2,
        x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
    have hsum_lt :
        (∑ i : Fin (Module.finrank (ZMod 2) W),
            (f i).totalDegree) <
          Fintype.card (Fin (Module.finrank (ZMod 2) V)) := by
      rw [Fintype.card_fin]
      calc
        (∑ i : Fin (Module.finrank (ZMod 2) W),
              (f i).totalDegree) ≤
            ∑ _i : Fin (Module.finrank (ZMod 2) W), 2 := by
          exact Finset.sum_le_sum fun i _hi => hpoly_degree i
        _ = 2 * Module.finrank (ZMod 2) W := by
          simp [Nat.mul_comm]
        _ < Module.finrank (ZMod 2) V := hdim
    let S :=
      {x : Fin (Module.finrank (ZMod 2) V) → ZMod 2 //
        ∀ i, MvPolynomial.eval x (f i) = 0}
    have hdiv : 2 ∣ Nat.card S := by
      change 2 ∣ Nat.card
        {x : Fin (Module.finrank (ZMod 2) V) → ZMod 2 //
          ∀ i, MvPolynomial.eval x (f i) = 0}
      simpa only [← Nat.card_eq_fintype_card] using
        (char_dvd_card_solutions_of_fintype_sum_lt 2 hsum_lt)
    let z : S := ⟨0, by
      intro i
      rw [hpoly_eval 0 i]
      simp [alphaOf, hq_zero]⟩
    have hcard_pos : 0 < Nat.card S :=
      Nat.card_pos_iff.mpr ⟨⟨z⟩, inferInstance⟩
    have hcard_gt_one : 1 < Nat.card S := by
      obtain ⟨N, hN⟩ := hdiv
      omega
    letI : Nontrivial S :=
      Finite.one_lt_card_iff_nontrivial.mp hcard_gt_one
    obtain ⟨w, hw⟩ := exists_ne z
    refine ⟨w.1, ?_, w.2⟩
    intro hwzero
    apply hw
    apply Subtype.ext
    simpa [z] using hwzero
  obtain ⟨x, hx, hzero⟩ := hnonzero_solution
  refine ⟨alphaOf x, ?_, ?_⟩
  · intro halpha
    apply hx
    apply bV.equivFun.symm.injective
    simpa [alphaOf] using halpha
  · apply bW.repr.injective
    ext i
    have hi : tau i (q (alphaOf x)) = 0 :=
      (hpoly_eval x i).symm.trans (hzero i)
    simpa [tau, Module.Basis.coord_apply] using hi


end Higman
end External
end CFSG.BenderSuzuki
