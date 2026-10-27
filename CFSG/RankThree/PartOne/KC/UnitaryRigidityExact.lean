module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodAct
public import CFSG.RankThree.PartOne.KC.UnitaryGoodLift
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneLift

public section

namespace CFSG.RankThree.PartOne.KCUnitaryExact

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f n p : ℕ} {K : Type} [Field K]

structure PlaneSetup (h : UnitaryFieldData ℓ f K) (n p : ℕ)
    (Ahat : Subgroup (gramSU h (idGram K n))) : Prop where
  three_le : 3 ≤ n
  ne : ¬(n = 3 ∧ ℓ ^ f = 2)
  prime : p.Prime
  ne_char : p ≠ ℓ
  noTorsion : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1
  elem : IsElementaryAbelian p Ahat
  card : Nat.card Ahat = p ^ 2

noncomputable abbrev xlin (h : UnitaryFieldData ℓ f K) (n : ℕ) (x : gramSU h (idGram K n)) :
    Module.End K (Fin n → K) :=
  ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
    Module.End K (Fin n → K))

variable {h : UnitaryFieldData ℓ f K} {Ahat : Subgroup (gramSU h (idGram K n))}

theorem PlaneSetup.pow_eq_one (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) : x ^ p = 1 := by
  have := S.elem
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem PlaneSetup.planeData (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) : PlaneData h n p x :=
  ⟨S.three_le, S.ne, S.prime, S.ne_char, S.noTorsion, S.pow_eq_one hx⟩

theorem PlaneSetup.commute (S : PlaneSetup h n p Ahat) {x y : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) (hy : y ∈ Ahat) : x * y = y * x := by
  have := S.elem
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥Ahat)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isPerfect_idSpecialBlock (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) (i : GoodBlockIdx h x) :
    Group.IsPerfect (idSpecialBlock h x (i.1 : K[X])) := by
  have := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have GS := (S.planeData hx).goodSetting (MulAut.conj : primeFormP h (idGram K n) →*
    MulAut (primeFormP h (idGram K n))).range le_rfl
  exact (GS.F_quasi i).1

theorem matrix_comm_of_perfect (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {F : Subgroup (primeFormUnitary h (idGram K n))} (hF : Group.IsPerfect F)
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hβ : ∀ g ∈ F, primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    ∀ g ∈ F, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro g hg
  have h1 := matrix_eq_of_centralizes hn hne hF M τ hβ g hg
  have hMM : (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ
      = (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ *
          (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc, hMM, Matrix.mul_one]
    _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1]

theorem matrix_comm_of_plane (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hβ : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have L := S.planeData hx
  have hα := (mul_inv_eq_iff_eq_mul).mpr hβ
  have h1 := L.idAct'_eq_of_conj_eq _ hα
  rw [idAct'_primeFormPsi, idMatAction_mk] at h1
  have hMM : (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ
      = (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ *
          (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc, hMM, Matrix.mul_one]
    _ = ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1]

end CFSG.RankThree.PartOne.KCUnitaryExact
