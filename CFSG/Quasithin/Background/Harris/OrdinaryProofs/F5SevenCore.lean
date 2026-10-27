module

public import Certificates.Data.CFSGNative.F5Seven.Core
public import Certificates.Certificate300101
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open Certificates.F5Seven

namespace F5Seven

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open Fin.CommRing

def toZ (a : Fin 7) : ZMod 7 := a

theorem toZ_mul (a b : Fin 7) : toZ (a * b) = toZ a * toZ b := by rfl

theorem toZ_sub (a b : Fin 7) : toZ (a - b) = toZ a - toZ b := by rfl

theorem toZ_ne_zero {a : Fin 7} : toZ a ≠ 0 ↔ a ≠ 0 := Iff.rfl

def mat (x : Tup7) : Matrix (Fin 2) (Fin 2) (ZMod 7) :=
  !![toZ x.1, toZ x.2.1; toZ x.2.2.1, toZ x.2.2.2]

theorem det_mat (x : Tup7) : (mat x).det = toZ (detT x) := by
  rw [mat, Matrix.det_fin_two_of, detT, toZ_sub, toZ_mul, toZ_mul]

def mkU (x : Tup7) (h : detT x ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 7) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x) (by rw [det_mat]; exact toZ_ne_zero.mpr h)

theorem zeta7_det : detT zeta7 ≠ 0 := by decide

theorem sigma7_det : detT sigma7 ≠ 0 := by decide

end F5Seven

open F5Seven

def uHat7 : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)) :=
  Subgroup.closure {mkU zeta7 zeta7_det, mkU sigma7 sigma7_det}

theorem uHat7_eq_uHat7S : uHat7 = Certificates.uHat7S := by
  rw [uHat7, Certificates.uHat7S]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  have hz : (mkU zeta7 zeta7_det : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 5; 2, 1] := by
    decide
  have hs : (mkU sigma7 sigma7_det : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 0; 0, 6] := by
    decide
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hz
    · exact Or.inr hs
  · rintro (h | h)
    · exact Or.inl (Units.ext (h.trans hz.symm))
    · exact Or.inr (Units.ext (h.trans hs.symm))

theorem f5SevenCore_maximal :
    ∀ H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)),
      uHat7 ≤ H → H = uHat7 ∨ H = ⊤ := by
  rw [uHat7_eq_uHat7S]
  exact Certificates.certificate300101

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
