module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord

public section

namespace CFSG.StandardType.ZS

open Subgroup

@[expose] noncomputable def owR33_Qw (p d : ℕ) (w : Fin d → ZMod p) :
    QuadraticForm (ZMod p) (Fin d → ZMod p) :=
  QuadraticMap.weightedSumSquares (ZMod p) w

theorem owR33_Qw_apply (p d : ℕ) (w : Fin d → ZMod p) (v : Fin d → ZMod p) :
    owR33_Qw p d w v = ∑ i, w i * v i ^ 2 := by
  rw [owR33_Qw, QuadraticMap.weightedSumSquares_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, sq]

@[expose] def owR33_alphaVal (w : Fin 3 → ZMod 3) (a v : Fin 3 → ZMod 3) : ZMod 3 :=
  2 * ∑ k, w k * (v k * a k)

@[expose] def owR33_form (w : Fin 3 → ZMod 3) (a v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  v - (owR33_alphaVal w a v) • a

def owR33_W112 : Fin 3 → ZMod 3 := ![1, 1, 2]
def owR33_A112 : Fin 3 → Fin 3 → ZMod 3 := ![![1, 0, 0], ![1, 1, 1], ![0, 1, 0]]
def owR33_X112 : Fin 6 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![1, 1, 1], ![0, 1, 0], ![2, 1, 1], ![1, 2, 1], ![2, 2, 1]]

theorem owR33_data112 :
    (∀ i, ∑ k, owR33_W112 k * (owR33_A112 i k * owR33_A112 i k) = 1) ∧
    (owR33_X112 0 = owR33_A112 0 ∧ owR33_X112 1 = owR33_A112 1 ∧
      owR33_X112 2 = owR33_A112 2) ∧
    (owR33_X112 3 = owR33_form owR33_W112 (owR33_A112 1) (owR33_X112 0) ∧
      owR33_X112 4 = owR33_form owR33_W112 (owR33_A112 2) (owR33_X112 1) ∧
      owR33_X112 5 = owR33_form owR33_W112 (owR33_A112 2) (owR33_X112 3)) ∧
    (∀ y : Fin 3 → ZMod 3, (∑ k, owR33_W112 k * (y k * y k)) = 1 →
      ∃ k : Fin 6, y = owR33_X112 k ∨ y = -owR33_X112 k) ∧
    (∀ i j, owR33_alphaVal owR33_W112 (owR33_A112 i) (owR33_A112 j)
      = (CartanMatrix.A 3 i j : ZMod 3)) := by decide +kernel

def owR33_W121 : Fin 3 → ZMod 3 := ![1, 2, 1]
def owR33_A121 : Fin 3 → Fin 3 → ZMod 3 := ![![1, 0, 0], ![1, 1, 1], ![0, 0, 1]]
def owR33_X121 : Fin 6 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![1, 1, 1], ![0, 0, 1], ![2, 1, 1], ![1, 1, 2], ![2, 1, 2]]

theorem owR33_data121 :
    (∀ i, ∑ k, owR33_W121 k * (owR33_A121 i k * owR33_A121 i k) = 1) ∧
    (owR33_X121 0 = owR33_A121 0 ∧ owR33_X121 1 = owR33_A121 1 ∧
      owR33_X121 2 = owR33_A121 2) ∧
    (owR33_X121 3 = owR33_form owR33_W121 (owR33_A121 1) (owR33_X121 0) ∧
      owR33_X121 4 = owR33_form owR33_W121 (owR33_A121 2) (owR33_X121 1) ∧
      owR33_X121 5 = owR33_form owR33_W121 (owR33_A121 2) (owR33_X121 3)) ∧
    (∀ y : Fin 3 → ZMod 3, (∑ k, owR33_W121 k * (y k * y k)) = 1 →
      ∃ k : Fin 6, y = owR33_X121 k ∨ y = -owR33_X121 k) ∧
    (∀ i j, owR33_alphaVal owR33_W121 (owR33_A121 i) (owR33_A121 j)
      = (CartanMatrix.A 3 i j : ZMod 3)) := by decide +kernel

def owR33_W211 : Fin 3 → ZMod 3 := ![2, 1, 1]
def owR33_A211 : Fin 3 → Fin 3 → ZMod 3 := ![![0, 1, 0], ![1, 1, 1], ![0, 0, 1]]
def owR33_X211 : Fin 6 → Fin 3 → ZMod 3 :=
  ![![0, 1, 0], ![1, 1, 1], ![0, 0, 1], ![1, 2, 1], ![1, 1, 2], ![1, 2, 2]]

theorem owR33_data211 :
    (∀ i, ∑ k, owR33_W211 k * (owR33_A211 i k * owR33_A211 i k) = 1) ∧
    (owR33_X211 0 = owR33_A211 0 ∧ owR33_X211 1 = owR33_A211 1 ∧
      owR33_X211 2 = owR33_A211 2) ∧
    (owR33_X211 3 = owR33_form owR33_W211 (owR33_A211 1) (owR33_X211 0) ∧
      owR33_X211 4 = owR33_form owR33_W211 (owR33_A211 2) (owR33_X211 1) ∧
      owR33_X211 5 = owR33_form owR33_W211 (owR33_A211 2) (owR33_X211 3)) ∧
    (∀ y : Fin 3 → ZMod 3, (∑ k, owR33_W211 k * (y k * y k)) = 1 →
      ∃ k : Fin 6, y = owR33_X211 k ∨ y = -owR33_X211 k) ∧
    (∀ i j, owR33_alphaVal owR33_W211 (owR33_A211 i) (owR33_A211 j)
      = (CartanMatrix.A 3 i j : ZMod 3)) := by decide +kernel

def owR33_W222 : Fin 3 → ZMod 3 := ![2, 2, 2]
def owR33_A222 : Fin 3 → Fin 3 → ZMod 3 := ![![0, 1, 1], ![1, 0, 2], ![0, 2, 1]]
def owR33_X222 : Fin 6 → Fin 3 → ZMod 3 :=
  ![![0, 1, 1], ![1, 0, 2], ![0, 2, 1], ![1, 1, 0], ![1, 2, 0], ![1, 0, 1]]

theorem owR33_data222 :
    (∀ i, ∑ k, owR33_W222 k * (owR33_A222 i k * owR33_A222 i k) = 1) ∧
    (owR33_X222 0 = owR33_A222 0 ∧ owR33_X222 1 = owR33_A222 1 ∧
      owR33_X222 2 = owR33_A222 2) ∧
    (owR33_X222 3 = owR33_form owR33_W222 (owR33_A222 1) (owR33_X222 0) ∧
      owR33_X222 4 = owR33_form owR33_W222 (owR33_A222 2) (owR33_X222 1) ∧
      owR33_X222 5 = owR33_form owR33_W222 (owR33_A222 2) (owR33_X222 3)) ∧
    (∀ y : Fin 3 → ZMod 3, (∑ k, owR33_W222 k * (y k * y k)) = 1 →
      ∃ k : Fin 6, y = owR33_X222 k ∨ y = -owR33_X222 k) ∧
    (∀ i j, owR33_alphaVal owR33_W222 (owR33_A222 i) (owR33_A222 j)
      = (CartanMatrix.A 3 i j : ZMod 3)) := by decide +kernel

def owR33_W111 : Fin 3 → ZMod 3 := ![1, 1, 1]
@[expose] def owR33_E111 : Fin 3 → ZMod 3 := ![1, 0, 0]
def owR33_W122 : Fin 3 → ZMod 3 := ![1, 2, 2]
@[expose] def owR33_E122 : Fin 3 → ZMod 3 := ![1, 0, 0]
def owR33_W212 : Fin 3 → ZMod 3 := ![2, 1, 2]
@[expose] def owR33_E212 : Fin 3 → ZMod 3 := ![0, 1, 0]
def owR33_W221 : Fin 3 → ZMod 3 := ![2, 2, 1]
@[expose] def owR33_E221 : Fin 3 → ZMod 3 := ![0, 0, 1]

theorem owR33_red111 :
    owR33_E111 ≠ 0 ∧
    (∀ a : Fin 3 → ZMod 3, (∑ k, owR33_W111 k * (a k * a k)) = 1 →
      ∃ c : ZMod 3, owR33_form owR33_W111 a owR33_E111 = c • owR33_E111) := by
  decide +kernel

theorem owR33_red122 :
    owR33_E122 ≠ 0 ∧
    (∀ a : Fin 3 → ZMod 3, (∑ k, owR33_W122 k * (a k * a k)) = 1 →
      ∃ c : ZMod 3, owR33_form owR33_W122 a owR33_E122 = c • owR33_E122) := by
  decide +kernel

theorem owR33_red212 :
    owR33_E212 ≠ 0 ∧
    (∀ a : Fin 3 → ZMod 3, (∑ k, owR33_W212 k * (a k * a k)) = 1 →
      ∃ c : ZMod 3, owR33_form owR33_W212 a owR33_E212 = c • owR33_E212) := by
  decide +kernel

theorem owR33_red221 :
    owR33_E221 ≠ 0 ∧
    (∀ a : Fin 3 → ZMod 3, (∑ k, owR33_W221 k * (a k * a k)) = 1 →
      ∃ c : ZMod 3, owR33_form owR33_W221 a owR33_E221 = c • owR33_E221) := by
  decide +kernel


theorem owR33_w_cases (w : Fin 3 → ZMod 3) (hw : ∀ i, w i ≠ 0) :
    w = owR33_W111 ∨ w = owR33_W112 ∨ w = owR33_W121 ∨ w = owR33_W122 ∨
    w = owR33_W211 ∨ w = owR33_W212 ∨ w = owR33_W221 ∨ w = owR33_W222 := by
  revert hw w
  decide +kernel

end CFSG.StandardType.ZS

end
