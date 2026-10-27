module

public import Certificates.Certificate3085

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly

@[expose] def r3eH : J := (a * b) * lyz * (a * b)⁻¹

@[expose] def r3eG : J := (r3eH * lyf) ^ 7 * (lyz * r3eH) ^ 4

@[expose] def r3eWords : List (List ℤ) :=
  [[12], [6, 6, -12, 8, 10, 9], [5, 5, 5, 9, 6, 10, -11], [6, -11],
    [-6, 5, -6, -6, 7, 6, 8, 10, 9, 12, 11, 12], [2, 12, 1, -8, 6, -11, -12]]

@[expose] def r3eD (k : ℕ) : J := evalWord cStar (r3eWords.getD k [])

@[expose] def r3eD0 :
    Subgroup J := Subgroup.closure ({lyz, lyf} ∪ r3eD '' Set.Iio 6)

@[expose] def r3eC : J := cStar 3

@[expose] def r3ePowerWord : List ℤ := [4]

@[expose] def r3eExponent : ℕ := 18

@[expose] def r3eSubst :
    List J := [1, lyz, lyf, lyz * lyf].map fun δ => r3eC * δ * r3eG

@[expose] def r3eFusionWord : List ℤ := [3, 2, 3, 2]

@[expose] def r3eFusion : J :=
  evalWord (fun k => if h : k < 6 then sylowGen ⟨k, h⟩ else 1) r3eFusionWord

theorem involution_pointwise_kernel_data :
    r3eH = (a * b) * lyz * (a * b)⁻¹ ∧ r3eG = (r3eH * lyf) ^ 7 * (lyz * r3eH) ^ 4 ∧
    r3eWords = [[12], [6, 6, -12, 8, 10, 9], [5, 5, 5, 9, 6, 10, -11], [6, -11],
      [-6, 5, -6, -6, 7, 6, 8, 10, 9, 12, 11, 12], [2, 12, 1, -8, 6, -11, -12]] ∧
    (∀ k, r3eD k = evalWord cStar (r3eWords.getD k [])) ∧
    r3eD0 = Subgroup.closure ({lyz, lyf} ∪ r3eD '' Set.Iio 6) ∧
    r3eC = cStar 3 ∧ r3eC = evalWord cStar r3ePowerWord ∧ r3eExponent = 18 ∧
    r3eSubst = [r3eC * 1 * r3eG, r3eC * lyz * r3eG, r3eC * lyf * r3eG,
      r3eC * (lyz * lyf) * r3eG] ∧
    r3eFusion = evalWord (fun k => if h : k < 6 then sylowGen ⟨k, h⟩ else 1) [3, 2, 3, 2] := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp [r3eC, r3ePowerWord, evalWord, letterVal]

end CFSG.Sporadic.LySchreier
