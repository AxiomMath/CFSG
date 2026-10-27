module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.CommonJRowLinTwo

open CFSG.Assembly
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf

theorem ggCommonJRowLinTwo_labelSparse {d : ℕ} (hd : 6 ≤ d)
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (e : Matrix.SpecialLinearGroup (Fin (d - 2)) F2 ≃* J) :
    LargeEvenInLambda2 (⟨.A, d - 3, 1⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, d - 3, 1⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
  constructor
  · simp only [LargeEvenInLambda2]
    omega
  · have hk : 2 ≤ d - 2 := by omega
    have hK : Nat.card F2 = 2 ^ 1 := by
      simpa using GaloisField.card 2 1 (by norm_num)
    have hne2 : (d - 2, 2 ^ 1) ≠ (2, 2) := by
      intro h
      have h1 : d - 2 = 2 := by simpa using congrArg Prod.fst h
      omega
    have hne3 : (d - 2, 2 ^ 1) ≠ (2, 3) := by
      intro h
      have h2 : 2 ^ 1 = 3 := by simpa using congrArg Prod.snd h
      norm_num at h2
    have h := ggHasLabel_of_mulEquiv_specialLinear (K := F2) (k := d - 2) (f := 1)
      hk hK hne2 hne3 e
    rwa [show (d - 2) - 1 = d - 3 from by omega] at h

theorem ggCommonJRowLinTwo_labelDense {d m : ℕ} (hm : 3 ≤ m)
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d) F2)}
    (e : Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2) ≃* J) :
    LargeEvenInLambda2 (⟨.A, m - 1, 2⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, m - 1, 2⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) := by
  constructor
  · simp only [LargeEvenInLambda2]
    omega
  · have hk : 2 ≤ m := by omega
    have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := by
      simpa using GaloisField.card 2 2 (by norm_num)
    have hne2 : (m, 2 ^ 2) ≠ (2, 2) := by
      intro h
      have h1 : m = 2 := by simpa using congrArg Prod.fst h
      omega
    have hne3 : (m, 2 ^ 2) ≠ (2, 3) := by
      intro h
      have h2 : 2 ^ 2 = 3 := by simpa using congrArg Prod.snd h
      norm_num at h2
    exact ggHasLabel_of_mulEquiv_specialLinear (K := GaloisField 2 2) (k := m) (f := 2)
      hk hK hne2 hne3 e

end CFSG.StandardType.CommonJRowLinTwo

end
