module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Hyp139Low
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Hyp139

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem concl139_of_hyp139_le_two {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W} {n : ℕ}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ n)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (n - 1))
    (hYD : Y ≤ fixV D)
    (hn : n ≤ 2) :
    Concl139Printed W G X n := by
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl
  · exact absurd (one_le_n_of_hyp139_data hW hXG hXcard) (by omega)
  · exact concl139_one_of_hyp139_n1 hw2 hK hpCore hirr ht2 hXG hXnorm hXcard hsG
      hs_ord2 hs_not_cent hYinv hYrk hW hD hDCX hDs hElem hDcard hYD
  · exact concl139_two_of_hyp139_n2 hw2 hK hpCore hirr ht2 hXG hXnorm hXcard hsG
      hs_ord2 hs_not_cent hYinv hYrk hW hD hDCX hDs hElem hDcard hYD

end CFSG.LocalAnalysis.WeakClosure81
