module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3F1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3F2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_exists_order_three_of_torus {W : Type} [CommGroup W] [Finite W]
    (hcard : Nat.card W = 64) {l : MulAut W} (hl : orderOf l = 3)
    (hfpf : ∀ w : W, l w = w → w = 1) {D J : Subgroup (MulAut W)} (hD : IsElemAbelian 3 D)
    (hD27 : 27 ≤ Nat.card ↥D) (hDl : D ≤ centralizer ({l} : Set (MulAut W)))
    (hJl : J ≤ centralizer ({l} : Set (MulAut W))) (hDJ : D ≤ normalizer (J : Set (MulAut W)))
    (hJgen : ∃ X : Set (MulAut W), (∀ g ∈ X, g ^ 2 = 1) ∧ J = closure X)
    (hJ2 : ¬ IsPGroup 2 J) : ∃ y ∈ J, y ^ 3 = 1 ∧ y ∉ zpowers l := by
  by_contra hcon
  have hJ3 : ∀ y ∈ J, y ^ 3 = 1 → y ∈ zpowers l := fun y hy hy3 => by
    by_contra hyl
    exact hcon ⟨y, hy, hy3, hyl⟩
  exact hJ2 (s16h_isPGroup_two_of_coprime_three hcard hl hfpf hD hD27 hDl hJl hDJ
    (s16h_not_three_dvd_of_torus hcard hl hfpf hD hD27 hJl hDJ hJgen hJ3))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
