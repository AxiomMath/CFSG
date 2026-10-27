module

public import CFSG.LocalAnalysis.WeakClosure81.W116Inner
public import CFSG.LocalAnalysis.WeakClosure81.W116Outer
public import CFSG.LocalAnalysis.WeakClosure81.W115WeakDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w4Lem11_6Weak_holds :
    W4Lem11_6Weak := by
  classical
  intro W _ _ hW Y L hLY hnorm hF hq hO2 hZ hSp hirr
  have hEven : Even (Nat.card Y) := by
    have h1 : Nat.card ↥L ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hLY
    rw [w116_card_cover hZ hSp] at h1
    exact even_iff_two_dvd.2 (dvd_trans (by norm_num) h1)
  unfold E3.mParam
  rw [if_pos hEven]
  refine le_csInf ?_ ?_
  · obtain ⟨t, hto⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
    exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
  · rintro n ⟨t, htY, hto, rfl⟩
    by_cases htL : t ∈ L
    · exact w116_inner_ge hW hq hZ hSp hirr htL hto
    · exact w116_outer_ge hW hLY hnorm hF hq hZ hSp hirr htY htL hto

end CFSG.LocalAnalysis.WeakClosure81.W115
