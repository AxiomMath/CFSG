module

public import CFSG.Quasithin.Background.F918H2
public import CFSG.Quasithin.Background.F918H4

public section

namespace CFSG.Quasithin

theorem d36c_of_named_inputs (h35 : D35) (hA : D36Acts) (hA38 : D36A38)
    (hL38 : D3L38) : D36c := by
  intro W _ _ M Mp T L V std hlt t ht htn hMp
  have key : ∀ {L : Subgroup (MulAut W)} {t : MulAut W}, D36Norm M Mp T L V t →
      D36cConcl Mp T L V t := by
    intro L t n
    have h2 := d36_part2 hL38 hA n
    exact ⟨n.triv, d36_part1 hL38 n, h2, d36_part3 h35 hA38 hL38 n h2⟩
  rcases d36_reduce h35 hL38 std hlt ht htn hMp with n | n
  · exact Or.inl (key n)
  · exact Or.inr (key n)

end CFSG.Quasithin
