module

public import CFSG.Quasithin.Background.F918H2
public import CFSG.Quasithin.Background.F918H4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d36Asm_holds (h35 : D35) (hA : D36Acts) (hA38 : D36A38)
    (hL38 : D3L38) :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → V < orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
        Mp = L ⊔ conjAutSub t L →
          (D36cConcl Mp T L V t ∧
              ∀ A : Subgroup (MulAut W), A ≤ T →
                autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
                  A ≤ stabSub (commSub (orbSup T V) L)) ∨
            (D36cConcl Mp T (conjAutSub t L) V t⁻¹ ∧
              ∀ A : Subgroup (MulAut W), A ≤ T →
                autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
                  A ≤ stabSub (commSub (orbSup T V) (conjAutSub t L))) := by
  intro W _ _ M Mp T L V std hlt t ht htn hMp
  have key : ∀ {L : Subgroup (MulAut W)} {t : MulAut W}, D36Norm M Mp T L V t →
      D36cConcl Mp T L V t ∧ ∀ A : Subgroup (MulAut W), A ≤ T →
        autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
          A ≤ stabSub (commSub (orbSup T V) L) := by
    intro L t n
    have h2 := d36_part2 hL38 hA n
    exact ⟨⟨n.triv, d36_part1 hL38 n, h2, d36_part3 h35 hA38 hL38 n h2⟩,
      fun A hAT hQ => hA W M Mp T L V t n A hAT hQ⟩
  rcases d36_reduce h35 hL38 std hlt ht htn hMp with n | n
  · exact Or.inl (key n)
  · exact Or.inr (key n)

end CFSG.Quasithin
