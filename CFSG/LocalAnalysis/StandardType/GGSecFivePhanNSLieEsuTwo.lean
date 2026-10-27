module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
public import CFSG.LocalAnalysis.StandardType.GGNsq2Hopf

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
  CFSG.RankThree.PartOne.S15K Matrix

theorem ggNSLie_cover_of_esu_odd
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop} (hP : ∀ p lab, P p lab → ggRowP_ESU p lab)
    (hodd : Odd (Nat.card (Subgroup.center ↥X))) (h : GGInnerDiagOnLabel P p Bs X) :
    ∃ (lab : LargeEvenLabel) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ)
      (ψ : Su K 2 f n →* G), P p lab ∧ n = lab.rank + 1 ∧ f = lab.n ∧
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGActsUnitarily (p := 2) (f := f) ψ Bs ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) := by
  refine ggNSLie_cover_of_esu_of_lift hP h ?_
  intro lab m K _ _ hlab hK h4m hmrank hperf η hηsurj hηker
  by_cases hne : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
  · obtain ⟨hn1, hr35⟩ := hne
    obtain ⟨t, r, n⟩ := lab
    subst hn1
    have hcop : Nat.Coprime (Nat.card η.ker) 4 := by
      have hoddker : Odd (Nat.card η.ker) :=
        Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hηker)
      simpa using hoddker.coprime_two_right.pow_right 2
    have hm46 : m = 4 ∨ m = 6 := by
      rcases hr35 with h3 | h5
      · left
        omega
      · right
        omega
    rcases hm46 with rfl | rfl
    · exact exists_cover_u2 hK (Or.inl rfl) η hηsurj ⟨hperf⟩ hηker hcop
    · exact exists_cover_u2 hK (Or.inr rfl) η hηsurj ⟨hperf⟩ hηker hcop
  · exact ggNSLie_lift_of_ne hK h4m hmrank hne hperf η hηsurj hηker

end CFSG.StandardType

end
