module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Rho
public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Norm

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {F : OmegaFrame Q 1 1} {k : Subfield K} {Rat M : Subgroup (V ≃ₗ[K] V)}

theorem lemmaB [Finite K] (hk : ∀ x : K, x ∈ k ↔ x = 0 ∨ x = 1) {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = 2 ^ p) (R : RatGroupData F k Rat) (hRM : Rat ≤ M) {u w : V}
    (hQu : Q u = 0) (hQw : Q w = 0) (huw : polar Q u w = 0) (hM : eichler Q u w ∈ M)
    (hδ : Phi Q u w (F.e 0) (F.e 1) ∉ k) :
    (∀ t : K, eichler Q (F.e 0) (t • F.e 1) ∈ M) ∨
      ∃ (T : F2Triple Q) (u' w' : V), T.IsRat F k ∧ Q u' = 0 ∧ Q w' = 0 ∧ polar Q u' w' = 0 ∧
        T.Generic u' w' ∧ eichler Q u' w' ∈ M := by
  have hδ0 : Phi Q u w (F.e 0) (F.e 1) ≠ 0 := fun h => hδ (h ▸ k.zero_mem)
  by_cases hg₁ : F.triple₁.Generic u w
  · exact Or.inr ⟨F.triple₁, u, w, F.triple₁_isRat, hQu, hQw, huw, hg₁, hM⟩
  by_cases hg₂ : F.triple₂.Generic u w
  · exact Or.inr ⟨F.triple₂, u, w, F.triple₂_isRat, hQu, hQw, huw, hg₂, hM⟩
  by_cases hg₃ : (F.triple₃ 0).Generic u w
  · exact Or.inr ⟨F.triple₃ 0, u, w, F.triple₃_isRat 0, hQu, hQw, huw, hg₃, hM⟩
  by_cases hg₄ : (F.triple₃ 1).Generic u w
  · exact Or.inr ⟨F.triple₃ 1, u, w, F.triple₃_isRat 1, hQu, hQw, huw, hg₄, hM⟩
  have b₁ : F.BadAt k u w (F.e 2) := F.badAt_of_not_generic hk _ _ _ _ _ hδ0 hg₁
  have b₂ : F.BadAt k u w (F.f 2) := F.badAt_of_not_generic hk _ _ _ _ _ hδ0 hg₂
  have b₃ : F.BadAt k u w (F.e 2 + F.f 2 + F.t 0) :=
    F.badAt_of_not_generic hk _ _ _ _ _ hδ0 hg₃
  have b₄ : F.BadAt k u w (F.e 2 + F.f 2 + F.t 1) :=
    F.badAt_of_not_generic hk _ _ _ _ _ hδ0 hg₄
  have bt₀ : F.BadAt k u w (F.t 0) := by
    have e : F.t 0 = F.e 2 + F.f 2 + F.t 0 - F.e 2 - F.f 2 := by abel
    rw [e]
    exact (b₃.sub b₁).sub b₂
  have bt₁ : F.BadAt k u w (F.t 1) := by
    have e : F.t 1 = F.e 2 + F.f 2 + F.t 1 - F.e 2 - F.f 2 := by abel
    rw [e]
    exact (b₄.sub b₁).sub b₂
  obtain ⟨u', w', hQu', hQw', huw', hM', hΦ', hperp'⟩ :=
    exists_normalized R hRM hQu hQw huw hM b₁ b₂ bt₀ bt₁
  rw [← hΦ'] at hδ
  rcases dichotomy hk hp hK R hRM hQu' hQw' huw' hM' hperp' hδ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨F.starTriple, u', w', F.starTriple_isRat, hQu', hQw', huw', h, hM'⟩

end CFSG.RankThree.PartOne.SEITZ2
