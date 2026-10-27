module

public import CFSG.RankThree.PartOne.KE.E7FourStabFive
public import CFSG.RankThree.PartOne.KE.E7FourPerX
import CFSG.RankThree.PartOne.KE.E6FourGraph

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

theorem e7Four_p_cases {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1) :
    p = 5 ∨ 7 < p := by
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.1 h
  have h2 := not_lt.1 h2
  have h7 : p = 7 := by
    interval_cases p
    · exact absurd hp (by decide)
    · exact absurd rfl h1
    · exact absurd hp (by decide)
    · rfl
  subst h7
  have hno : ∀ x : ZMod 7, x ^ 2 + 1 ≠ 0 := by decide
  refine hno (q : ZMod 7) ?_
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 + 1) 7).2 hpf
  simpa using this

section Main

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L ℓ]

omit [Finite K] in
theorem e7_stabHyp (F : E7FourFrame K L ℓ f p) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) :
    E7StabHyp F.n (iterateFrobenius L ℓ f) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpf
    simpa using this
  intro a hap ha1 haT
  have haF : a ∈ fixedCharTuples e7F4W (iterateFrobenius L ℓ f) := by
    have h1 : rootDiagUnit .E7 a ∈ (fixedCharTuples e7F4W (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom .E7 L) := by
      rw [← F.hT]
      exact haT
    obtain ⟨a', ha', ha'a⟩ := h1
    have : a' = a := rootDiagUnit_injective ha'a
    exact this ▸ ha'
  refine rootCharStabilizer_subset_closure_of_fixed e7F4W (iterateFrobenius L ℓ f) hFr hp haF hap
    ha1 (fun z hz0 hzM => ?_)
  rcases e7Four_p_cases hp hp3 hpf with rfl | hp7
  · have hzM' : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ z =
        ((Nat.card K : ℕ) : ZMod 5) • z := by
      rw [← e7F4W_eq]
      exact hzM
    exact e7S5_claim_eigen (zmod5_sq_add_one_eq_zero _ hΦ) hz0 hzM'
  · exact (dualWeylStabilizer_eq_closure
      (not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))) z).le

end Main

end CFSG.RankThree.PartOne.KE
