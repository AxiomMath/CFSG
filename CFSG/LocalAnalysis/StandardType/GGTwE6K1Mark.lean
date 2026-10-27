module

public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint

private theorem eq_D4_of_dict {lab : LargeEvenLabel} {n : ℕ} (ht : markTag lab = .POmegaPlus)
    (hr : markRank lab = 4) (hf : markDeg lab = n) : lab = ⟨.D, 4, n⟩ := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markDeg] at ht hr hf
  case D =>
    by_cases h3 : r = 3
    · rw [if_pos h3] at ht
      exact absurd ht (by decide)
    · rw [if_neg h3] at hr
      subst hr hf
      rfl
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

private theorem eq_triD4_of_dict {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {n : ℕ}
    (ht : markTag lab = .trialityD4) (hf : markDeg lab = n) : lab = ⟨.triD4, 0, n⟩ := by
  obtain ⟨t, r, m⟩ := lab
  cases t <;> dsimp only [markTag, markDeg] at ht hf
  case triD4 =>
    have hr : r = 0 := hlab.2
    subst hr hf
    rfl
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

private theorem eq_twA_of_dict {lab : LargeEvenLabel} {r f : ℕ} (ht : markTag lab = .PSU)
    (hc : markChar lab = 2) (hr : markRank lab = r + 1) (hf : markDeg lab = f) (h4 : r ≠ 3) :
    lab = ⟨.twA, r, f⟩ := by
  obtain ⟨t, l, m⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markChar, markDeg] at ht hc hr hf
  case twA =>
    obtain rfl := Nat.add_right_cancel hr
    subst hf
    rfl
  case twD =>
    split_ifs at ht hr <;> first | exact absurd ht (by decide) | exact absurd (by omega) h4
  case G2der => exact absurd hc (by decide)
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

theorem largeEvenMarking_k1Labels_of_lieModel {X : Type} [Group X] (hX : commutator X = ⊤)
    {n : ℕ}
    (h : LieModel (X ⧸ Subgroup.center X) .POmegaPlus 4 2 n ∨
      LieModel (X ⧸ Subgroup.center X) .trialityD4 0 2 n ∨
      LieModel (X ⧸ Subgroup.center X) .PSU 3 2 (3 * n) ∨
      LieModel (X ⧸ Subgroup.center X) .PSU 6 2 n) :
    LargeEvenMarking X fun lab' _ _ _ _ _ =>
      (lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
        lab' = ⟨.twA, 2, 3 * n⟩) ∨ lab' = ⟨.twA, 5, n⟩ := by
  have key : ∀ {t r f}, LieModel (X ⧸ Subgroup.center X) t r 2 f →
      (∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → markTag lab = t → markRank lab = r →
        markChar lab = 2 → markDeg lab = f →
        (lab = ⟨.D, 4, n⟩ ∨ lab = ⟨.triD4, 0, n⟩ ∨ lab = ⟨.A, 2, 3 * n⟩ ∨
          lab = ⟨.twA, 2, 3 * n⟩) ∨ lab = ⟨.twA, 5, n⟩) →
      LargeEvenMarking X fun lab' _ _ _ _ _ =>
        (lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
          lab' = ⟨.twA, 2, 3 * n⟩) ∨ lab' = ⟨.twA, 5, n⟩ := by
    intro t r f hm hdict
    obtain ⟨hX', lab, hlab, hraw⟩ := largeEvenMarking_of_lieModel_centerQuot hX hm
    refine ⟨hX', lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, ht, hr, hc, hf⟩
    exact ⟨hs, hna, θ, hdict lab hlab ht hr hc hf⟩
  rcases h with h | h | h | h
  · exact key h fun lab _ ht hr _ hf => Or.inl (Or.inl (eq_D4_of_dict ht hr hf))
  · exact key h fun lab hlab ht _ _ hf => Or.inl (Or.inr (Or.inl (eq_triD4_of_dict hlab ht hf)))
  · exact key h fun lab _ ht hr hc hf =>
      Or.inl (Or.inr (Or.inr (Or.inr (eq_twA_of_dict (r := 2) ht hc hr hf (by decide)))))
  · exact key h fun lab _ ht hr hc hf => Or.inr (eq_twA_of_dict (r := 5) ht hc hr hf (by decide))

end CFSG.StandardType.SCFourCover

end
