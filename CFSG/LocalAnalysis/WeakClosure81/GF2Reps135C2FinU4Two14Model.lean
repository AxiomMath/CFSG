module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M
import CFSG.LieType.Multipliers.U42
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact
  (exists_twistedA_of_statedClassicalModel_PSU)

theorem finU4_center_eq_bot
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hL : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 1) : Subgroup.center ↥L = ⊥ := by
  have hq : CFSG.IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hdvd : Nat.card (Subgroup.center ↥L) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (↥L ⧸ Subgroup.center ↥L)) :=
    CFSG.ClassicalInvolution.Q3.TL4.E3S3M.natCard_center_dvd hq (MulEquiv.refl _)
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hL
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (↥L ⧸ Subgroup.center ↥L)) = 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ ZMod 2),
      Nat.card_zmod]
  rw [hcard] at hdvd
  have hodd := w135_odd_card_center hctx
  have h1 : Nat.card (Subgroup.center ↥L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem finU4_isU4Group {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : LieModel ↥L .PSU 4 2 1) : IsU4Group 1 L := by
  have hC := CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  obtain ⟨q, hv, hp, hqe, ⟨φ⟩⟩ := exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
  exact ⟨⟨_, hv⟩, ⟨q, hp, hqe, rfl⟩, ⟨φ⟩⟩

theorem finU4_natural_card {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}
    (h : NaturalU4Mod 1 L) : Nat.card S = 2 ^ 8 ∨ Nat.card S = 2 ^ 6 := by
  rcases h with ⟨F, _, _, hF, ε, ψ, -⟩ | ⟨F, _, _, b, c, hF, -, ε, ψ, -⟩
  · left
    have h1 : Nat.card S = Nat.card (Fin 4 → F) :=
      (Nat.card_congr ψ.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
    rw [h1, Nat.card_fun, hF]
    simp
  · right
    have h1 : Nat.card S = Nat.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
      (Nat.card_congr ψ.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
    rw [h1, Nat.card_fun, hF]
    simp

end CFSG.LocalAnalysis.WeakClosure81
