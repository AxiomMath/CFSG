module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenUnitary
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenTransport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

private theorem cover_linear_of_lieModel
    {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hpf : p ^ f % 3 = 1) (hQ : CFSG.Open.IsQuasisimple L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (hLie : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL 3 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ∣ Nat.card K - 1 ∧
      Nonempty (SpecialLinearGroup (Fin 3) K ≃* L) := by
  have hperf : commutator L = ⊤ := hQ.1
  have hz : Subgroup.center L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ
    omega
  obtain ⟨F, _, _, hFcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  refine ⟨F, inferInstance, inferInstance, h3, ?_⟩
  by_cases h4 : Nat.card F = 4
  · have hpf4 : p ^ f = 4 := by rw [← hFcard, h4]
    obtain ⟨hp, hf1, -⟩ := hLie.admissible
    have hp2 : p = 2 := by
      have hdvd : p ∣ 2 * 2 := by
        have : p ∣ p ^ f := dvd_pow_self p (by omega)
        rw [hpf4] at this
        simpa using this
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h <;>
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    subst hp2
    have hf2 : f = 2 :=
      Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 2 by rw [hpf4])
    subst hf2
    have hmod := hLie.statedClassicalModel_of_ne_zero (by norm_num)
    have hodd : Odd (Nat.card (Subgroup.center L)) := by
      rw [hZ]
      decide
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour.exists_mulEquiv_specialLinear_four
      h4 hperf hmod e hodd hz
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_mulEquiv_specialLinear h3 h4
      hperf e hz

private theorem cover_unitary_of_lieModel
    {L : Type} [Group L] [Finite L]
    {p f : ℕ} (hpf : p ^ f % 3 = 2) (hQ : CFSG.Open.IsQuasisimple L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (hLie : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 3 p f) :
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : UnitaryFieldData p f K), 2 < p ^ f ∧
      p ^ f % 3 = 2 ∧ Nonempty (↥(unitarySU p f K 3) ≃* L) := by
  have hperf : commutator L = ⊤ := hQ.1
  have hz : Subgroup.center L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨hp, hf1, hadm⟩, F, _, _, hFcard, ⟨e⟩⟩ :=
    hLie.statedClassicalModel_of_ne_zero (by norm_num)
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2 (by rw [h1, h2])
  have hU : UnitaryFieldData p f F := ⟨hp, hf1, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hq2 : 2 < p ^ f := by
    have : p ^ f ≠ 2 := fun h => hq ⟨rfl, h⟩
    omega
  exact ⟨p, f, F, inferInstance, hU, hq2, hpf,
    CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_mulEquiv_unitarySU_three hU hq2
      hperf (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm) hz⟩

theorem cover_of_isSL3pi
    {L : Type} [Group L] [Finite L] (hL : IsSL3pi L) :
    (∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ∣ Nat.card K - 1 ∧
      Nonempty (SpecialLinearGroup (Fin 3) K ≃* L)) ∨
    (∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : UnitaryFieldData p f K), 2 < p ^ f ∧
      p ^ f % 3 = 2 ∧ Nonempty (↥(unitarySU p f K 3) ≃* L)) := by
  rcases hL with ⟨p, f, hpf, hQ, hZ, hLie⟩ | ⟨p, f, hpf, hQ, hZ, hLie⟩
  · exact Or.inl (cover_linear_of_lieModel hpf hQ hZ hLie)
  · exact Or.inr (cover_unitary_of_lieModel hpf hQ hZ hLie)

theorem sl3Gen_holds :
    SL3Gen := by
  intro H _ _ L T a hSL hLn hT ha ha3 hnc hidx hab
  have hTnc := not_isMulCommutative_of_isSylowOf hSL.isQuasisimple hSL.card_center hT
  rcases cover_of_isSL3pi hSL with ⟨K, _, _, h3, ⟨ψ⟩⟩ | ⟨p, f, K, _, h, hq, hq3, ⟨ψ⟩⟩
  · exact SL3G.model_transport (SL3G.linearModelGen h3) hLn ψ hT ha ha3 hnc hidx hab hTnc
  · exact SL3G.model_transport (SL3G.unitaryModelGen h hq hq3) hLn ψ hT ha ha3 hnc hidx hab hTnc

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
