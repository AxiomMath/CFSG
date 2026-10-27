module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCover
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

theorem qTwo_psuTrivialMultiplier
    {m : ℕ} (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m) :
    PSUTrivialMultiplier m := by
  intro E _ _ hperf hL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ 1) ^ 2 ∧
        Nonempty (E ⧸ Subgroup.center E ≃* StatedProj (StatedSU m (2 ^ 1) K)) := by
    rcases hL with ⟨-, -, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals omega
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four
      (by simpa using hK)
  have hcop : Nat.Coprime m (2 ^ 1 + 1) := by
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hZU : Subgroup.center (StatedSU m (2 ^ 1) K) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hK le_rfl (by omega)
      hcop
  have hscal : (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ 1) K) = ⊥ := by
    refine eq_bot_iff.2 fun u hu => ?_
    have hcen : (u : GL (Fin m) K) ∈ Subgroup.center (GL (Fin m) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.1 hu
    have hc : u ∈ Subgroup.center (StatedSU m (2 ^ 1) K) := by
      rw [Subgroup.mem_center_iff]
      intro v
      exact Subtype.ext (Subgroup.mem_center_iff.1 hcen (v : GL (Fin m) K))
    rwa [hZU] at hc
  have hiso : Nonempty (E ⧸ Subgroup.center E ≃*
      StatedSU m (2 ^ 1) K ⧸ Subgroup.center (StatedSU m (2 ^ 1) K)) :=
    ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (hscal.trans hZU.symm))⟩
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π : E' →* StatedSU m (2 ^ 1) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E' →
        ∃ s : StatedSU m (2 ^ 1) K →* E', π.comp s = MonoidHom.id _ := by
    intro E' _ _ π hπ hc
    obtain ⟨s, hs⟩ := CFSG.StandardType.LineU.statedSU_exists_section_unitary hK le_rfl hm
      (fun h => by
        have := congrArg Prod.fst h
        simp only at this
        omega) hπ hc
    exact ⟨s, MonoidHom.ext hs⟩
  obtain ⟨ψ, hψ, -⟩ := ggExists_universal_cover_of_marking hperf hiso hsplit
  have h1 : Nat.card E ≤ Nat.card (StatedSU m (2 ^ 1) K) := Nat.card_le_card_of_surjective ψ hψ
  have h2 : Nat.card E =
      Nat.card (E ⧸ Subgroup.center E) * Nat.card (Subgroup.center E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3' : Nat.card (E ⧸ Subgroup.center E) = Nat.card (StatedSU m (2 ^ 1) K) := by
    rw [Nat.card_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq hscal).trans
      QuotientGroup.quotientBot)).toEquiv]
  have hpos : 0 < Nat.card (StatedSU m (2 ^ 1) K) := Nat.card_pos
  have hZpos : 0 < Nat.card (Subgroup.center E) := Nat.card_pos
  rw [h2, h3'] at h1
  have : Nat.card (Subgroup.center E) ≤ 1 := by
    by_contra hlt
    have : Nat.card (StatedSU m (2 ^ 1) K) * 2 ≤
        Nat.card (StatedSU m (2 ^ 1) K) * Nat.card (Subgroup.center E) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  omega

end CFSG.StandardType.QTwo
