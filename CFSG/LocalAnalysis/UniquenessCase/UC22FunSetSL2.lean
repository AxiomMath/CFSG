module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwoLower
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactorSylowShape
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.CGT.Timmesfeld75.NodeAux
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Rho
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped MatrixGroups


theorem nonempty_mulEquiv_sl2_of_mem_funSet {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (htwo : FunTwoType t n) (hD4 : t ≠ .trialityD4) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    Nonempty (K ≃* SL(2, GaloisField p f)) := by
  have hp : p.Prime := Fact.out
  have hfund : IsFundTag t := by cases t <;> simp_all [FunTwoType, IsFundTag]
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p f hp hp2 hfund hadm X hX
  obtain ⟨R, hR, -, -, -⟩ := exists_commuting_modelFund_of_funTwoType hp2 hadm htwo
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hψk eR
      exact ⟨ψ a, ψ b, hab⟩
    · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hψk eR
      exact ⟨ψ a, ψ b, hab⟩
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.CGT.Timmesfeld75.center_eq_bot_of_simple_nonabelian X hnc
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro h2
    exact PartTwo.Inputs1719.k_LieModelNotL2_holds (X ⧸ Subgroup.center X) t n p f (p ^ f) hp2
      (by
        by_cases ht : t = .PSL
        · subst t; right; change n = 4 ∨ n = 5 at htwo; omega
        · exact Or.inl ht) hadm (CFSG.Blueprint.LieModel.quotient_center hZ hX) h2
  obtain ⟨R', hR', rfl, hdisj⟩ :=
    exists_mem_fundamentalSubgroups_of_mem_funSet hp hp2 hadm hX htwo hL2 ψ hψs hψk P hK
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR' with ⟨⟨e⟩⟩ | ⟨ht, -⟩
  · exact ⟨(CFSG.LocalAnalysis.ComponentInitial.equivMapOfInfKerEqBot ψ hdisj).symm.trans e⟩
  · exact absurd ht hD4

theorem exists_rho_of_mem_funSet {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hadm : StatedLieAdmissible t n p 1) (hX : CFSG.Blueprint.LieModel X t n p 1)
    (htwo : FunTwoType t n) (hD4 : t ≠ .trialityD4) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred p) X (P : Subgroup X)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p)
      (ρ : normalizer (K : Set X) →* PGL(Fin 2, F)),
      (∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k) ∧
      ¬ IsCyclic ((((P : Subgroup X) ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ) := by
  rw [← pow_one p] at hK
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_of_mem_funSet (by omega) hadm hX htwo hD4 P hK
  have hF : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  exact ⟨GaloisField p 1, inferInstance, inferInstance, inferInstance,
    uc22s2112r34_rho K hp5 hF e, uc22s2112r34_rho_eq_one_iff hp5 hF e,
    uc22s2112r34_rho_not_isCyclic hp5 hF e hK.2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
