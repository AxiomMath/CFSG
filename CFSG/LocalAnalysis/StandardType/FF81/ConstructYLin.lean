module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYDiagram
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult

public section

namespace CFSG.StandardType.FF81

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem FrameSystem.center_eq_bot_of_commute
    (hC : CurtisA2) (hF : FrameSystem n b L K t)
    (hn : n = 5 ∨ n = 6) (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    Subgroup.center ↥(⨆ i : Fin (n + 2), K (i : ℕ)) = ⊥ := by
  obtain ⟨hq, hm⟩ := hF.lieModel_of_commute hC (by omega) h1n
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(⨆ i : Fin (n + 2), K (i : ℕ)) := hq.1
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ (n + 3) 2 1
    (hm.statedClassicalModel (by decide))
  have hdvd := CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier e
  obtain ⟨-, ⟨M⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl_generic 2 1 (n + 3)
    one_pos (by omega) (Or.inr (Or.inr (by omega)))
  have hE : CFSG.Open.griessPSLExceptional (n + 3) (2 ^ 1) = (1, 1) :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.griessPSLExceptional_eq_one (by simp) (by simp)
      (by omega) (by omega) (by omega)
  have hg : Nat.gcd (n + 3) (2 ^ 1 - 1) = 1 := by simp
  rw [hE, hg] at M
  have h1 : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin (n + 3)) (GaloisField 2 1))) = 1 := by
    rw [Nat.card_congr M.toEquiv]
    simp
  rw [h1] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

theorem FrameSystem.statedClassicalModel_of_commute
    (hC : CurtisA2) (hF : FrameSystem n b L K t)
    (hn : n = 5 ∨ n = 6) (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    CFSG.Open.StatedClassicalModel ↥(⨆ i : Fin (n + 2), K (i : ℕ))
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 3) 2 1 := by
  obtain ⟨-, hm⟩ := hF.lieModel_of_commute hC (by omega) h1n
  have hZ := hF.center_eq_bot_of_commute hC hn h1n
  let e : ↥(⨆ i : Fin (n + 2), K (i : ℕ)) ⧸ Subgroup.center ↥(⨆ i : Fin (n + 2), K (i : ℕ)) ≃*
      ↥(⨆ i : Fin (n + 2), K (i : ℕ)) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (CFSG.Blueprint.LieModel.of_mulEquiv e hm).statedClassicalModel (by decide)

theorem FrameSystem.yLab_of_commute
    (hC : CurtisA2) (hF : FrameSystem n b L K t)
    (hn : n = 5 ∨ n = 6) (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) :
    YLab n (⨆ i : Fin (n + 2), K (i : ℕ)) :=
  Or.inl (hF.statedClassicalModel_of_commute hC hn h1n)

theorem FrameSystem.L_le_join (hF : FrameSystem n b L K t) :
    L ≤ ⨆ i : Fin (n + 2), K (i : ℕ) := by
  rw [← hF.sysL.2.1]
  exact iSup_le fun j => le_iSup (fun i : Fin (n + 2) => K (i : ℕ)) ⟨(j : ℕ) + 2, by omega⟩

end CFSG.StandardType.FF81
