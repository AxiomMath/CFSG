module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ProofModels
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCases
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem exists_conj_le_of_model {X G : Type*} [Group X] [Group G] (φ : X →* G)
    {G₀ D J : Subgroup G} {D₀ T₀ : Subgroup X} (hφ : φ.range ≤ G₀) (hD : D ≤ D₀.map φ)
    (hT : T₀.map φ ≤ J) {n : X} (hn : D₀.map (MulAut.conj n).toMonoidHom ≤ T₀) :
    ∃ g ∈ G₀, D.map (MulAut.conj g).toMonoidHom ≤ J := by
  refine ⟨φ n, hφ ⟨n, rfl⟩, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨d₀, hd₀, rfl⟩ := hD hd
  apply hT
  refine ⟨n * d₀ * n⁻¹, hn ⟨d₀, hd₀, rfl⟩, ?_⟩
  simp [map_mul, map_inv]

section Inputs

@[expose] def GGSixLSixSevenA3EntryPSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSL n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL n f).D .PSL n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    GGSixLSevenA3Case J →
      ∃ φ : Matrix.SpecialLinearGroup (Fin 8) (ZMod 2) →* G,
        φ.range ≤ ggG0 p B x L D J ∧ D ≤ GGA3.slD.map φ ∧ GGA3.slT.map φ ≤ J

@[expose] def GGSixLSixSevenConjA3RestSeven : Prop :=
  GGSixLSixSevenConjA3At .PSU ∧ GGSixLSixSevenConjA3At .PSp ∧
    GGSixLSixSevenConjA3At .POmegaMinus ∧ GGSixLSixSevenConjA3At .F4 ∧
    GGSixLSixSevenConjA3At .E7 ∧ GGSixLSixSevenConjA3At .E8 ∧
    GGSixLSixSevenConjA3At .twistedE6

theorem ggSixLSixSevenConjA3At_PSL_of_entry (h : GGSixLSixSevenA3EntryPSL) :
    GGSixLSixSevenConjA3At .PSL := by
  intro G _ _ p B Bs x L D J n f ψ hctx hC2 hodd hcomp hA
  obtain ⟨φ, hφ, hD, hT⟩ := h G p B Bs x L D J n f ψ hctx hC2 hodd hcomp hA
  exact exists_conj_le_of_model φ hφ hD hT GGA3.map_conj_swapSL_slD.le

theorem ggSixLSixSevenConjA3At_of_small {t : StatedLieTag} (ht : GGOrdPSmallTag t) :
    GGSixLSixSevenConjA3At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ _
  obtain ⟨hadm, hrank⟩ := hctx.2.2.2.1
  rcases ht with ht | ht | ht | ht | ht | ht | rfl
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inl ht)] at hrank
    omega
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inr (Or.inl ht))] at hrank
    omega
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two (Or.inr (Or.inr (Or.inl ht)))] at hrank
    omega
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two
      (Or.inr (Or.inr (Or.inr (Or.inl ht))))] at hrank
    omega
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))] at hrank
    omega
  · rw [lieUniversal_rank_eq_zero t n 2 f Nat.prime_two
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))] at hrank
    omega
  · exact absurd rfl hadm.2.2.2

theorem ggSixLSixSevenConjA3Input_of_rest (hPSL : GGSixLSixSevenConjA3At .PSL)
    (hPlus : GGSixLSixSevenConjA3At .POmegaPlus) (hE6 : GGSixLSixSevenConjA3At .E6)
    (hr : GGSixLSixSevenConjA3RestSeven) : GGSixLSixSevenConjA3Input := by
  obtain ⟨hU, hSp, hMinus, hF4, hE7, hE8, hTwE6⟩ := hr
  refine ggSixLSixSevenConjA3Input_of_tags fun t => ?_
  cases t with
  | PSL => exact hPSL
  | PSU => exact hU
  | PSp => exact hSp
  | POmegaOdd => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | G2 => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | trialityD4 => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | twistedB2 => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | twistedG2 => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | twistedF4 => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])
  | Tits => exact ggSixLSixSevenConjA3At_of_small (by simp [GGOrdPSmallTag])

end Inputs

end CFSG.StandardType
