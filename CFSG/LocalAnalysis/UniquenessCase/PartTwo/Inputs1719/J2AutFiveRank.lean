module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.J2FiveStrong
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

@[expose] def K_J2_aut_five_rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 →
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut X)) = 2


theorem k_J2_aut_five_rank_holds : K_J2_aut_five_rank := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  haveI : Finite ↥j2P := Subtype.finite
  have hcard : Nat.card (MulAut ↥j2P) = 1209600 := by
    obtain ⟨-, -, -, -, h⟩ := ctuc_j2_full_automorphism_permutation_model
    exact h
  have hconjinj : Function.Injective (MulAut.conj : ↥j2P →* MulAut ↥j2P) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
      ctuc_j2_normalizing_involution_permutation_model
    exact h
  obtain ⟨E₀, hE, hEcard⟩ := CFSG.HardMathSupport.Dickson.I271.j2P_elemAbelian_twentyfive
  let f : ↥E₀ →* MulAut ↥j2P :=
    (MulAut.conj : ↥j2P →* MulAut ↥j2P).comp E₀.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hconjinj hxy)
  have hlower : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut ↥j2P)) :=
    CFSG.SectionRank.le_pRank_of_injective (A := ↥E₀) (G := MulAut ↥j2P)
      (p := 5) (k := 2) (by norm_num) (fun a b => hE.1.is_comm.comm a b)
      (fun a => Subtype.ext (hE.2 a.1 a.2)) hEcard f hf le_top
  have hupper : CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut ↥j2P)) ≤ 2 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveRanksNotLe.pRank_top_le_of_not_dvd_card
      (k := 2) Nat.prime_five (by rw [hcard]; norm_num)
  have hmain : CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut ↥j2P)) = 2 :=
    le_antisymm hupper hlower
  let ψ : X ≃* ↥j2P := (e : X ≃* CFSG.Blueprint.NativeSporadic.J2).trans j2PermEquiv
  calc CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut X))
      = CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut ↥j2P)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) (MulAut.congr ψ)
    _ = 2 := hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
