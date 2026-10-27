module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem ggNSLocalHyp_of_nbr (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hrange : ψ.range = X)
    (hdvd : p ∣ 2 ^ f + 1) (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs) :
    GGNSLocalHyp p B Bs K f n ψ := by
  have hcfg' : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hcfg'.1.2.2.2.2.2.2.1
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  refine ⟨hp, (ggRouteCfg_prime hcfg).2, hcard, hdvd, hn, hker, hcfg'.2.1,
    ggNSPosPD_routeCfg_rank hcfg', Or.inr hS.1, ?_, ggRouteCfg_noTransvection hcfg, hacts⟩
  rw [hrange]
  rcases hX with rfl | ⟨y, hnbr⟩
  · exact ggNSPosPD_routeCfg_cent_L hcfg'
  · exact ggNSPosPD_routeCfg_cent_K hp hnbr

theorem ggNSLocalHyp_of_routeCfg (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hrange : ψ.range = X)
    (hdvd : p ∣ 2 ^ f + 1) (hacts : GGActsUnitarily (p := 2) (f := f) ψ Bs) :
    GGNSLocalHyp p B Bs K f n ψ :=
  ggNSLocalHyp_of_nbr hcfg (hX.imp_right (hcfg.2.2.2.1.2 X)) hcard hn hker hrange hdvd hacts

end CFSG.StandardType

end
