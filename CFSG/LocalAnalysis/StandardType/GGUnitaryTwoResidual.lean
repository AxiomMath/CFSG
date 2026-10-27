module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUCore
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}

theorem ggSu_top_le_closure_two (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n) :
    (⊤ : Subgroup (Su K 2 f n)) ≤
      Subgroup.closure {x : Su K 2 f n | ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : SU (unitaryInvolution K 2 f) n ≃* Su K 2 f n :=
    (equivStatedSU hK n).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)).symm
  exact OTwoGen.top_le_closure_of_surjective e.toMonoidHom e.surjective
    (RootCentSU.top_le_closure_SU hK hn)

theorem ggSu_range_le_ggOTwoPrime {G : Type} [Group G]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (θ : Su K 2 f n →* G) {C : Subgroup G} (hθ : θ.range ≤ C) :
    θ.range ≤ ggOTwoPrime C :=
  OTwoGen.range_le_ggOTwoPrime θ hθ (ggSu_top_le_closure_two hK hn)

theorem ggSu_ggOTwoPrime_range {G : Type} [Group G]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n) (θ : Su K 2 f n →* G) :
    ggOTwoPrime θ.range = θ.range :=
  le_antisymm (ggOTwoPrime_le _) (ggSu_range_le_ggOTwoPrime hK hn θ le_rfl)

theorem ggSu_range_le_of_odd_index {G : Type} [Group G]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (θ : Su K 2 f n →* G) (N : Subgroup G) [N.Normal] (hN : Odd N.index) :
    θ.range ≤ N := by
  have htwo : ggOTwoPrime (⊤ : Subgroup G) ≤ N := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro x ⟨_, k, hk⟩
    exact CFSG.ComponentClassification.AS76b.mem_of_two_element_of_odd_index hN hk
  exact (ggSu_range_le_ggOTwoPrime hK hn θ le_top).trans htwo

theorem ggSu_range_le_of_odd_relIndex {G : Type} [Group G]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (θ : Su K 2 f n →* G) (C N : Subgroup G)
    [(N.subgroupOf C).Normal] (hθ : θ.range ≤ C) (hN : Odd (N.relIndex C)) :
    θ.range ≤ N := by
  let θC : Su K 2 f n →* C := θ.codRestrict C (fun x => hθ ⟨x, rfl⟩)
  have hle : θC.range ≤ N.subgroupOf C :=
    ggSu_range_le_of_odd_index hK hn θC (N.subgroupOf C) hN
  rintro _ ⟨x, rfl⟩
  exact hle ⟨x, rfl⟩

end CFSG.StandardType
