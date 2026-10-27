module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.EmbedLoc

open Equiv CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_two_element_normalizer {X T : Subgroup G} (hT : IsSylowTwoOf T X) {g : G}
    (hgX : g ∈ X) (hgN : g ∈ Subgroup.normalizer (T : Set G)) (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 (T.subgroupOf X) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let Q : Sylow 2 ↥X := hT2.toSylow hT.2.2
  have hQ : (Q : Subgroup ↥X) = T.subgroupOf X := rfl
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨g, hgX⟩ : ↥X)) := by
    obtain ⟨k, hk⟩ := hg
    have hdvd : orderOf (⟨g, hgX⟩ : ↥X) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hN : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.normalizer ((Q : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hgN h
  have hmem : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.zpowers (⟨g, hgX⟩ : ↥X) ⊓ (Q : Subgroup ↥X) := by
    rw [← IsPGroup.inf_normalizer_sylow hP Q]
    exact ⟨Subgroup.mem_zpowers _, hN⟩
  have h1 : (⟨g, hgX⟩ : ↥X) ∈ T.subgroupOf X := hmem.2
  exact Subgroup.mem_subgroupOf.mp h1

end CFSG.Quasithin.EmbedLoc
