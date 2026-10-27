module

public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4Plane
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4Conj
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.CTP

theorem reeF4_cenGen_eq_top_three {m : ℕ}
    (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (E₁ : Subgroup (ReeTag.F4.reeGamma K m))
    (hE : CFSG.Open.IsElemAbelian 3 E₁) (hc : Nat.card E₁ = 9) :
    Subgroup.closure {k : ReeTag.F4.reeGamma K m | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K m) := Subtype.finite
  obtain ⟨E, hEΓ, hEp, hEc, hD⟩ := q1_phi2_plane_three hm hK Nat.prime_three rfl
  have hE₀ := reeF4c_closure_cenGen_subgroupOf (ReeTag.F4.reeGamma K m) E hEΓ hD
  set E₀ := E.subgroupOf (ReeTag.F4.reeGamma K m) with hE₀def
  have hE₀c : Nat.card E₀ = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv]
    exact hEc
  have hE₀p : ∀ x ∈ E₀, x ^ 3 = 1 := fun x hx => Subtype.ext (by simpa using hEp x hx)
  have hE₀ab : CFSG.Open.IsElemAbelian 3 E₀ :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hE₀c, hE₀p⟩
  obtain ⟨g, hg⟩ := reeGamma_planes_conj_three m hK E₀ E₁ hE₀ab
    (by simpa using hE₀c) hE hc
  rw [← hg]
  change Subgroup.closure (cenGen (cj E₀ g)) = ⊤
  rw [closure_cenGen_cj, hE₀, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

end CFSG.RankThree.PartTwo.Sec19
