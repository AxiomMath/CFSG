module

public import CFSG.Sporadic.Fi24.Fischer
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi22.InvCent
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Sporadic.Schreier.Fi24

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint.NativeSporadic (Fi24prime)

noncomputable def autEquivR :
    MulAut Fi24prime ≃* Sporadic.Fi24.R :=
  (Sporadic.Fi24.rEquivAut Fischer.polarFacts Fischer.hyperovalFacts
    (Sporadic.Fi22.fi22Facts Fischer.polarFacts Fischer.hyperovalFacts)
    (Sporadic.Fi23.fi23Facts (Sporadic.Fi22.fi22Facts Fischer.polarFacts Fischer.hyperovalFacts))
    Sporadic.Fi22.card_fixed_involution_D Sporadic.Fi22.eq_of_commute_centralizer
    Sporadic.Fi24.edgeSwap_a Sporadic.Fi23.d1_mem_localClass Sporadic.Fi23.involution_cover).symm

theorem card_mulAut_fi24prime :
    Nat.card (MulAut Fi24prime) = 2 * Nat.card Fi24prime := by
  rw [Nat.card_congr autEquivR.toEquiv, Sporadic.Fi24.card_R, Sporadic.Fi24.card_Fi24prime]

theorem center_fi24prime : Subgroup.center Fi24prime = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hJ : Sporadic.Fi24.fi24EquivJ z ∈ Subgroup.center Sporadic.Fi24.J := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := congrArg Sporadic.Fi24.fi24EquivJ (hz (Sporadic.Fi24.fi24EquivJ.symm g))
    simpa using this
  rw [Sporadic.Fi24.center_J, Subgroup.mem_bot] at hJ
  exact Sporadic.Fi24.fi24EquivJ.injective (hJ.trans (map_one _).symm)

theorem card_inner_of_center_eq_bot (G : Type) [Group G] (h : Subgroup.center G = ⊥) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner G) = Nat.card G := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun α : MulAut G => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rw [h, Subgroup.mem_bot] at hc
    exact hc
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem card_outer_eq_two_of (G : Type) [Group G] (hpos : 0 < Nat.card G)
    (h : Subgroup.center G = ⊥) (hc : Nat.card (MulAut G) = 2 * Nat.card G) :
    Nat.card (Outer G) = 2 := by
  have h1 := (CFSG.ComponentClassification.OuterAutomorphisms.inner G).card_mul_index
  rw [card_inner_of_center_eq_bot G h, hc, Subgroup.index_eq_card] at h1
  have h2 : Nat.card G * Nat.card (Outer G) = Nat.card G * 2 := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem card_outer_fi24prime :
    Nat.card (Outer Fi24prime) = 2 :=
  card_outer_eq_two_of Fi24prime (by rw [Sporadic.Fi24.card_Fi24prime]; norm_num)
    center_fi24prime card_mulAut_fi24prime

theorem fi24prime_outer_solvable :
    IsCyclic (Outer Fi24prime) ∧ Group.IsSolvable (Outer Fi24prime) := by
  have hc : IsCyclic (Outer Fi24prime) := isCyclic_of_prime_card card_outer_fi24prime
  refine ⟨hc, Group.isSolvable_of_comm fun a b => ?_⟩
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

end CFSG.Sporadic.Schreier.Fi24
