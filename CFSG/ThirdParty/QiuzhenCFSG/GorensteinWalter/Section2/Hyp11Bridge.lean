module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection

namespace CFSG
end CFSG
open CFSG

/-!
# Bridge from the Section 2 centralizer setup to Bender--Glauberman Hypothesis 1.1

The character-theoretic Theorem B is stated for `BenderGlauberman.Hyp11`.
The Gorenstein--Walter Section 2 setup stores the same Sylow subgroup,
rotation subgroup, central involution, and centralizer, but not the two
reflection generators used by the character paper.  This module constructs
those generators from the cyclic index-two subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A `CentralizerSetup` satisfying the two recalled Section 2 preamble facts
supplies Bender--Glauberman Hypothesis 1.1.

Choose a generator `a` of the cyclic subgroup `S0` and an element `s` of
`S \ S0`.  Both `s` and `s * a` are reflections, hence involutions, and their
product is `a`; therefore they generate `S0` in the form required by
`BenderGlauberman.Hyp11`. -/
public theorem exists_benderGlaubermanHyp11_of_centralizerSetup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hone : ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y)
    (hHSU : (c.S : Subgroup G) ⊔ c.U = c.H) :
    ∃ bg : BenderGlauberman.Hyp11 G, bg.H = c.H := by
  classical
  have hS0neS : c.S0 ≠ (c.S : Subgroup G) := by
    intro hEq
    have hcardEq : Nat.card c.S = Nat.card c.S0 := by rw [hEq]
    have hindex := c.S_index_two
    rw [hcardEq] at hindex
    have hpos : 0 < Nat.card c.S0 := Nat.card_pos
    omega
  have hnotle : ¬ (c.S : Subgroup G) ≤ c.S0 := by
    intro hle
    exact hS0neS (le_antisymm c.S0_le_S hle)
  obtain ⟨s, hsS, hsnot⟩ := Set.not_subset.mp hnotle
  obtain ⟨a, ha⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top c.S0).mp c.S0_cyclic
  have haS0 : a ∈ c.S0 := by
    rw [← ha]
    exact Subgroup.mem_zpowers a
  have haS : a ∈ (c.S : Subgroup G) := c.S0_le_S haS0
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c ⟨hsS, hsnot⟩
  let t1 : G := s
  let t2 : G := s * a
  have ht2S : t2 ∈ (c.S : Subgroup G) := by
    exact (c.S : Subgroup G).mul_mem hsS haS
  have ht2not : t2 ∉ c.S0 := by
    intro ht2
    have hs0 : t2 * a⁻¹ ∈ c.S0 :=
      c.S0.mul_mem ht2 (c.S0.inv_mem haS0)
    apply hsnot
    simpa [t2, mul_assoc] using hs0
  have ht2Inv : IsInvolution t2 :=
    centralizerSetup_reflection_isInvolution c ⟨ht2S, ht2not⟩
  have htprod : t1 * t2 = a := by
    have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
    calc
      t1 * t2 = s * (s * a) := rfl
      _ = (s * s) * a := (mul_assoc s s a).symm
      _ = a := by rw [hss]; simp
  refine ⟨{
    S := c.S
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := c.dihedralEquiv
    S0 := c.S0
    S0_le_S := c.S0_le_S
    S0_cyclic := c.S0_cyclic
    S_index_two := c.S_index_two
    t := c.t
    t_mem_S0 := c.t_mem_S0
    t_involution := c.t_involution
    one_involution_class := hone
    s := s
    s_mem_S := hsS
    s_not_mem_S0 := hsnot
    s_involution := hsInv
    t1 := t1
    t2 := t2
    t1_mem_S := hsS
    t1_not_mem_S0 := hsnot
    t1_involution := hsInv
    t2_mem_S := ht2S
    t2_not_mem_S0 := ht2not
    t2_involution := ht2Inv
    S0_eq_zpowers := by rw [htprod]; exact ha.symm
    H := c.H
    H_eq_centralizer := c.H_eq_centralizer
    H_eq_US := by simpa [CentralizerSetup.U, sup_comm] using hHSU
  }, rfl⟩

/-- Full-information variant of `exists_benderGlaubermanHyp11_of_centralizerSetup`:
the constructed `Hyp11` additionally inherits the Sylow subgroup, the rotation
subgroup, and the central involution from the `CentralizerSetup`. -/
public theorem exists_benderGlaubermanHyp11_of_centralizerSetup_full
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hone : ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y)
    (hHSU : (c.S : Subgroup G) ⊔ c.U = c.H) :
    ∃ bg : BenderGlauberman.Hyp11 G,
      bg.H = c.H ∧ (bg.S : Subgroup G) = (c.S : Subgroup G) ∧
        bg.S0 = c.S0 ∧ bg.t = c.t := by
  classical
  have hS0neS : c.S0 ≠ (c.S : Subgroup G) := by
    intro hEq
    have hcardEq : Nat.card c.S = Nat.card c.S0 := by rw [hEq]
    have hindex := c.S_index_two
    rw [hcardEq] at hindex
    have hpos : 0 < Nat.card c.S0 := Nat.card_pos
    omega
  have hnotle : ¬ (c.S : Subgroup G) ≤ c.S0 := by
    intro hle
    exact hS0neS (le_antisymm c.S0_le_S hle)
  obtain ⟨s, hsS, hsnot⟩ := Set.not_subset.mp hnotle
  obtain ⟨a, ha⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top c.S0).mp c.S0_cyclic
  have haS0 : a ∈ c.S0 := by
    rw [← ha]
    exact Subgroup.mem_zpowers a
  have haS : a ∈ (c.S : Subgroup G) := c.S0_le_S haS0
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c ⟨hsS, hsnot⟩
  let t1 : G := s
  let t2 : G := s * a
  have ht2S : t2 ∈ (c.S : Subgroup G) := by
    exact (c.S : Subgroup G).mul_mem hsS haS
  have ht2not : t2 ∉ c.S0 := by
    intro ht2
    have hs0 : t2 * a⁻¹ ∈ c.S0 :=
      c.S0.mul_mem ht2 (c.S0.inv_mem haS0)
    apply hsnot
    simpa [t2, mul_assoc] using hs0
  have ht2Inv : IsInvolution t2 :=
    centralizerSetup_reflection_isInvolution c ⟨ht2S, ht2not⟩
  have htprod : t1 * t2 = a := by
    have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
    calc
      t1 * t2 = s * (s * a) := rfl
      _ = (s * s) * a := (mul_assoc s s a).symm
      _ = a := by rw [hss]; simp
  refine ⟨{
    S := c.S
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := c.dihedralEquiv
    S0 := c.S0
    S0_le_S := c.S0_le_S
    S0_cyclic := c.S0_cyclic
    S_index_two := c.S_index_two
    t := c.t
    t_mem_S0 := c.t_mem_S0
    t_involution := c.t_involution
    one_involution_class := hone
    s := s
    s_mem_S := hsS
    s_not_mem_S0 := hsnot
    s_involution := hsInv
    t1 := t1
    t2 := t2
    t1_mem_S := hsS
    t1_not_mem_S0 := hsnot
    t1_involution := hsInv
    t2_mem_S := ht2S
    t2_not_mem_S0 := ht2not
    t2_involution := ht2Inv
    S0_eq_zpowers := by rw [htprod]; exact ha.symm
    H := c.H
    H_eq_centralizer := c.H_eq_centralizer
    H_eq_US := by simpa [CentralizerSetup.U, sup_comm] using hHSU
  }, by simp⟩

end CFSG.GorensteinWalter
