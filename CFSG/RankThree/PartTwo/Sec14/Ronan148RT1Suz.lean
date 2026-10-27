module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowL3
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence inner)
open scoped commutatorElement

section IndexTwo

variable {G : Type} [Group G]

theorem mem_of_pow_three_eq_one_of_index_dvd_two {H : Subgroup G} (hH : H.index ∣ 2) {g : G}
    (hg : g ^ 3 = 1) : g ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hH with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top g
  · have hsq : g ^ 2 ∈ H := Subgroup.sq_mem_of_index_two h2 g
    have hg' : g = (g ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ', hg]
    rw [hg']
    exact H.inv_mem hsq

theorem commutator_mem_of_index_two {H : Subgroup G} (hH : H.index = 2) (x y : G) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hH,
    Subgroup.mul_mem_iff_of_index_two hH, Subgroup.mul_mem_iff_of_index_two hH,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem perfect_le_of_index_dvd_two {H P : Subgroup G} (hH : H.index ∣ 2)
    (hP : Group.IsPerfect P) : P ≤ H := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hH with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · exact le_of_perfect_commutator_mem hP fun x _ y _ => commutator_mem_of_index_two h2 x y

end IndexTwo

theorem row143_of_oPrimeCore {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S) (hout : Nat.card (Outer S) ∣ 2)
    (hO : ∀ s : S, orderOf s = 3 →
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({s} : Set S)) = ⊥) : Row143 S := by
  have hidx : (inner S).index ∣ 2 := hout
  have hinner : ∀ φ : MulAut S, φ ∈ inner S → ∃ g : S, φ = MulAut.conj g := by
    intro φ hφ
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hφ
    exact ⟨g, hg.symm⟩
  refine row143_of_inner_kgroup hS hnc (fun P _ hPp _ => perfect_le_of_index_dvd_two hidx hPp)
    ?_
  intro β hβ Y hYfix hYsub _ _ hY3
  obtain ⟨g, rfl⟩ := hinner β (mem_of_pow_three_eq_one_of_index_dvd_two hidx hβ)
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = MulAut.conj (1 : S) := by
      rw [map_pow, map_one]
      exact hβ
    exact conj_injective_of_isSimpleGroup hS hnc h1
  by_cases hg1 : g = 1
  ·
    subst hg1
    have hA : Sec4.autFix (MulAut.conj (1 : S)) = ⊤ := by
      ext x
      simp [Sec4.mem_autFix]
    have hsimp : IsSimpleGroup ↥(Sec4.autFix (MulAut.conj (1 : S))) :=
      ((MulEquiv.subgroupCongr hA).trans Subgroup.topEquiv).isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hYsub with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYfix hy))
    · rw [Subgroup.subgroupOf_eq_top] at h
      exfalso
      apply hY3
      have hYtop : Y = ⊤ := eq_top_iff.mpr (by rw [← hA]; exact h)
      rw [hYtop, Subgroup.card_top]
      exact h3
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    rw [RonanK429H.autFix_conj] at hYfix hYsub
    set C := Subgroup.centralizer ({g} : Set S) with hC
    have hcard : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYfix).toEquiv
    have hle : Y.subgroupOf C ≤ CFSG.pPrimeCore 3 ↥C :=
      Sec4.le_pPrimeCore_of_isSubnormal hYsub (by rw [hcard]; exact hY3)
    rw [hO g hgo, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hle hy (hYfix hy))

section Suz


theorem rowOf143_spor_suz : RowOf143 (Sec4.Spor .Suz) := by
  intro S _ _ hS hnc ⟨e⟩ h3
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Suz ≃* Sec4.Spor .Suz := b
  have e' : S ≃* Blueprint.NativeSporadic.Carrier .Suz := e.trans b'.symm
  have hout : Nat.card (Outer S) ∣ 2 := by
    rw [Nat.card_congr (equivalence e').toEquiv, CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
  haveI := hS
  have hOP := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOPrimeHolds_Suz_three S ⟨e'⟩
  refine row143_of_oPrimeCore hS hnc h3 hout fun s hs => ?_
  have h := hOP s hs
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h

end Suz

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
