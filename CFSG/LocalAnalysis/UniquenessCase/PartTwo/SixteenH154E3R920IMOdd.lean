module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMOddRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMOddQuot
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

variable {G : Type} [Group G] [Finite G]

private theorem r920imo_card_map_mk_of_inf_eq_bot {Q : Type} [Group Q] (N : Subgroup Q)
    [N.Normal] (A : Subgroup Q) (h : A ⊓ N = ⊥) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  let f : ↥A →* Q ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hrange : f.range = A.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map_of_mem _ a.2
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hker : f.ker = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxN : (x : Q) ∈ N := by
        have hx1 : f x = 1 := hx
        exact (QuotientGroup.eq_one_iff (x : Q)).mp hx1
      have hxA : (x : Q) ∈ A ⊓ N := ⟨x.2, hxN⟩
      rw [h] at hxA
      exact Subtype.ext (Subgroup.mem_bot.mp hxA)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact map_one f
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Subgroup.card_bot, one_mul] at hcard
  exact hcard

private theorem r920imo_card_sl2_five : Nat.card (SL(2, ZMod 5)) = 120 := by
  rw [Matrix.card_SL_field]
  norm_num [Fin.prod_univ_two]

theorem false_of_odd_chief_factor (hK46 : UCK.K46Semireg) {L Z U W : Subgroup G} {r : ℕ}
    (hKK : CFSG.Open.IsKGroup ↥L) (hE9 : ¬ HasE9 ↥L) (hLperf : ⁅L, L⁆ = L) (hZL : Z ≤ L)
    (hZ3 : Nat.card Z = 3)
    (hLgen : ∀ B : Subgroup G, B ≤ L → L ≤ normalizer (B : Set G) → Z ≤ B → B = L)
    (hr : r.Prime) (hr2 : r ≠ 2) (hUW : IsChiefFactorUnder r L U W)
    (hfix : ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hfixA : ∀ (p : ℕ) (A : Subgroup G), p.Prime → p ≠ 2 → A ≤ L → Nat.card A = p →
      ∀ u ∈ U, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hA7 : ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = 7) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, _, _, _, _, ρ, hirr, hfixV⟩ := exists_rep_of_chief_factor hUW
  have hperf : commutator ↥L = ⊤ := by
    haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact Group.IsPerfect.commutator_eq_top
  have hD3 : Nat.card (Z.subgroupOf L) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  have hfixZ : fixV ρ (Z.subgroupOf L) = ⊥ :=
    hfixV (Z.subgroupOf L) fun u hu hc =>
      hfix u hu fun x hx => hc ⟨x, hZL hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
  have hfixA' : ∀ (p : ℕ) (A : Subgroup ↥L), p.Prime → p ≠ 2 → Nat.card A = p →
      fixV ρ A = ⊥ := by
    intro p A hp hp2 hcard
    refine hfixV A fun u hu hc => hfixA p (A.map L.subtype) hp hp2 (Subgroup.map_subtype_le A)
      ?_ u hu ?_
    · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
    · rintro a ⟨a', ha', rfl⟩
      exact hc a' ha'
  have hcases := quot_ker_semireg hK46 hr2 hKK hE9 hperf hD3
    (CFSG.LocalAnalysis.UniquenessCase.UC22.F09.normalClosure_subgroupOf_eq_top hZL hLgen)
    ρ hirr hfixZ hfixA'
  obtain ⟨A₀, hA₀L, hA₀card⟩ := hA7
  let A' : Subgroup ↥L := A₀.subgroupOf L
  have hA'card : Nat.card A' = 7 := by
    rw [← hA₀card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀L).toEquiv
  have hfixA'' : fixV ρ A' = ⊥ :=
    hfixV A' fun u hu hc =>
      hfixA 7 A₀ Nat.prime_seven (by norm_num) hA₀L hA₀card u hu fun a ha =>
        hc ⟨a, hA₀L ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
  have hbot_top : (⊥ : Submodule (ZMod r) V) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvbot : v ∈ (⊥ : Submodule (ZMod r) V) := h.symm ▸ Submodule.mem_top
    exact hv (by simpa using hvbot)
  have hker_bot : A' ⊓ ρ.ker = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(A' ⊓ ρ.ker) ∣ 7 := by
      rw [← hA'card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcard7 : Nat.card ↥(A' ⊓ ρ.ker) = 7 := by
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
      · exact h
    have hEq : A' ⊓ ρ.ker = A' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA'card]; exact le_of_eq hcard7.symm)
    have hle : A' ≤ ρ.ker := hEq ▸ inf_le_right
    have htop : fixV ρ A' = ⊤ := by
      ext v
      simp only [Submodule.mem_top, iff_true]
      intro a ha
      rw [hle ha, Module.End.one_apply]
    exact hbot_top (by rw [← hfixA'', htop])
  have h7dvd : 7 ∣ Nat.card (↥L ⧸ ρ.ker) := by
    have hcard_map : Nat.card (A'.map (QuotientGroup.mk' ρ.ker)) = 7 := by
      rw [r920imo_card_map_mk_of_inf_eq_bot ρ.ker A' hker_bot, hA'card]
    rw [← hcard_map]
    exact Subgroup.card_subgroup_dvd_card _
  rcases hcases with hSL2 | hExt
  · obtain ⟨e⟩ := hSL2
    have hcard : Nat.card (↥L ⧸ ρ.ker) = 120 := by
      rw [Nat.card_congr e.toEquiv, r920imo_card_sl2_five]
    have : 7 ∣ 120 := hcard ▸ h7dvd
    norm_num at this
  · obtain ⟨V₁, hV₁normal, hQ8, hA5⟩ := hExt
    haveI : V₁.Normal := hV₁normal
    have hVcard : Nat.card ↥V₁ = 32 := by
      have h := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hQ8).1
      simpa using h
    obtain ⟨eA5⟩ := hA5
    have hA5card : Nat.card ((↥L ⧸ ρ.ker) ⧸ V₁) = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hcard : Nat.card (↥L ⧸ ρ.ker) = 1920 := by
      have h := Subgroup.card_mul_index (H := V₁)
      rw [hVcard, Subgroup.index_eq_card, hA5card] at h
      norm_num at h
      exact h.symm
    have : 7 ∣ 1920 := hcard ▸ h7dvd
    norm_num at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
