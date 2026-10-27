module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtA7Norm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.H13.Lem1227Lt

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open CFSG.Assembly.LowTwoRank CFSG.Quasithin

namespace A7

theorem eq_of_normal_simple {X : Type*} [Group X] {B M : Subgroup X} (hBM : B ≤ M)
    [IsSimpleGroup ↥M] (hN : M ≤ Subgroup.normalizer (B : Set X)) (hbot : B ≠ ⊥) : B = M := by
  have hn : (B.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBM).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf M) with h | h
  · exfalso
    have : B ⊓ M = ⊥ := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    rw [inf_of_le_left hBM] at this
    exact hbot this
  · exact le_antisymm hBM (Subgroup.subgroupOf_eq_top.1 h)

theorem classify_B
    {B : Subgroup ↥A7s} (hperf : ⁅B, B⁆ = B) (hbot : B ≠ ⊥)
    (htop : B ≠ ⊤) (hN : T7 ≤ Subgroup.normalizer (B : Set ↥A7s)) :
    B = rng5 ∨ (∃ i, (i = 8 ∨ i = 9) ∧ B.map A7s.subtype = Z i) ∨ B = rng6 := by
  have hA7 : IsSimpleGroup ↥A7s := alternatingGroup.isSimpleGroup (by simp)
  have hMN : B ⊔ T7 ≤ Subgroup.normalizer (B : Set ↥A7s) := sup_le Subgroup.le_normalizer hN
  have hMne : B ⊔ T7 ≠ ⊤ := by
    intro h
    have hn : B.Normal := ⟨fun n hn g => by
      have := hMN (h ▸ Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.1 this n).1 hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h0 | h1
    · exact hbot h0
    · exact htop h1
  have hBM : B ≤ B ⊔ T7 := le_sup_left
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T7) := by
    intro hs
    have : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hBM)
        (Subgroup.inclusion_injective hBM)
    have hp : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
    have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).2 hbot
    exact Group.IsPerfect.not_isSolvable ↥B ‹_›
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ B ⊔ T7)
  have hcardM : Nat.card ↥(B ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  interval_cases i
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcardM]; decide)) hMns
  ·
    left
    have := alt5_simple
    have hle : rng5 ≤ B ⊔ T7 := by
      intro k hk
      obtain ⟨h4, h5⟩ := (mem_rng5 k).mp hk
      exact (mem_of_map_eq hMi k).mpr
        ((mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp k.2)).mpr ⟨Or.inl h4, Or.inr h5⟩)
    have hperf5 : ⁅rng5, rng5⁆ = rng5 := perfect_of_equiv_simple alt5_nonabelian rng5Equiv
    have hBr : B ≤ rng5 :=
      (le_perfectCore_of_perfect hBM hperf).trans
        ((perfectCore_le_commutator (B ⊔ T7)).trans (commutator_le_rng5 hMi))
    have : IsSimpleGroup ↥rng5 := rng5Equiv.isSimpleGroup
    exact eq_of_normal_simple hBr (hle.trans hMN) hbot
  ·
    right; left
    have e : ↥(B ⊔ T7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      ((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z8Equiv.symm)
    have : IsSimpleGroup ↥(B ⊔ T7) := by
      have := slThree_isSimple
      exact e.isSimpleGroup
    have hBeq : B = B ⊔ T7 := eq_of_normal_simple hBM hMN hbot
    exact ⟨8, Or.inl rfl, by rw [hBeq]; exact hMi⟩
  ·
    right; left
    have e : ↥(B ⊔ T7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
      ((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z9Equiv.symm)
    have : IsSimpleGroup ↥(B ⊔ T7) := by
      have := slThree_isSimple
      exact e.isSimpleGroup
    have hBeq : B = B ⊔ T7 := eq_of_normal_simple hBM hMN hbot
    exact ⟨9, Or.inr rfl, by rw [hBeq]; exact hMi⟩
  ·
    right; right
    have hM6 : B ⊔ T7 = rng6 := eq_rng6 hMi
    have : IsSimpleGroup ↥(B ⊔ T7) := by
      have := alt6_simple
      exact (MulEquiv.subgroupCongr hM6).trans rng6Equiv |>.isSimpleGroup
    have hBeq : B = B ⊔ T7 := eq_of_normal_simple hBM hMN hbot
    rw [hBeq, hM6]
  · exfalso
    apply hMne
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, card_A7s]
    decide

theorem sigma_mem_Z {B : Subgroup ↥A7s} {i : ℕ} (hi : i = 8 ∨ i = 9)
    (hBi : B.map A7s.subtype = Z i) {σ : P7} (hσD : ∀ x, x ∈ D7 ↔ σ * x * σ⁻¹ ∈ D7)
    (hσB : ∀ b ∈ B, σ * (b : P7) * σ⁻¹ ∈ B.map A7s.subtype) : σ ∈ Z i := by
  obtain ⟨hcases, -, -⟩ := norm_D7 hσD
  have hZ : ∀ z, z ∈ Z i → σ * z * σ⁻¹ ∈ Z i := by
    intro z hz
    rw [← hBi] at hz ⊢
    obtain ⟨b, hb, rfl⟩ := hz
    exact hσB b hb
  rcases hcases with hd | ⟨d, hd, rfl⟩
  · rcases hi with rfl | rfl
    · exact D7_le_Z8 hd
    · exact D7_le_Z9 hd
  · exfalso
    rcases hi with rfl | rfl
    · exact not_normalizes_Z8 hd hZ
    · exact not_normalizes_Z9 hd hZ

end A7

end CFSG.Quasithin.H13.Lem1227Lt
