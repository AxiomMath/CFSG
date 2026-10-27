module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Label
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalizeE7
public import CFSG.RankThree.PartOne.KE.CTCasesE7Sev
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxNine
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxEighteen
public import CFSG.RankThree.PartOne.KE.CTCasesE8Coxeter
public import CFSG.RankThree.PartOne.KE.CTCasesE8Explicit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley

namespace F4Nonsplit

@[expose] def GGNonsplitCoreNeOneAt (C : Type) [Group C] (p : ℕ) : Prop :=
  ∀ a b : C, a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 →
    ∀ X : Subgroup C, IsComponentOf X (Subgroup.centralizer {a}) → ¬ p ∣ Nat.card X →
      ∃ X' : Subgroup C, IsComponentOf X' (Subgroup.centralizer {b}) ∧ X ≤ X' ∧
        ¬ GGNbrClauseFiveMarking p a X'

theorem ggNonsplitCoreAt_of_neOne {C : Type} [Group C] [Finite C] (hQ : CFSG.IsQuasisimple C)
    {p : ℕ} (hpC : p ∣ Nat.card C) (h : GGNonsplitCoreNeOneAt C p) :
    ExcNonsplit.GGNonsplitCoreAt C p := by
  intro a b ha hb hab X hX hpX
  by_cases ha1 : a = 1
  · exfalso
    subst ha1
    have htop : Subgroup.centralizer ({1} : Set C) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (one_mem _))
    rw [htop] at hX
    have hQt : CFSG.IsQuasisimple ↥(⊤ : Subgroup C) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
    have hc : ⁅(⊤ : Subgroup C), ⊤⁆ = ⊤ :=
      CFSG.RankThree.Chevalley.commutator_eq_self_of_isPerfect hQt.1
    have hQ' : CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup C), ⊤⁆ : Subgroup C) := by
      rw [hc]
      exact hQt
    rw [eq_commutator_of_isComponentOf hQ' hX, hc, Subgroup.card_top] at hpX
    exact hpX hpC
  · exact h a b ha hb hab ha1 X hX hpX

theorem ggNonsplitCoreNeOneAt_of_cyclic {C : Type} [Group C] {p n₀ d : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartOne.KE.CyclicSylowConclusion' C p n₀ d) :
    GGNonsplitCoreNeOneAt C p := by
  intro a b ha _ _ ha1 X hX _
  obtain ⟨T, hT, -, -, -, -, -, hcent⟩ := h
  have hap : orderOf a = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one ha) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) ha1
    · exact h1
  obtain ⟨g, -, hg⟩ := hcent a hap
  exact absurd hX (not_isComponentOf_of_conj_centralizer_cyclic hT hg)

theorem seven_lt_of_dvd_phiSeven {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : 1 ≤ q) (hq1 : ¬ p ∣ q - 1) (h : (p : ℤ) ∣ (exhaustionPhi 7).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hp5 : p = 5 ∨ p = 7 := by
    have := hp.two_le
    interval_cases p <;> simp_all <;> norm_num at hp
  have e : (exhaustionPhi 7).eval (q : ℤ) =
      (q : ℤ) ^ 6 + (q : ℤ) ^ 5 + (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + (q : ℤ) + 1 := by
    simp [exhaustionPhi]
  rw [e] at h
  rcases hp5 with rfl | rfl
  · have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 h
    push_cast at h5
    generalize (q : ZMod 5) = x at h5
    revert x
    decide
  · have h7 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 h
    push_cast at h7
    have hx : (q : ZMod 7) = 1 := by
      generalize (q : ZMod 7) = x at h7
      revert x
      decide
    apply hq1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, hx, Nat.cast_one, sub_self]

theorem seven_lt_of_dvd_phiFourteen {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq1 : ¬ p ∣ q + 1) (h : (p : ℤ) ∣ (exhaustionPhi 14).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hp5 : p = 5 ∨ p = 7 := by
    have := hp.two_le
    interval_cases p <;> simp_all <;> norm_num at hp
  have e : (exhaustionPhi 14).eval (q : ℤ) =
      (q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    simp [exhaustionPhi]
  rw [e] at h
  rcases hp5 with rfl | rfl
  · have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 h
    push_cast at h5
    generalize (q : ZMod 5) = x at h5
    revert x
    decide
  · have h7 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 h
    push_cast at h7
    have hx : (q : ZMod 7) + 1 = 0 := by
      generalize (q : ZMod 7) = x at h7
      revert x
      decide
    apply hq1
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact hx

end F4Nonsplit

section E7

@[expose] def GGE7NonsplitCoreRestInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 → p ∣ Nat.card ↥(adjointGroup .E7 K) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K : ℤ) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K : ℤ) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 18).eval (Nat.card K : ℤ) →
      F4Nonsplit.GGNonsplitCoreNeOneAt ↥(adjointGroup .E7 K) p

theorem ggExcNonsplitCoreInput_E7_of_rest (h : GGE7NonsplitCoreRestInput) :
    GGExcNonsplitCoreInput .E7 := by
  intro K _ _ _ p hp hp2 hq1 hq2
  have hp3 := ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  have hQ := CFSG.SeitzReduction.E8Pilot.isQuasisimple_adjointGroup_E7 K
  by_cases hC : p ∣ Nat.card ↥(adjointGroup .E7 K)
  swap
  · exact ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3 hC
      (fun X hX lab hl hc hM => F4Nonsplit.not_halfSplit_of_isComponentOf_top hQ hp3 hC hX hl hc hM)
  refine F4Nonsplit.ggNonsplitCoreAt_of_neOne hQ hC ?_
  have hmain := CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  by_cases h7 : (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E7_seven_cyclic_sylow hmain K hp
        (F4Nonsplit.seven_lt_of_dvd_phiSeven hp hp2 hp3 hq hq1 h7) h7).2
  by_cases h9 : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E7_nine_cyclic_sylow hmain K hp hp3' h9).2.2
  by_cases h14 : (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E7_fourteen_cyclic_sylow hmain K hp
        (F4Nonsplit.seven_lt_of_dvd_phiFourteen hp hp2 hp3 hq2 h14) h14).2
  by_cases h18 : (p : ℤ) ∣ (exhaustionPhi 18).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E7_eighteen_cyclic_sylow hmain K hp hp3' h18).2.2
  exact h K p hp hp2 hq1 hq2 hC h7 h9 h14 h18

end E7

section E8

@[expose] def GGE8NonsplitCoreRestInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 → p ∣ Nat.card ↥(adjointGroup .E8 K) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 15).eval (Nat.card K : ℤ) →
    (5 < p → ¬ (p : ℤ) ∣ (exhaustionPhi 20).eval (Nat.card K : ℤ)) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 24).eval (Nat.card K : ℤ) →
    ¬ (p : ℤ) ∣ (exhaustionPhi 30).eval (Nat.card K : ℤ) →
      F4Nonsplit.GGNonsplitCoreNeOneAt ↥(adjointGroup .E8 K) p

theorem ggExcNonsplitCoreInput_E8_of_rest (h : GGE8NonsplitCoreRestInput) :
    GGExcNonsplitCoreInput .E8 := by
  intro K _ _ _ p hp hp2 hq1 hq2
  have hp3 := ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  have hQ := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K
  by_cases hC : p ∣ Nat.card ↥(adjointGroup .E8 K)
  swap
  · exact ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3 hC
      (fun X hX lab hl hc hM => F4Nonsplit.not_halfSplit_of_isComponentOf_top hQ hp3 hC hX hl hc hM)
  refine F4Nonsplit.ggNonsplitCoreAt_of_neOne hQ hC ?_
  have hmain := CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers
  by_cases h15 : (p : ℤ) ∣ (exhaustionPhi 15).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E8_fifteen_cyclic_sylow hmain K hp hp3' h15).2.2
  by_cases h20 : 5 < p ∧ (p : ℤ) ∣ (exhaustionPhi 20).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E8_twenty_cyclic_sylow hmain K hp h20.1 h20.2).2.2
  by_cases h24 : (p : ℤ) ∣ (exhaustionPhi 24).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E8_twentyfour_cyclic_sylow hmain K hp hp3' h24).2.2
  by_cases h30 : (p : ℤ) ∣ (exhaustionPhi 30).eval (Nat.card K : ℤ)
  · exact F4Nonsplit.ggNonsplitCoreNeOneAt_of_cyclic hp
      (CFSG.RankThree.PartOne.KE.E8_thirty_cyclic_sylow hmain K hp hp3' h30).2.2
  exact h K p hp hp2 hq1 hq2 hC h15 (fun h5 h' => h20 ⟨h5, h'⟩) h24 h30

end E8

end CFSG.StandardType
