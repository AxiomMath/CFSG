module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SL2
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Alt5

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSimpleGroup_of_isAlt_five (h : IsAlt 5 X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

omit [Finite X] in
theorem exists_ne_of_isAlt_five (h : IsAlt 5 X) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨e⟩ := h
  by_contra hcon
  push Not at hcon
  apply A5.G3.not_solvable_alt5
  apply Group.isSolvable_of_comm
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hcon _ _

theorem solvableRadical_eq_bot_of_isAlt_five (h : IsAlt 5 X) :
    CFSG.solvableRadical X = ⊥ := by
  have hs := isSimpleGroup_of_isAlt_five h
  obtain ⟨a, b, hab⟩ := exists_ne_of_isAlt_five h
  let e : X ⧸ (⊥ : Subgroup X) ≃* X := QuotientGroup.quotientBot
  have hs' : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) := e.isSimpleGroup
  have hna' : ∃ a b : X ⧸ (⊥ : Subgroup X), a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact A314.solvableRadical_eq_of_simple (V := ⊥)
    (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _) hs' hna'

theorem isAlt_modRadical_of_isAlt_five (h : IsAlt 5 X) :
    IsAlt 5 (X ⧸ CFSG.solvableRadical X) := by
  have e : X ⧸ CFSG.solvableRadical X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (solvableRadical_eq_bot_of_isAlt_five h)).trans
      QuotientGroup.quotientBot
  exact IsAlt.of_mulEquiv e.symm h

theorem pCore_eq_bot_of_isAlt_five (h : IsAlt 5 X) : CFSG.pCore 2 X = ⊥ := by
  have hs := isSimpleGroup_of_isAlt_five h
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h0 | h1
  · exact h0
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
    rw [h1] at hp
    obtain ⟨k, hk⟩ := (hp.of_equiv Subgroup.topEquiv).exists_card_eq
    rw [A314.card_isAlt_five h] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end Alt5

theorem commutator_eq_of_isAlt_five {Y : Type} [Group Y] {B : Subgroup Y} (hB : IsAlt 5 ↥B) :
    ⁅B, B⁆ = B := by
  have hs := isSimpleGroup_of_isAlt_five hB
  obtain ⟨a, b, hab⟩ := exists_ne_of_isAlt_five hB
  have h1 : commutator ↥B = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥B) with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator ↥B := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  have h2 : (commutator ↥B).map B.subtype = ⁅B, B⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isQuasisimple_modO2_of_isAlt_five {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}
    (hB : IsAlt 5 ↥B) : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
  have hs := isSimpleGroup_of_isAlt_five hB
  have hq : CFSG.IsQuasisimple ↥B :=
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup
      (exists_ne_of_isAlt_five hB)
  have e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* ↥B :=
    (QuotientGroup.quotientMulEquivOfEq (pCore_eq_bot_of_isAlt_five hB)).trans
      QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem card_isElemAbelianOfRank {V : Type*} [Group V] {p n : ℕ}
    (h : IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod p) ≃ (Fin n → ZMod p)), Nat.card_pi]
  simp [Nat.card_zmod]

theorem eleven_le_of_mod {p : ℕ} (hp : p.Prime) (h5 : p ^ 2 % 5 = 1)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  have h2 := hp.two_le
  interval_cases p <;> simp_all

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
