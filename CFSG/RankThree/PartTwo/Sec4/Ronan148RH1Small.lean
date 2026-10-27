module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.KFacts.KP4
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section J1


theorem noCfgS427_j1 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .J1) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J1 ≃* Spor .J1 := b
  have hcard : Nat.card S = 175560 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans CFSG.Sporadic.J1.card_J1
  refine ⟨noCfgS427_of_inner (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e spor_j1.1) fun s hs => ?_,
    noONS427_of_card (by rw [hcard]; norm_num)⟩
  refine good427_of_central_of_not_nine_dvd (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) hs fun h9 => ?_
  have h := h9.trans (Subgroup.card_subgroup_dvd_card _)
  rw [hcard] at h
  norm_num at h

end J1

section M22


theorem noCfgS427_m22 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .M22) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M22 ≃* Spor .M22 := b
  have hcard : Nat.card S = 443520 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  refine ⟨noCfgS427_of_inner (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e spor_m22.1) fun s hs => ?_,
    noONS427_of_card (by rw [hcard]; norm_num)⟩
  exact good427_of_card_dvd (M := 36)
    (dvd_of_eq (KFacts.KP4.m22_centralizer_facts_of_orderOf ⟨e.trans b'.symm⟩ hs).1)
    (by norm_num)

end M22

section McL


theorem noCfgS427_mcl :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .McL) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  haveI : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv S e.toEquiv
  have hcard : Nat.card S = 898128000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL
  have hgood : ∀ y : Blueprint.NativeSporadic.McL, orderOf y = 3 →
      Good427 (Subgroup.centralizer ({y} : Set Blueprint.NativeSporadic.McL)) := fun y hy =>
    good427_of_pConstrained (CFSG.HardMathSupport.Dickson.I271.mcl_pConstrained_three
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL y hy)
  refine ⟨noCfgS427_of_model (G' := Blueprint.NativeSporadic.McL) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_of_le_two Sec4.card_outer_McL))
    hgood, noONS427_of_card (by rw [hcard]; norm_num)⟩

end McL

section Rows



section J1Row


theorem rowOf427_j1
    : RowOf427 (Spor .J1) := rowOf427_of_noCfgS noCfgS427_j1

end J1Row

section M22Row


theorem rowOf427_m22
    : RowOf427 (Spor .M22) := rowOf427_of_noCfgS noCfgS427_m22

end M22Row

section McLRow


theorem rowOf427_mcl
    : RowOf427 (Spor .McL) :=
  rowOf427_spor (s := .McL) CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv noCfgS427_mcl

end McLRow

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
