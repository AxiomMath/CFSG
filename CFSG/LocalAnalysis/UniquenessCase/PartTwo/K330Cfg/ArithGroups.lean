module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Arith
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)

theorem excl_alt_six {J : Type} [Group J] [Finite J] (e : IsAlt J 6) : Excl J := by
  obtain ⟨φ⟩ := e
  have hcard : Nat.card J = 360 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  exact Or.inr (Or.inl (arithExcl_of_card 3 2 5 (by rw [hcard]; norm_num) arith_five))

theorem excl_alt_seven {J : Type} [Group J] [Finite J] (e : IsAlt J 7) : Excl J := by
  obtain ⟨φ⟩ := e
  have hcard : Nat.card J = 2520 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  exact Or.inr (Or.inl (arithExcl_of_card 3 2 35 (by rw [hcard]; norm_num) arith_thirty_five))

theorem excl_M11 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .M11) : Excl J := by
  obtain ⟨φ⟩ := e
  have hcard : Nat.card J = 7920 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11
  exact Or.inr (Or.inl (arithExcl_of_card 4 2 55 (by rw [hcard]; norm_num) arith_fifty_five))

theorem excl_M22 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .M22) : Excl J := by
  obtain ⟨φ⟩ := e
  have hcard : Nat.card J = 443520 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  exact Or.inr (Or.inl (arithExcl_of_card 7 2 385 (by rw [hcard]; norm_num) arith_385))

theorem excl_HS {J : Type} [Group J] [Finite J]
    (e : IsSpor J .HS) : Excl J := by
  obtain ⟨φ⟩ := e
  have hcard : Nat.card J = 44352000 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.HS.card_HS
  exact Or.inr (Or.inl (arithExcl_of_card 9 2 9625 (by rw [hcard]; norm_num) arith_9625))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
