module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.GF2Type.Aschbacher1977.SymplecticExclusions
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
public import Mathlib.GroupTheory.Coset.Card
public import Certificates.Certificate2012
public import CFSG.LargeExtraspecial.Types
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_mulAut_of_lieModel_psp_two_three
    {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSp 2 3 1) :
    Nat.card (MulAut X) = 51840 :=
  (CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42
    (CFSG.GF2Type.Aschbacher1977.lieModel_PSU_four_two_of_PSp_two_three h)).1

theorem card_quotient_J (h : Tim79a.ParrottHyp z) :
    Nat.card (↥(H z) ⧸ (J z).subgroupOf (H z)) = 51840 := by
  obtain ⟨h1, h2, hcomm, h4, hnorm, X, instX, hLM, hiso⟩ := h
  obtain ⟨e⟩ := hiso
  calc Nat.card (↥(H z) ⧸ (J z).subgroupOf (H z))
      = Nat.card (MulAut X) := Nat.card_congr e.toEquiv
    _ = 51840 := card_mulAut_of_lieModel_psp_two_three hLM

theorem card_H (h : Tim79a.ParrottHyp z) :
    Nat.card (H z) = 2 ^ 10 * 51840 := by
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((J z).subgroupOf (H z))
  rw [card_quotient_J h] at hq
  have hJcard : Nat.card ↥((J z).subgroupOf (H z)) = Nat.card (J z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv
  rw [hJcard, card_J h] at hq
  rw [hq]
  ring

theorem card_H_eq (h : Tim79a.ParrottHyp z) :
    Nat.card (H z) = 2 ^ 17 * 3 ^ 4 * 5 := by
  rw [card_H h]
  norm_num

end CFSG.RankThree.GF2n.Parrott
