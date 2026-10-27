module

public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Mult
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.Quasithin.H13.NQCatLieThompsonSp4
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms

theorem center_eq_bot_of_isPSp4_quot
    {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 2 ≤ n) (hq : CFSG.IsQuasisimple Q)
    (h : IsPSp4 2 n (Q ⧸ Subgroup.center Q)) : Subgroup.center Q = ⊥ := by
  have hq' : CFSG.Open.IsQuasisimple Q :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff Q).2.2.1).mp hq
  exact (CFSG.Quasithin.H13.Ch4.sp4MultTrivial_of
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds) Q n hn hq' h

theorem isPSp4_of_center_eq_bot {Q : Type} [Group Q] {n : ℕ}
    (hZ : Subgroup.center Q = ⊥) (h : IsPSp4 2 n (Q ⧸ Subgroup.center Q)) :
    IsPSp4 2 n Q :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) h

theorem isCyclic_outer_of_isPSp4 {X : Type} [Group X] {n : ℕ} (h : IsPSp4 2 n X) :
    IsCyclic (Outer X) := by
  change CFSG.Open.StatedClassicalModel X .PSp 2 2 n at h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI := hKfield
  letI := hKfinite
  have hKchar : CharP K 2 := CFSG.SectionRank.charP_two_of_card hKcard
  letI := hKchar
  haveI : IsCyclic (Outer (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K))) :=
    CFSG.Quasithin.H13.NQCat.LieThompson.Sp4.isCyclic_outer_projSp (F := K)
  exact GL83.I713.isCyclic_outer_congr e

theorem center_eq_bot_of_isG2_quot
    {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hq : CFSG.IsQuasisimple Q)
    (hZ : Odd (Nat.card (Subgroup.center Q)))
    (h : IsG2 2 n (Q ⧸ Subgroup.center Q)) : Subgroup.center Q = ⊥ := by
  haveI : Group.IsPerfect Q := hq.1
  have h0 := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial h
    (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le (by rw [QuotientGroup.ker_mk']; exact hZ)
  rwa [QuotientGroup.ker_mk'] at h0

theorem isG2_of_center_eq_bot {Q : Type} [Group Q] {n : ℕ}
    (hZ : Subgroup.center Q = ⊥) (h : IsG2 2 n (Q ⧸ Subgroup.center Q)) :
    IsG2 2 n Q :=
  CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h

theorem isCyclic_outer_of_isG2
    {X : Type} [Group X] {n : ℕ} (h : IsG2 2 n X) : IsCyclic (Outer X) :=
  GL83.I713.isCyclic_outer_of_untwistedModel_G2 Nat.prime_two h.1.2.1 h.1.2.2.2 h.2

end CFSG.Quasithin
