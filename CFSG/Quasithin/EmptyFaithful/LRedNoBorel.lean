module

public import CFSG.Quasithin.EmptyFaithful.S151XD
public import CFSG.Quasithin.Background.F918P1
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Aux

private theorem lred_pCore_two_eq_bot {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hs : IsSimpleGroup X) : CFSG.pCore 2 X = ⊥ := by
  have : Nontrivial X := hs.toNontrivial
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 X) := CFSG.pCore_isNilpotent
    rw [h] at hnil
    have hX : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := X))
    have hsolv : Group.IsSolvable X := inferInstance
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial X
    rw [hperf] at hlt
    exact lt_irrefl _ hlt

private noncomputable def lredQuotEquiv {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hs : IsSimpleGroup X) : X ≃* X ⧸ CFSG.pCore 2 X :=
  (QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (lred_pCore_two_eq_bot hperf hs).symm)

end Aux

private theorem lred_bender_quot {L : Type} [Group L] [Finite L] (hperf : commutator L = ⊤)
    (h : IsBender1516 L) : IsBender1516 (L ⧸ CFSG.pCore 2 L) := by
  rcases h with ⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩
  · have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity L 2 2 n h).2
    exact Or.inl ⟨n, hn, isPSL_congr (lredQuotEquiv hperf hs) h⟩
  · have hs := (CFSG.LieType.Simplicity.fam_2b2_simplicity L 2 e h).2
    exact Or.inr (Or.inl ⟨e, isSz_congr (lredQuotEquiv hperf hs) h⟩)
  · have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity L 3 2 n h).2
    exact Or.inr (Or.inr ⟨n, hn, isPSU_congr (lredQuotEquiv hperf hs) h⟩)

theorem input15122NoBorel_proved : Input15122NoBorel := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L c hcomp
  have hq : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have hperf : commutator ↥L = ⊤ := hq.1
  have h21 := c.h21 c.hL.comp
  have hnot : ¬ L ≤ mZ1516 Mc Z₁ := c.hL.not_le
  refine ⟨?_, ?_⟩
  · rintro ⟨hA, -⟩
    refine hnot (h21 (Or.inr ⟨hcomp, ?_⟩))
    rcases hA with hb | hs
    · exact Or.inl (lred_bender_quot hperf hb)
    · exact Or.inl (Or.inr (Or.inl ⟨3, hs⟩))
  · rintro ⟨hB, -⟩
    refine hnot (h21 (Or.inr ⟨hcomp, ?_⟩))
    rcases hB with ⟨n, -, h⟩ | ⟨n, -, h⟩ | h
    · have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 3 2 n h).2
      exact Or.inr (Or.inl ⟨n, isPSL_congr (lredQuotEquiv hperf hs) h⟩)
    · have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp ↥L 2 2 n h
      exact Or.inr (Or.inr ⟨n, isPSp4_congr (lredQuotEquiv hperf hs) h⟩)
    · exact Or.inr (Or.inl ⟨2, h⟩)

end CFSG.Quasithin
