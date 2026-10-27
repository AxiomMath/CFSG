module

public import CFSG.Quasithin.EmptyFaithful.S151U1
public import CFSG.Quasithin.Background.F918P1
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem dichotomy_of_isL1519 {Mc Z₁ L : Subgroup G} (hL : IsL1519 Mc Z₁ L)
    (hodd : oddCoreIn (g1_1516 Z₁) = ⊥) : CharTwo L ∨ IsComponentOf L (g1_1516 Z₁) := by
  have hcomp : L ∈ cComp (g1_1516 Z₁) := hL.comp
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hcomp)
  rcases s151u_centralizer_pCore_le_or_quasisimple hperf hL.quasi
      (fun p hp hp2 => pCore_odd_eq_bot_of_mem_cComp hcomp hodd hp hp2) with h | h
  · left
    have h' : Subgroup.centralizer (CFSG.Open.pCore 2 ↥L : Set ↥L) ≤ CFSG.Open.pCore 2 ↥L := by
      exact h
    exact (centralizer_pCore_le_iff_pCoreOf 2 L).1 h'
  · right
    exact ⟨le_of_mem_cComp hcomp, subnormal_of_mem_cComp hcomp,
      Group.isPerfect_def.mp h.1, h.2.1⟩

theorem not_centralizer_pCore_le_of_quasisimple {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) :
    ¬ Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X := by
  intro hc
  have hnt : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (CFSG.pCore 2 X) with
    h | h
  ·
    have hcomm : ∀ x y : X, x * y = y * x := by
      intro x y
      have hxC : x ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) :=
        Subgroup.mem_centralizer_iff.mpr fun p hp => (Subgroup.mem_center_iff.mp (h hp) x).symm
      exact (Subgroup.mem_center_iff.mp (h (hc hxC)) y).symm
    have hab : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    have hx' : x ∈ commutator X := by
      rw [hperf]
      exact Subgroup.mem_top x
    rw [hab] at hx'
    exact hx (Subgroup.mem_bot.mp hx')
  ·
    have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 X) := CFSG.pCore_isNilpotent
    rw [h] at hnil
    have hX : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := X))
    have hsolv : Group.IsSolvable X := inferInstance
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial X
    rw [hperf] at hlt
    exact lt_irrefl _ hlt

theorem not_charTwo_of_isComponentOf {X L : Subgroup G} (hc : CharTwo L)
    (hcomp : IsComponentOf L X) : False := by
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hcomp.2.2
  have h' : Subgroup.centralizer (CFSG.Open.pCore 2 ↥L : Set ↥L) ≤ CFSG.Open.pCore 2 ↥L :=
    (centralizer_pCore_le_iff_pCoreOf 2 L).2 hc
  exact not_centralizer_pCore_le_of_quasisimple hq (by exact h')

private theorem pCore_two_eq_bot_of_simple {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) (hs : IsSimpleGroup X) : CFSG.pCore 2 X = ⊥ := by
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

private noncomputable def quotEquivOfSimple {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) (hs : IsSimpleGroup X) : X ≃* X ⧸ CFSG.pCore 2 X :=
  (QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_bot_of_simple hperf hs).symm)

private theorem bender_quot_of_perfect {L : Type} [Group L] [Finite L] (hperf : commutator L = ⊤)
    (h : IsBender1516 L) : IsBender1516 (L ⧸ CFSG.pCore 2 L) := by
  rcases h with ⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩
  · have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity L 2 2 n h).2
    exact Or.inl ⟨n, hn, isPSL_congr (quotEquivOfSimple hperf hs) h⟩
  · have hs := (CFSG.LieType.Simplicity.fam_2b2_simplicity L 2 e h).2
    exact Or.inr (Or.inl ⟨e, isSz_congr (quotEquivOfSimple hperf hs) h⟩)
  · have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity L 3 2 n h).2
    exact Or.inr (Or.inr ⟨n, hn, isPSU_congr (quotEquivOfSimple hperf hs) h⟩)

theorem noBorel_of_h21 {Mc Z₁ L : Subgroup G} (hL : IsL1519 Mc Z₁ L)
    (h21 : Lemma15121Concl Mc Z₁ L) (hcomp : IsComponentOf L (g1_1516 Z₁)) :
    ¬ Case15120ThreeA Mc Z₁ L ∧ ¬ Case15120ThreeB Mc Z₁ L := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have hperf : commutator ↥L = ⊤ := hq.1
  have h21' := h21 hL.comp
  have hnot : ¬ L ≤ mZ1516 Mc Z₁ := hL.not_le
  refine ⟨?_, ?_⟩
  · rintro ⟨hA, -⟩
    refine hnot (h21' (Or.inr ⟨hcomp, ?_⟩))
    rcases hA with hb | hs
    · exact Or.inl (bender_quot_of_perfect hperf hb)
    · exact Or.inl (Or.inr (Or.inl ⟨3, hs⟩))
  · rintro ⟨hB, -⟩
    refine hnot (h21' (Or.inr ⟨hcomp, ?_⟩))
    rcases hB with ⟨n, -, h⟩ | ⟨n, -, h⟩ | h
    · have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 3 2 n h).2
      exact Or.inr (Or.inl ⟨n, isPSL_congr (quotEquivOfSimple hperf hs) h⟩)
    · have hs :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp ↥L 2 2 n h
      exact Or.inr (Or.inr ⟨n, isPSp4_congr (quotEquivOfSimple hperf hs) h⟩)
    · exact Or.inr (Or.inl ⟨2, h⟩)

end CFSG.Quasithin.E9
