module

public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.R3c6Psl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S152SFam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def NotLieCharTwoAlt7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 7)) → ¬ Lemma115LieCharTwo X

@[expose] def NotLieCharTwoSporadic : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → ∀ s : TauCeti.SporadicName,
    IsLemma115SporadicName s → Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* NativeSporadic.Carrier s) →
      ¬ Lemma115LieCharTwo (K ⧸ Subgroup.center K)

section TypeAnalysis


variable {G : Type} [Group G] [Finite G]

theorem btProps_or_l32_of_caseA (hBQ : BigQBorelCentralizerTrivial) {L : Subgroup G}
    (hq : Group.IsPerfect ↥L) (hs : IsSimpleGroup ↥L) (hlieL : Lemma115LieCharTwo ↥L)
    (hF2 : ¬ IsF2RankTwoGroup ↥L) (hA6 : ¬ Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    BTProps (↥L ⧸ Subgroup.center ↥L) ∨ (Subgroup.center ↥L = ⊥ ∧ IsPSL 3 2 1 ↥L) := by
  have hcen := CFSG.Quasithin.R3c3.center_eq_bot_of_simple_perfect hs hq
  rcases lemma115LieCharTwo_cases hlieL hF2 hA6 with h | h
  · left
    exact BTProps.of_mulEquiv (CFSG.Quasithin.R3c3.quotCenterEquivOfSimple hs hq).symm
      (BTProps.of_isBigQLieGroup hBQ h)
  · exact Or.inr ⟨hcen, h⟩

theorem typeAnalysis (hBQ : BigQBorelCentralizerTrivial) (hD : NotLieCharTwoAlt7)
    (hF : NotLieCharTwoSporadic) {I L : Subgroup G} {z : G} (hcomp : IsComponentIn L I)
    (hcases : Lemma115Cases L z) (hlie : Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L))
    (hnC : ¬ Lemma115CaseC L z)
    (hnA : ¬ (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ Lemma115CaseA L z))
    (hF2 : ¬ (IsF2RankTwoGroup ↥L ∧ Lemma115CaseA L z)) :
    InducesInner z L ∧
      (BTProps (↥L ⧸ Subgroup.center ↥L) ∨ (Subgroup.center ↥L = ⊥ ∧ IsPSL 3 2 1 ↥L)) := by
  have hqs : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hcomp
  have hperf : Group.IsPerfect ↥L := hqs.1
  have viaA : Lemma115CaseA L z → InducesInner z L ∧
      (BTProps (↥L ⧸ Subgroup.center ↥L) ∨ (Subgroup.center ↥L = ⊥ ∧ IsPSL 3 2 1 ↥L)) :=
    fun hA => ⟨hA.2.2, btProps_or_l32_of_caseA hBQ hperf hA.1 hA.2.1 (fun h => hF2 ⟨h, hA⟩)
      (fun h => hnA ⟨h, hA⟩)⟩
  rcases hcases with hA | hB | hC | hD' | hE | hF'
  · exact viaA hA
  · obtain ⟨-, hZO, hmod, hinn⟩ := hB
    refine ⟨hinn, Or.inl ?_⟩
    have hBig : IsBigQLieGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases hmod with h | h
      · exact ⟨2, le_rfl, Or.inr (Or.inl h)⟩
      · exact ⟨2, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    exact BTProps.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO).symm
      (BTProps.of_isBigQLieGroup hBQ hBig)
  · exact (hnC hC).elim
  · obtain ⟨φ, σ, -⟩ := hD'
    exact (hD _ ⟨φ⟩ hlie).elim
  · obtain ⟨hmodel, hinn⟩ := hE
    have hsE : IsSimpleGroup ↥L := by
      rcases hmodel with h | ⟨p, hp, h⟩
      · exact (CFSG.Quasithin.R3c6.psl3Data h).2.1
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 h).2
    have hlieL : Lemma115LieCharTwo ↥L :=
      Lemma115LieCharTwo.of_mulEquiv (CFSG.Quasithin.R3c3.quotCenterEquivOfSimple hsE hperf).symm hlie
    exact viaA ⟨hsE, hlieL, hinn⟩
  · obtain ⟨⟨s, hs, he⟩, -⟩ := hF'
    exact (hF ↥L hqs s hs he hlie).elim

end TypeAnalysis

end CFSG.Quasithin
