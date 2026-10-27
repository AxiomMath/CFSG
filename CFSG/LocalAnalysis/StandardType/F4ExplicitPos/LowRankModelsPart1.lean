module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankOneTorusPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Finite

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.LowRankModels

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

open CFSG.RankThree.PartOne.KE

open CFSG.StandardType.F4ExplicitPos.BaseChange (bcGL bcGL_injective)

open CFSG.StandardType.F4ExplicitPos.FiniteAction (rootSpanOver)

open CFSG.StandardType.F4ExplicitPos.B2Finite (rootSpanOver_eq_map_rootSpan)

open CFSG.LieType.AlgebraicGroups (rootCharHom)

open CFSG.HardMathSupport.Timmesfeld.LangTorus (compRank)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped MatrixGroups Matrix

variable {Ω : Type} [Field Ω]

variable {M : Type} [Group M]

variable {S Ψ : Set (Fin Tag.F4.rank → ℤ)}

variable {v : WeylGroup Tag.F4}

noncomputable def kappaE
    (E : Subfield Ω) (rE : M →* ModGL Tag.F4 E) (v : WeylGroup Tag.F4) :
    M →* ModGL Tag.F4 Ω :=
  (bcGL E.subtype).comp
    ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) E v)).toMonoidHom.comp rE)

theorem kappaE_injective
    (E : Subfield Ω) (rE : M →* ModGL Tag.F4 E)
    (hrE : Function.Injective rE) (v : WeylGroup Tag.F4) :
    Function.Injective (kappaE E rE v) := by
  have hconj : Function.Injective
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) E v)).toMonoidHom :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) E v)).injective
  exact (bcGL_injective E.subtype E.subtype.injective).comp (hconj.comp hrE)

theorem kappaE_range
    (E : Subfield Ω) (rE : M →* ModGL Tag.F4 E)
    (hR : rE.range = rootSpan Tag.F4 E S) (hS : ∀ α ∈ S, IsRoot Tag.F4 α)
    (v : WeylGroup Tag.F4) (hΨ : Ψ = (fun α => v • α) '' S) :
    (kappaE E rE v).range = rootSpanOver Ω E Ψ := by
  have h : (kappaE E rE v).range
      = ((rootSpan Tag.F4 E Ψ).map (bcGL E.subtype)) := by
    rw [kappaE, MonoidHom.range_comp, MonoidHom.range_comp, hR, map_conj_rootSpan v hS,
      ← hΨ]
  rw [h, ← CFSG.StandardType.F4ExplicitPos.B2Finite.rootSpanOver_eq_map_rootSpan E Ψ]

noncomputable def commonModel
    (E : Subfield Ω) (rE : M →* ModGL Tag.F4 E)
    (hrE : Function.Injective rE)
    (hR : rE.range = rootSpan Tag.F4 E S) (hS : ∀ α ∈ S, IsRoot Tag.F4 α)
    (v : WeylGroup Tag.F4) (hΨ : Ψ = (fun α => v • α) '' S) :
    M ≃* rootSpanOver Ω E Ψ :=
  (MonoidHom.ofInjective (kappaE_injective E rE hrE v)).trans
    (MulEquiv.subgroupCongr (kappaE_range E rE hR hS v hΨ))

section RankOne

variable (E : Subfield Ω) [CharP ↥E 2]

noncomputable def rankOneRE
    (j : Fin Tag.F4.rank) :
    SL2 ↥E →* ModGL Tag.F4 ↥E :=
  (adjointGroup Tag.F4 ↥E).subtype.comp
    (CFSG.StandardType.F4ExplicitPos.RankOneTorus.simpleRootMap (K := ↥E) j)

theorem rankOneRE_injective
    (j : Fin Tag.F4.rank) :
    Function.Injective (rankOneRE E j) :=
  (adjointGroup Tag.F4 ↥E).subtype_injective.comp
    (CFSG.StandardType.F4ExplicitPos.RankOneTorus.simpleRootMap_injective (K := ↥E) j)

theorem rootGroup_single_map_subtype
    (j : Fin Tag.F4.rank) :
    (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily Tag.F4) ↥E
        (Pi.single j 1)).map (adjointGroup Tag.F4 ↥E).subtype =
      rootSubgroup Tag.F4 ↥E (Pi.single j 1) := by
  rw [CFSG.StandardType.F4ExplicitPos.RankOneTorus.rootGroup_single_eq
      (F := rootOperatorFamily Tag.F4) (K := ↥E) j,
    ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
      (F := rootOperatorFamily Tag.F4) ↥E
      (CFSG.LieType.Chevalley.simpleRoot Tag.F4 j),
    Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr (rootSubgroup_le_adjointGroup (Pi.single j 1))

theorem rootGroup_neg_single_map_subtype
    (j : Fin Tag.F4.rank) :
    (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily Tag.F4) ↥E
        (-Pi.single j 1)).map (adjointGroup Tag.F4 ↥E).subtype =
      rootSubgroup Tag.F4 ↥E (-Pi.single j 1) := by
  rw [CFSG.StandardType.F4ExplicitPos.RankOneTorus.rootGroup_neg_single_eq
      (F := rootOperatorFamily Tag.F4) (K := ↥E) j,
    ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
      (F := rootOperatorFamily Tag.F4) ↥E
      (-CFSG.LieType.Chevalley.simpleRoot Tag.F4 j),
    Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr (rootSubgroup_le_adjointGroup (-Pi.single j 1))

theorem rankOneRE_range
    (j : Fin Tag.F4.rank) :
    (rankOneRE E j).range =
      rootSpan Tag.F4 ↥E ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
  rw [rankOneRE, MonoidHom.range_comp,
    CFSG.StandardType.F4ExplicitPos.RankOneTorus.simpleRootMap_range
      (F := rootOperatorFamily Tag.F4) (K := ↥E) j,
    CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
    rootGroup_single_map_subtype E j, rootGroup_neg_single_map_subtype E j,
    rootSpan, iSup_insert, iSup_singleton]

noncomputable def rankOneModel
    (j : Fin Tag.F4.rank) (v : WeylGroup Tag.F4)
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) ''
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) :
    SL2 ↥E ≃* rootSpanOver Ω E Ψ :=
  commonModel E (rankOneRE E j) (rankOneRE_injective E j) (rankOneRE_range E j)
    (fun α hα => by
      rcases hα with h | h
      · rw [h]; exact isRoot_single Tag.F4 j
      · rw [h]; exact isRoot_neg_single Tag.F4 j)
    v hΨ

end RankOne

section A2

variable (E : Subfield Ω)

theorem longA2RE_injective :
    Function.Injective
      (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_actual (K := ↥E)) :=
  CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_injective_actual (K := ↥E)

theorem longA2RE_range :
    (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_actual (K := ↥E)).range =
      rootSpan Tag.F4 ↥E
        (parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4LongSupport) := by
  rw [CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_range_actual,
    CFSG.StandardType.F4ExplicitPos.A2Actual.subsystemGroup_eq_rootSpan]

noncomputable def longA2Model
    (v : WeylGroup Tag.F4) {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) ''
      parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4LongSupport) :
    SL(3, ↥E) ≃* rootSpanOver Ω E Ψ :=
  commonModel E (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoLong_actual (K := ↥E))
    (longA2RE_injective E) (longA2RE_range E)
    (fun _ hα => hα.1) v hΨ

theorem shortA2RE_injective :
    Function.Injective
      (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_actual (K := ↥E)) :=
  CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_injective_actual (K := ↥E)

theorem shortA2RE_range :
    (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_actual (K := ↥E)).range =
      rootSpan Tag.F4 ↥E
        (parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4ShortSupport) := by
  rw [CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_range_actual,
    CFSG.StandardType.F4ExplicitPos.A2Actual.subsystemGroup_eq_rootSpan]

noncomputable def shortA2Model
    (v : WeylGroup Tag.F4) {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) ''
      parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4ShortSupport) :
    SL(3, ↥E) ≃* rootSpanOver Ω E Ψ :=
  commonModel E (CFSG.StandardType.F4ExplicitPos.A2Actual.f4rhoShort_actual (K := ↥E))
    (shortA2RE_injective E) (shortA2RE_range E)
    (fun _ hα => hα.1) v hΨ

end A2

section B2

variable (E : Subfield Ω) [CharP ↥E 2] [Finite ↥E]

noncomputable def b2RE :
    ↥(CFSG.Open.StatedSp 2 ↥E) →* ModGL Tag.F4 ↥E :=
  (adjointGroup Tag.F4 ↥E).subtype.comp (B2Finite.b2LeviHom (E := ↥E))

end B2
end CFSG.StandardType.F4ExplicitPos.LowRankModels
end

end
