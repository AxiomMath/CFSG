module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.F4LowRankShapes
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LowRankModelsPart1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

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

section B2
variable (E : Subfield Ω) [CharP ↥E 2] [Finite ↥E]

theorem b2RE_injective :
    Function.Injective (b2RE E) :=
  (adjointGroup Tag.F4 ↥E).subtype_injective.comp
    (CFSG.StandardType.F4ExplicitPos.B2Finite.b2LeviHom_injective (E := ↥E))

theorem b2RE_range :
    (b2RE E).range = rootSpan Tag.F4 ↥E CFSG.SeitzReduction.F4Pilot.b2LeviRoots := by
  rw [b2RE, MonoidHom.range_comp, B2Finite.map_range_b2LeviHom_modGL]

theorem b2LeviRoots_isRoot :
    ∀ α ∈ CFSG.SeitzReduction.F4Pilot.b2LeviRoots, IsRoot Tag.F4 α := by
  intro α hα
  rw [CFSG.SeitzReduction.F4Pilot.b2LeviRoots] at hα
  exact hα.1

noncomputable def b2Model
    (v : WeylGroup Tag.F4) {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) '' CFSG.SeitzReduction.F4Pilot.b2LeviRoots) :
    ↥(CFSG.Open.StatedSp 2 ↥E) ≃* rootSpanOver Ω E Ψ :=
  commonModel E (b2RE E) (b2RE_injective E) (b2RE_range E) b2LeviRoots_isRoot v hΨ

end B2

section Shape

variable (E : Subfield Ω) [CharP ↥E 2] [Finite ↥E]

theorem lowRankShape_models
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} {v : WeylGroup Tag.F4}
    (hshape :
      (∃ j : Fin Tag.F4.rank, Ψ = (fun α => v • α) ''
        ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      Ψ = (fun α => v • α) ''
        parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4LongSupport ∨
      Ψ = (fun α => v • α) ''
        parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4ShortSupport ∨
      Ψ = (fun α => v • α) '' CFSG.SeitzReduction.F4Pilot.b2LeviRoots) :
    Nonempty (SL2 ↥E ≃* rootSpanOver Ω E Ψ) ∨
    Nonempty (SL(3, ↥E) ≃* rootSpanOver Ω E Ψ) ∨
    Nonempty (↥(CFSG.Open.StatedSp 2 ↥E) ≃* rootSpanOver Ω E Ψ) := by
  rcases hshape with ⟨j, hj⟩ | hlong | hshort | hb2
  · exact Or.inl ⟨rankOneModel E j v hj⟩
  · exact Or.inr (Or.inl ⟨longA2Model E v hlong⟩)
  · exact Or.inr (Or.inl ⟨shortA2Model E v hshort⟩)
  · exact Or.inr (Or.inr ⟨b2Model E v hb2⟩)

end Shape

theorem f4_rank_le_two_component_models
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p : ℕ} (hp : p.Prime) (hpΩ : (p : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ} (hap : rootDiagUnit Tag.F4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : compRank (componentRoots (rootCharHom a) i) ≤ 2)
    (E : Subfield Ω) [CharP ↥E 2] [Finite ↥E] :
    Nonempty (SL2 ↥E ≃* rootSpanOver Ω E (componentRoots (rootCharHom a) i)) ∨
    Nonempty (SL(3, ↥E) ≃* rootSpanOver Ω E (componentRoots (rootCharHom a) i)) ∨
    Nonempty (↥(CFSG.Open.StatedSp 2 ↥E) ≃*
      rootSpanOver Ω E (componentRoots (rootCharHom a) i)) := by
  obtain ⟨v, hshape⟩ :=
    f4_rank_le_two_component_shape (Ω := Ω) hp hpΩ hap i h2
  exact lowRankShape_models E hshape

theorem frobeniusFixed_component_models
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (a : Fin Tag.F4.rank → Ωˣ)
    (i : KernelComponent (rootCharHom a))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : rootDiagUnit Tag.F4 a ^ p = 1) :
    compRank (componentRoots (rootCharHom a) i) ≤ 2 →
      ∀ (k : ℕ) (_hk : k ≠ 0)
        (_hk4 : 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k)),
      let E := TauCeti.frobeniusFixedSubfield Ω 2 k
      let H0 := rootSpanOver Ω E (componentRoots (rootCharHom a) i)
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) E ≃* H0) ∨
      Nonempty (Matrix.SpecialLinearGroup (Fin 3) E ≃* H0) ∨
      Nonempty (↥(CFSG.Open.StatedSp 2 E) ≃* H0) := by
  have hpΩ : (p : Ω) ≠ 0 := by
    intro h
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff Ω 2 p).mp h
    rcases (Nat.dvd_prime hp).mp hdvd with h21 | h2p
    · norm_num at h21
    · exact hp2 h2p.symm
  intro h2 k hk _hk4
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  exact f4_rank_le_two_component_models (Ω := Ω) hp hpΩ hap i h2
    (TauCeti.frobeniusFixedSubfield Ω 2 k)

end CFSG.StandardType.F4ExplicitPos.LowRankModels

end

end
