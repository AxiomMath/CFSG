module

public import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraicRestriction
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameD
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RhoTw
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameO

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Open CFSG.StandardType
open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_exists_f)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (commutator_adjointGroup_E6_eq_top commutator_adjointGroup_E7_eq_top
    commutator_adjointGroup_E8_eq_top)
open scoped commutatorElement

attribute [local instance] ZMod.algebra algebraicClosure.isAlgClosure IsAlgClosure.isAlgClosed

theorem famTrivial_transport
    {τ : Tag} {L0 L : Type} [Field L0] [IsAlgClosed L0] [Field L] [IsAlgClosed L]
    (j : L0 →+* L) {p q : ℕ} (S0 : LangSetup τ L0 p) (S : LangSetup τ L q)
    (hΓ : S0.Γ.map (baseChangeGL j) = S.Γ)
    {t : StatedLieTag} {f : ℕ}
    (hLie : LieModel (S0.Γ ⧸ Subgroup.center S0.Γ) t 0 2 f)
    (hq : CFSG.Open.IsQuasisimple ↥S0.Γ) :
    LieModel (S.Γ ⧸ Subgroup.center S.Γ) t 0 2 f ∧
      CFSG.Open.IsQuasisimple ↥S.Γ := by
  let φ : S0.Γ ≃* S.Γ :=
    (Subgroup.equivMapOfInjective S0.Γ (baseChangeGL j) (baseChangeGL_injective j)).trans
      (MulEquiv.subgroupCongr hΓ)
  exact ⟨LieModel.quotient_center_of_mulEquiv φ hLie,
    CFSG.Open.IsQuasisimple.of_mulEquiv φ.symm hq⟩

theorem famTrivial_Γ_data_twE6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup .E6 L p)
    (hAlg : S.IsAlgebraic)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ f : ℕ, 2 ^ f = S.D.q ∧
      LieModel (S.Γ ⧸ Subgroup.center S.Γ) .twistedE6 0 2 f ∧
        CFSG.Open.IsQuasisimple ↥S.Γ := by
  obtain ⟨f, hf1, hqf⟩ := ssTw_exists_f S (ℓ := 2)
  obtain ⟨K, hKf, hKfin, hKa, σ, e, hKq, hσ, he⟩ := S.descendsTwE6 hΦ hAlg
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK2 : Nat.card K = (2 ^ f) ^ 2 := by rw [hKq, hqf]
  have hσ' : ∀ c : K, σ c = c ^ 2 ^ f := by
    intro c
    have h1 : algebraMap K L (σ c) = algebraMap K L (c ^ 2 ^ f) := by
      rw [map_pow, ← hqf]
      exact hσ c
    exact (algebraMap K L).injective h1
  have hLie : LieModel S.Γ .twistedE6 0 2 f :=
    (CFSG.ComponentClassification.CatLeafProof.lieModel_twistedE6_of_mulEquiv
      hf1 hK2 σ hσ' e.symm).2
  have hZ : Subgroup.center ↥S.Γ = ⊥ := by
    have h1 : Subgroup.center ↥S.Γ =
        Subgroup.map e.toMonoidHom (Subgroup.center ↥(twistedE6RootGroup K σ)) :=
      (Subgroup.map_center_eq e).symm
    have hZ0 : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
      CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) σ.surjective
    rw [h1, hZ0]
    exact Subgroup.map_bot (f := e.toMonoidHom)
  have hLieZ : LieModel (S.Γ ⧸ Subgroup.center S.Γ) .twistedE6 0 2 f :=
    LieModel.quotient_center hZ hLie
  have hperfC0 : ⁅graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf1 K hK2 σ.toRingHom hσ').1
  haveI : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    Subgroup.isPerfect_iff.2 hperfC0
  haveI : Group.IsPerfect ↥S.Γ :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hCE : ChevalleyExceptionalModel (S.Γ ⧸ Subgroup.center S.Γ) .twistedE6 2 f :=
    ((LieModel.chevalleyExceptional_iff (t := .twistedE6) (by decide)).1 hLieZ).2
  have hsimple : IsSimpleGroup (S.Γ ⧸ Subgroup.center S.Γ) :=
    (CFSG.LieType.Simplicity.fam_2e6_simplicity _ 2 f hCE).2
  exact ⟨f, hqf.symm, hLieZ, ⟨Group.IsPerfect.commutator_eq_top, hsimple⟩⟩

theorem famTrivial_Γ_data_tag
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) :
    ∃ (t : StatedLieTag) (f : ℕ), 2 ^ f = S.D.q ∧
      LieModel (S.Γ ⧸ Subgroup.center S.Γ) t 0 2 f ∧
        CFSG.Open.IsQuasisimple ↥S.Γ ∧
          ((τ = .E6 ∧ t = .E6 ∧
              twistInner {γ | IsRoot τ γ} (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))) ∨
            (τ = .E6 ∧ t = .twistedE6 ∧
              ¬ twistInner {γ | IsRoot τ γ} (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))) ∨
            (τ = .E7 ∧ t = .E7) ∨ (τ = .E8 ∧ t = .E8)) := by
  obtain ⟨S0, hq0, hρ0, hAlg0, hn0, hg00, hΦ0, hmodel0, hΓ0, htorus0, hE0⟩ :=
    S.exists_algebraicRestriction
  obtain ⟨f, hf1, hqf⟩ := ssTw_exists_f S (ℓ := 2)
  have hq0f : S0.D.q = 2 ^ f := hq0.trans hqf
  haveI : CharP ↥(algebraicClosure (ZMod 2) L) 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) ↥(algebraicClosure (ZMod 2) L)) 2
      (by norm_num)
  obtain ⟨S5, hD5, hρ5⟩ :=
    CFSG.StandardType.LieCore.exists_langSetup_of_datum S0.D S0.ρ S0.frob S0.finite hf1 hq0f
  have hAlg5 : S5.IsAlgebraic := by
    unfold LangSetup.IsAlgebraic at hAlg0 ⊢
    rw [hD5]
    exact hAlg0
  have hΓ5 : S5.Γ.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) = S.Γ := by
    have h55 : S5.Γ = S0.Γ := by show S5.D.Γ = S0.D.Γ; rw [hD5]
    rw [h55, hΓ0]
  have hq5 : S5.D.q = S.D.q := (congrArg LangDatum.q hD5).trans hq0
  have hρ05 : S5.ρ = S.ρ := hρ5.trans hρ0
  have hρ05f : (S5.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) =
      (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) :=
    congrArg (fun e : Equiv.Perm (Fin τ.rank → ℤ) =>
      (e : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))) hρ05
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨Fr, hFr, P, hP, hΦeq⟩ := S5.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ5 : ∃ Fr : algebraicClosure (ZMod 2) L →+* algebraicClosure (ZMod 2) L,
          (∀ c, Fr c = c ^ S5.D.q) ∧ S5.D.Φ = Units.map (entrywiseHom Fr) :=
        ⟨Fr, hFr, by ext g; rw [hΦeq]; simp⟩
      obtain ⟨f', hf1', hqf'⟩ := ssTw_exists_f S5 (ℓ := 2)
      obtain ⟨K, hKf, hKfin, hKa, e, hKq, he⟩ :=
        S5.descends_of_untw 3 (Or.inl ⟨rfl, rfl⟩) (by norm_num) hΦ5 hAlg5
          (fun K' _ _ => commutator_adjointGroup_E6_eq_top K')
      letI : Field K := hKf
      letI : Finite K := hKfin
      have hk : Nat.card K = 2 ^ f' := hKq.trans hqf'
      have hadm : StatedLieAdmissible .E6 0 2 f' := ⟨Nat.prime_two, hf1', rfl⟩
      have hLie : LieModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E6 0 2 f' :=
        CFSG.ComponentClassification.CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup
          (by decide) hadm hk e.symm
      haveI : Group.IsPerfect ↥(adjointGroup .E6 K) := ⟨commutator_adjointGroup_E6_eq_top K⟩
      haveI : Group.IsPerfect ↥S5.Γ :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have hCE : ChevalleyExceptionalModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E6 2 f' :=
        ((LieModel.chevalleyExceptional_iff (t := .E6) (by decide)).1 hLie).2
      have hsimple : IsSimpleGroup (S5.Γ ⧸ Subgroup.center S5.Γ) :=
        (CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 f' hCE).2
      have hq : CFSG.Open.IsQuasisimple ↥S5.Γ :=
        ⟨Group.IsPerfect.commutator_eq_top, hsimple⟩
      have h2f' : 2 ^ f' = S.D.q := hqf'.symm.trans hq5
      obtain ⟨hLieS, hqS⟩ :=
        famTrivial_transport (algebraMap (algebraicClosure (ZMod 2) L) L) S5 S hΓ5 hLie hq
      obtain ⟨Fr0, hFr0, hΦ0⟩ := hΦ5
      obtain ⟨w, hw⟩ := S5.D.n_weyl
      have hρw : ∀ γ, IsRoot Tag.E6 γ → S5.ρ γ = w • γ := fun γ hγ =>
        S5.rho_eq_smul_of_frob hFr0 hΦ0 hw hγ
      have hsi : ∀ i : Fin Tag.E6.rank,
          rootReflection (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = simple Tag.E6 i := fun i => by
        rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
      have hsub : Set.range (simple Tag.E6) ⊆
          {s : WeylGroup Tag.E6 | ∃ γ ∈ {γ | IsRoot Tag.E6 γ}, s = rootReflection γ} := by
        rintro _ ⟨i, rfl⟩
        exact ⟨Pi.single i 1, isRoot_single Tag.E6 i, (hsi i).symm⟩
      have hmem : w ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
          ∃ γ ∈ {γ | IsRoot Tag.E6 γ}, s = rootReflection γ} :=
        Subgroup.closure_mono hsub (by rw [closure_range_simple]; exact Subgroup.mem_top w)
      have htwist5 : twistInner {γ | IsRoot Tag.E6 γ}
          (S5.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := ⟨w, hmem, hρw⟩
      have htwistS : twistInner {γ | IsRoot Tag.E6 γ}
          (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
        rw [← hρ05f]; exact htwist5
      exact ⟨.E6, f', h2f', hLieS, hqS, Or.inl ⟨rfl, rfl, htwistS⟩⟩
    · cases t
      · have hΦ5 : ∃ Fr : algebraicClosure (ZMod 2) L →+* algebraicClosure (ZMod 2) L,
            (∀ c, Fr c = c ^ S5.D.q) ∧
              S5.D.Φ = twistHom TwistTag.E6 (algebraicClosure (ZMod 2) L) Fr := by
          refine ⟨Fr, hFr, ?_⟩
          ext g
          rw [hΦeq]
          simp only [diagramAt, twistHom, MulAut.conj_apply, MonoidHom.comp_apply]
          rfl
        have hΦE : ∀ g, S5.D.Φ g = e6Diagram (algebraicClosure (ZMod 2) L) *
            Units.map (entrywiseHom Fr) g * (e6Diagram (algebraicClosure (ZMod 2) L))⁻¹ := by
          intro g
          rw [hΦeq g]
          rfl
        have hFrs : Function.Surjective Fr := fun y => by
          obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (n := S5.D.q)
            (by rw [hq5, hqf]; exact pow_pos (by norm_num) f)
          exact ⟨x, by rw [hFr, hx]⟩
        obtain ⟨w, hw⟩ := S5.D.n_weyl
        have hnot5 : ¬ twistInner {γ | IsRoot Tag.E6 γ}
            (S5.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
          have hnot := langSetup_rho_not_weyl_twE6 S5 (w := w)
            (w5F_rho_eq_smul S5 hΦE hw hFrs)
          intro htw
          obtain ⟨w', _, hw'⟩ := htw
          exact hnot ⟨w', hw'⟩
        have hnotS : ¬ twistInner {γ | IsRoot Tag.E6 γ}
            (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
          rw [← hρ05f]; exact hnot5
        obtain ⟨f', h2f, hLie, hq⟩ := famTrivial_Γ_data_twE6 S5 hAlg5 hΦ5
        have h2f' : 2 ^ f' = S.D.q := h2f.trans hq5
        obtain ⟨hLieS, hqS⟩ :=
          famTrivial_transport (algebraMap (algebraicClosure (ZMod 2) L) L) S5 S hΓ5 hLie hq
        exact ⟨.twistedE6, f', h2f', hLieS, hqS, Or.inr (Or.inl ⟨rfl, rfl, hnotS⟩)⟩
      · exact absurd ht (by decide)
  · have hΦ5 := S5.exists_frobenius_of_steinberg (τ := .E7) (by decide) (by decide)
    obtain ⟨f', hf1', hqf'⟩ := ssTw_exists_f S5 (ℓ := 2)
    obtain ⟨K, hKf, hKfin, hKa, e, hKq, he⟩ :=
      S5.descends_of_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by norm_num) hΦ5 hAlg5
        (fun K' _ _ => commutator_adjointGroup_E7_eq_top K')
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hk : Nat.card K = 2 ^ f' := hKq.trans hqf'
    have hadm : StatedLieAdmissible .E7 0 2 f' := ⟨Nat.prime_two, hf1', rfl⟩
    have hLie : LieModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E7 0 2 f' :=
      CFSG.ComponentClassification.CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup
        (by decide) hadm hk e.symm
    haveI : Group.IsPerfect ↥(adjointGroup .E7 K) := ⟨commutator_adjointGroup_E7_eq_top K⟩
    haveI : Group.IsPerfect ↥S5.Γ :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hCE : ChevalleyExceptionalModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E7 2 f' :=
      ((LieModel.chevalleyExceptional_iff (t := .E7) (by decide)).1 hLie).2
    have hsimple : IsSimpleGroup (S5.Γ ⧸ Subgroup.center S5.Γ) :=
      (CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 f' hCE).2
    have hq : CFSG.Open.IsQuasisimple ↥S5.Γ :=
      ⟨Group.IsPerfect.commutator_eq_top, hsimple⟩
    have h2f' : 2 ^ f' = S.D.q := hqf'.symm.trans hq5
    obtain ⟨hLieS, hqS⟩ :=
      famTrivial_transport (algebraMap (algebraicClosure (ZMod 2) L) L) S5 S hΓ5 hLie hq
    exact ⟨.E7, f', h2f', hLieS, hqS, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · have hΦ5 := S5.exists_frobenius_of_steinberg (τ := .E8) (by decide) (by decide)
    obtain ⟨f', hf1', hqf'⟩ := ssTw_exists_f S5 (ℓ := 2)
    obtain ⟨K, hKf, hKfin, hKa, e, hKq, he⟩ :=
      S5.descends_of_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by norm_num) hΦ5 hAlg5
        (fun K' _ _ => commutator_adjointGroup_E8_eq_top K')
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hk : Nat.card K = 2 ^ f' := hKq.trans hqf'
    have hadm : StatedLieAdmissible .E8 0 2 f' := ⟨Nat.prime_two, hf1', rfl⟩
    have hLie : LieModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E8 0 2 f' :=
      CFSG.ComponentClassification.CatLeafProof.lieModel_centralQuotient_of_mulEquiv_adjointGroup
        (by decide) hadm hk e.symm
    haveI : Group.IsPerfect ↥(adjointGroup .E8 K) := ⟨commutator_adjointGroup_E8_eq_top K⟩
    haveI : Group.IsPerfect ↥S5.Γ :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hCE : ChevalleyExceptionalModel (S5.Γ ⧸ Subgroup.center S5.Γ) .E8 2 f' :=
      ((LieModel.chevalleyExceptional_iff (t := .E8) (by decide)).1 hLie).2
    have hsimple : IsSimpleGroup (S5.Γ ⧸ Subgroup.center S5.Γ) :=
      (CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 f' hCE).2
    have hq : CFSG.Open.IsQuasisimple ↥S5.Γ :=
      ⟨Group.IsPerfect.commutator_eq_top, hsimple⟩
    have h2f' : 2 ^ f' = S.D.q := hqf'.symm.trans hq5
    obtain ⟨hLieS, hqS⟩ :=
      famTrivial_transport (algebraMap (algebraicClosure (ZMod 2) L) L) S5 S hΓ5 hLie hq
    exact ⟨.E8, f', h2f', hLieS, hqS, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem famTrivial_Γ_data
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) :
    ∃ (t : StatedLieTag) (f : ℕ), 2 ^ f = S.D.q ∧
      LieModel (S.Γ ⧸ Subgroup.center S.Γ) t 0 2 f ∧
        CFSG.Open.IsQuasisimple ↥S.Γ ∧
          (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) := by
  obtain ⟨t, f, h2f, hLie, hq, htag⟩ := famTrivial_Γ_data_tag hτ S
  refine ⟨t, f, h2f, hLie, hq, ?_⟩
  rcases htag with ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht⟩ | ⟨-, ht⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inr (Or.inr ht))
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl ht))

theorem famTrivial_ggCompFieldAtSL_Γ
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) :
    CFSG.StandardType.GGCompFieldAtSL S.D.q S.Γ := by
  obtain ⟨t, f, h2f, hLie, hq, ht4⟩ := famTrivial_Γ_data hτ S
  have ht9 : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨
      t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4 := by
    rcases ht4 with rfl | rfl | rfl | rfl <;> decide
  have hgg : CFSG.StandardType.GGCompFieldAtSL (2 ^ f) S.Γ :=
    CFSG.StandardType.ggCompFieldAtSL_of_lieModel hq hLie ht9
  rw [h2f] at hgg
  exact hgg

end CFSG.StandardType.TableCRes

end
