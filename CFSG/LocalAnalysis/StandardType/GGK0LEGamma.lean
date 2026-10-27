module

public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem langGamma_conj_eq_map_adjointGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L),
      Nat.card K = S.D.q ∧
        S.Γ.map (MulAut.conj S.D.g0).toMonoidHom =
          (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨K, _, _, _, hK⟩ := S.exists_fixedField
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hK]; exact hFr c
  haveI : Algebra.IsAlgebraic K L := ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hAlg c
    have hq1 : 1 < Nat.card K ^ n := by
      rw [hK]
      exact Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
    refine ⟨Polynomial.X ^ (Nat.card K ^ n) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hK, hc, sub_self]⟩
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  have hperf : ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K :=
    CFSG.TauCetiBridge.Even.commutator_adjointGroup_eq_of_singleEdge τ K (by
      rcases hτ with h | h | h | h <;> simp [h])
  have hfinal := CFSG.TauCetiBridge.Even.Lang_Frobenius_fixed_derived_of_perfect
    τ K hperf L Fr hFrK
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ?_⟩
  rw [show S.Γ = S.D.Γ from rfl, S.D.map_conj_Γ]
  have hfix_eq : S.D.fix =
      adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [show S.D.fix = adjointGroup τ L ⊓ S.D.Φ.eqLocus (MonoidHom.id _) from rfl, hΦ]
  rw [hfix_eq]
  exact hfinal.2.2.2

end CFSG.StandardType.LangRat

end
