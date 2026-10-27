module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2Excl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.LocalAnalysis.GLTheoremA CFSG.Open
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggNbrLSideRSExc_u2_typeA
    (hExcl : GGNbrLSideRSExcExcl) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (h2 : (2 : L) = 0) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {Q : ℕ}
    (hP : GGNbrLSideRSExcPSL3 S a i Q) (hA : L154TypeAClass a i) :
    twistKind S.ρ (rootCharHom a) i = .inner ∧
      compRank (componentRoots (rootCharHom a) i) = 2 ∧
      (componentRoots (rootCharHom a) i).ncard = 6 ∧
      Q = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by simpa using h2)
  obtain ⟨hT, hp3, hne, hqs, hQ4, h3Q, F, hFf, hFin, hFc, ⟨e⟩⟩ := hP
  have hF4 : 4 ≤ Nat.card F := hFc ▸ hQ4
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · obtain ⟨f, hf1, hfeq, hmodel⟩ := I167.excRec_typeA_inner S Nat.prime_three hT hp3 hne i
      ⟨by have := hA.1; omega, hA.2⟩ hin hqs
    have hLie := I167.excRec_lieModel_two (by decide) hmodel
    obtain ⟨-, hm, hcard⟩ := hExcl hF4 e hLie
    have hr : compRank (componentRoots (rootCharHom a) i) = 2 := by omega
    refine ⟨?_, hr, ?_, ?_⟩
    · unfold twistKind
      rw [if_pos hin]
    · rw [hA.2, hr]
    · rw [← hFc, hcard, ← hfeq, ringChar.eq L 2]
  · exfalso
    obtain ⟨f, hf1, hfeq, hmodel⟩ :=
      I167.excRec_typeA_suN S Nat.prime_three hT hp3 hne i hA hin hqs
    have hLie := I167.excRec_lieModel_two (by decide) hmodel
    obtain ⟨ht, -, -⟩ := hExcl hF4 e hLie
    exact absurd ht (by decide)

end CFSG.StandardType
