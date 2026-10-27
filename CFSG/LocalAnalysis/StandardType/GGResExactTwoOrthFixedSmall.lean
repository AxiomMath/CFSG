module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Basic
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithfulMultiple.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421

public section

namespace CFSG.StandardType

open Module QuadraticMap Polynomial

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions

namespace OrthTorus

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] [CharP K 2] in
theorem ggResX2_isSolvable_supportedFixedDerived_of_le_two
    (hx : OddOrderIsometry Q p x) (h2 : Module.finrank K (fixedSpace x) ≤ 2) :
    Group.IsSolvable ↥(supportedFixedDerived Q x) := by
  classical
  have hRnd : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hOrthSol : Group.IsSolvable ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := by
    rcases Nat.lt_or_ge (Module.finrank K (fixedSpace x)) 2 with h1 | h2'
    · refine isSolvable_of_comm fun a b => ?_
      have ha1 : (a : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd a.2)
      have hb1 : (b : fixedSpace x ≃ₗ[K] fixedSpace x) = 1 :=
        eq_one_of_dicksonHom_eq_one_of_finrank_le_one hRnd (by omega)
          (dicksonHom_apply_orthDerived_eq_one hRnd b.2)
      refine Subtype.ext ?_
      show (a : fixedSpace x ≃ₗ[K] fixedSpace x) * b = b * a
      rw [ha1, hb1]
    · have hdim : Module.finrank K (fixedSpace x) = 2 := by omega
      refine isSolvable_of_comm fun a b => ?_
      have ha : dicksonHom (Q.comp (fixedSpace x).subtype) hRnd
          ⟨(a : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup a.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd a.2
      have hb : dicksonHom (Q.comp (fixedSpace x).subtype) hRnd
          ⟨(b : fixedSpace x ≃ₗ[K] fixedSpace x), orthDerived_le_orthogonalGroup b.2⟩ = 1 :=
        dicksonHom_apply_orthDerived_eq_one hRnd b.2
      exact Subtype.ext (commute_of_dicksonHom_eq_one hRnd hdim
        (orthDerived_le_orthogonalGroup a.2) (orthDerived_le_orthogonalGroup b.2) ha hb)
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _
    (supportedFixedDerivedEquiv hx).toMonoidHom
    (supportedFixedDerivedEquiv hx).injective hOrthSol

omit [CharP K 2] in
open CFSG.HardMathSupport.Dickson in
theorem ggResX2_not_isQuasisimple_of_fixedSpace_small (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q p x)
    (hW : Module.finrank K (fixedSpace x) ≤ 2 ∨
      (Module.finrank K (fixedSpace x) = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype)))
    {F' : Subgroup (V ≃ₗ[K] V)} (hF' : F' ≤ supportedFixedDerived Q x) :
    ¬ CFSG.IsQuasisimple ↥F' := by
  intro hF'q
  have hSsol : Group.IsSolvable ↥(supportedFixedDerived Q x) := by
    rcases hW with hsmall | ⟨h4, hplus⟩
    · exact ggResX2_isSolvable_supportedFixedDerived_of_le_two hx hsmall
    · refine Sec6.OrthBlocks.isSolvable_supportedFixedDerived_of_smallFixedException hx
        (by omega) ?_
      obtain ⟨W, hWrank, hWsing⟩ := hplus
      refine Or.inr ⟨⟨h4, W, ?_, hWsing⟩, Or.inl hK⟩
      omega
  have hq' : CFSG.IsQuasisimple ↥(F'.subgroupOf (supportedFixedDerived Q x)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hF').symm hF'q
  exact @CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.not_isQuasisimple_of_isSolvable
    ↥(supportedFixedDerived Q x) inferInstance hSsol
    (F'.subgroupOf (supportedFixedDerived Q x)) hq'

end OrthTorus

end CFSG.StandardType

end
