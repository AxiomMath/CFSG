module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LocalAnalysis.StandardType.GGLangCoroot

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {H : Subgroup G} {d : G}
    (hd : d ∈ H) : H.map (MulAut.conj d).toMonoidHom = H :=
  (Subgroup.pointwise_smul_def H).symm.trans (Subgroup.conj_smul_eq_self_of_mem hd)

theorem conj_rationalSpan_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (a b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    (rationalSpan S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj (rootDiagUnit τ b)).toMonoidHom =
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
  have hdM : rootDiagUnit τ b ∈ S.D.model := S.D.torus_le_model hb
  have hΓ : S.Γ.map (MulAut.conj (rootDiagUnit τ b)).toMonoidHom = S.Γ := by
    change ⁅S.D.model, S.D.model⁆.map _ = ⁅S.D.model, S.D.model⁆
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem hdM]
  have hspan : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map
      (MulAut.conj (rootDiagUnit τ b)).toMonoidHom =
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
    map_rootSpan_of_forall fun α hα =>
      map_conj_rootDiagUnit_rootSubgroup b (isRoot_of_mem_rationalRoots S i hα)
  change (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).map _ =
    rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (rootDiagUnit τ b)).injective, hspan, hΓ]

theorem conj_rationalComponent_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (a b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    (rationalComponent S.ρ S.Γ (rootCharHom a) i).map
        (MulAut.conj (rootDiagUnit τ b)).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  change (⁅rationalSpan S.ρ S.Γ (rootCharHom a) i, rationalSpan S.ρ S.Γ (rootCharHom a) i⁆).map
    _ = _
  rw [Subgroup.map_commutator, conj_rationalSpan_eq S a b hb i]
  rfl

theorem rootDiagUnit_mem_normalizer_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (a b : Fin τ.rank → Lˣ) (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    rootDiagUnit τ b ∈
      Subgroup.normalizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ L)) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.2 (conj_rationalComponent_eq S a b hb i)

end CFSG.StandardType.LangRat
