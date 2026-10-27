module

public import CFSG.LocalAnalysis.StandardType.GGK0LQInner

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem two_lt_ncard_of_inner_quasisimple_two
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 p : ℕ}
    (S : LangSetup tau L p0) (hp : p.Prime) (hG2 : tau ≠ .G2)
    {a : Fin tau.rank → Lˣ} (hT : rootDiagUnit tau a ∈ S.D.torus)
    (hTp : rootDiagUnit tau a ^ p = 1) (h1 : rootDiagUnit tau a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin tau.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hq : S.D.q = 2) (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    2 < (componentRoots (rootCharHom a) i).ncard := by
  classical
  have hrank : ¬ (∀ alpha ∈ componentRoots (rootCharHom a) i,
      ∀ delta ∈ componentRoots (rootCharHom a) i, delta = alpha ∨ delta = -alpha) := by
    intro hrank
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos hinner]
    have hsolv := CFSG.StandardType.GGK0LQ.lq_inner_solvable_of_rank_one
      S hp hT hTp h1 i hkind (fun h => (hG2 h).elim)
      (by rw [hs1, hq]; norm_num) hrank
    let _ := hsolv
    let _ := hQS.1
    let _ : Nontrivial (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hQS
    exact Group.IsPerfect.not_isSolvable _ hsolv
  push Not at hrank
  obtain ⟨alpha, ha, delta, hd, hda, hdna⟩ := hrank
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot tau).subset fun beta hb =>
      (isRootComponent_componentRoots i).isRoot beta hb
  apply (Set.two_lt_ncard_iff hfin).mpr
  refine ⟨alpha, -alpha, delta, ha,
    (isRootComponent_componentRoots i).neg_mem alpha ha, hd, ?_, hda.symm, hdna.symm⟩
  intro hNeg
  apply ((isRootComponent_componentRoots i).isRoot alpha ha).ne_zero
  ext j
  have h := congrFun hNeg j
  change alpha j = -alpha j at h
  change alpha j = 0
  omega

end CFSG.HardMathSupport.Timmesfeld.LangTorus
