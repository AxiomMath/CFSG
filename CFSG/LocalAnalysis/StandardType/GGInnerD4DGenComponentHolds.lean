module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenContracts

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType

private lemma ltrdg4_exists_three_singular
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x).subtype))
    (hdim : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) = 8) :
    ∃ U : Submodule K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x),
      Module.finrank K U = 3 ∧
        ∀ u ∈ U, (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x).subtype) u = 0 := by
  classical
  obtain ⟨W, hW, hWs⟩ := hplus
  have hWfin : Module.finrank K W = 4 := by omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := ↥W) (n := 3) (by omega)
  let q : Submodule K ↥W := Submodule.span K (Set.range f)
  have hq : Module.finrank K q = 3 := by
    have h := finrank_span_eq_card (R := K) hf
    simpa [q] using h
  refine ⟨q.map W.subtype, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq W q, hq]
  · rintro u hu
    obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp hu
    rw [← hwu]
    simpa using hWs w w.2

theorem orthogonalD4ComponentInner_of_supported
    (h : S2MathAs51600Contracts.SupportedFixedThreeInner) :
    S2MathAs51600Contracts.OrthogonalD4ComponentInner := by
  intro hRig K _ _ _ V _ _ _ n n' hn hn' hcard Q hQ hT x c hx hc3 hcx I hI hlab
  classical
  obtain ⟨_hn'n, hdim, hplus, hIeq⟩ :=
    S2MathAs51586Freeze.componentD4Identification_holds
      hRig K V n n' hn hn' hcard Q hQ hT x hx I hI hlab
  obtain ⟨U, hUfin, hUsing⟩ := ltrdg4_exists_three_singular hplus hdim
  have hcM : (c : V ≃ₗ[K] V) ∈
      CFSG.RankThree.PartOne.KCOrthogonal.isometryCentralizer Q (x : V ≃ₗ[K] V) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_isometryCentralizer]
    refine ⟨?_, ?_⟩
    · intro v
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup c.2)) v
    · intro v
      have hcv : (c : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) =
          (x : V ≃ₗ[K] V) * (c : V ≃ₗ[K] V) := by
        simpa using congrArg (fun y : CFSG.RankThree.Classical2.orthDerived Q =>
          (y : V ≃ₗ[K] V)) hcx
      exact congrFun (congrArg (fun e : V ≃ₗ[K] V => (e : V → V)) hcv) v
  have hc3' : (c : V ≃ₗ[K] V) ^ 3 = 1 := by
    simpa using congrArg (fun y : CFSG.RankThree.Classical2.orthDerived Q =>
      (y : V ≃ₗ[K] V)) hc3
  obtain ⟨u, hu, _hu3, hconj⟩ :=
    h K V Q (x : V ≃ₗ[K] V) hx ⟨U, hUfin, hUsing⟩ (c : V ≃ₗ[K] V) hcM hc3'
  let uΩ : CFSG.RankThree.Classical2.orthDerived Q :=
    ⟨u, hx.supportedFixedDerived_le_orthDerived hu⟩
  let ρ : ↥(CFSG.RankThree.Classical2.orthDerived Q) →*
      CFSG.RankThree.Classical2.ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (CFSG.RankThree.Classical2.orthDerived Q))
  refine ⟨ρ uΩ, ?_, ?_⟩
  · rw [hIeq]
    exact Subgroup.mem_map.mpr ⟨uΩ, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  · intro v hv
    rw [hIeq] at hv
    obtain ⟨g, hgsub, hgv⟩ := Subgroup.mem_map.mp hv
    rw [← hgv]
    simp only [← map_mul, ← map_inv]
    refine congrArg ρ (Subtype.ext ?_)
    have hg' := hconj (g : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hgsub)
    simpa using hg'

end CFSG.StandardType.GGInnerD4DGenParts

end
