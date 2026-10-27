module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutDCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainModel
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB3Part1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortPairStabilizerPart1
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowField

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Ree.ReeTag


variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

theorem centralizer_c3PerpLevi_eq_of_isAlgClosed :
    adjointGroup .F4 Ω ⊓ Subgroup.centralizer (c3PerpLevi Ω : Set (ModGL .F4 Ω)) =
      highestRootRankOne Ω := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset Ω)
  have hthird : ∃ c : Ω, c ≠ 0 ∧ c ≠ 1 := ⟨c, by simpa only [Finset.mem_insert,
    Finset.mem_singleton, not_or] using hc⟩
  exact centralizer_c3PerpLevi_eq_of_exists_ne_zero_ne_one hthird

variable [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem centralizer_conjIM_eq (n : ModGL .F4 Ω) (hn : n ∈ adjointGroup .F4 Ω) :
    adjointGroup .F4 Ω ⊓
        Subgroup.centralizer ((RationalC3.conjIM Ω n).range : Set (ModGL .F4 Ω)) =
      (rootSL2R Ω).map (MulAut.conj n).toMonoidHom := by
  have hroots : c3PerpRoots = C3Range.c3RootSet := by
    rw [B3Pinned.c3RootSet_eq_c3LeviRoots]
    ext γ
    rw [mem_c3PerpRoots_iff, mem_c3LeviRoots]
  have hnmap : (adjointGroup .F4 Ω).map (MulAut.conj n).toMonoidHom =
      adjointGroup .F4 Ω := by
    exact Subgroup.conj_smul_eq_self_of_mem hn
  rw [RationalC3.range_conjIM, ← hroots, ← c3PerpLevi]
  calc
    _ = (adjointGroup .F4 Ω ⊓
        Subgroup.centralizer (c3PerpLevi Ω : Set (ModGL .F4 Ω))).map
          (MulAut.conj n).toMonoidHom := by
      simpa only [hnmap] using map_inf_centralizer_map
        (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective
        (adjointGroup .F4 Ω) (c3PerpLevi Ω)
    _ = _ := by
      rw [centralizer_c3PerpLevi_eq_of_isAlgClosed, highestRootRankOne_eq_rootSL2R]

theorem centralizer_conjIM_canonicalRep_eq (v : WeylGroup .F4) :
    adjointGroup .F4 Ω ⊓ Subgroup.centralizer
        ((RationalC3.conjIM Ω (canonicalRep (coxeterSystem .F4) Ω v)).range :
          Set (ModGL .F4 Ω)) =
      (rootSL2R Ω).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) Ω v)).toMonoidHom :=
  centralizer_conjIM_eq _ (canonicalRep_mem_adjointGroup (coxeterSystem .F4) Ω v)

theorem centralizer_C3Levi_eq_of_isAlgClosed :
    Subgroup.centralizer (C3Levi Ω : Set (adjointGroup .F4 Ω)) =
      ShortPairStabilizer.UA Ω rootR ⊔ ShortPairStabilizer.UA Ω (-rootR) := by
  have hperp : (C3Levi Ω).map (adjointGroup .F4 Ω).subtype = c3PerpLevi Ω := by
    rw [map_subtype_C3Levi, c3PerpLevi]
    congr 1
    ext γ
    rw [mem_c3LeviRoots, mem_c3PerpRoots_iff]
  have hcenter : (Subgroup.centralizer (C3Levi Ω : Set (adjointGroup .F4 Ω))).map
      (adjointGroup .F4 Ω).subtype = highestRootRankOne Ω := by
    have h := map_inf_centralizer_map (f := (adjointGroup .F4 Ω).subtype)
      (adjointGroup .F4 Ω).subtype_injective
      (⊤ : Subgroup (adjointGroup .F4 Ω)) (C3Levi Ω)
    simpa only [Subgroup.map_top, Subgroup.range_subtype, hperp, top_inf_eq,
      centralizer_c3PerpLevi_eq_of_isAlgClosed] using h.symm
  apply Subgroup.map_injective (f := (adjointGroup .F4 Ω).subtype)
    (adjointGroup .F4 Ω).subtype_injective
  rw [hcenter, highestRootRankOne_eq_rootSL2R, Subgroup.map_sup,
    ShortPairStabilizer.UA_map_incl, ShortPairStabilizer.UA_map_incl]
  rfl

theorem centralizer_b3Levi_eq_of_isAlgClosed :
    adjointGroup .F4 Ω ⊓ Subgroup.centralizer
        (rootSpan .F4 Ω b3LeviRoots : Set (ModGL .F4 Ω)) =
      rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS) := by
  let f : adjointGroup .F4 Ω →* ModGL .F4 Ω :=
    (adjointGroup .F4 Ω).subtype.comp (B3Algebraic.sigmaΩF4 Ω)
  have hf : Function.Injective f :=
    (adjointGroup .F4 Ω).subtype_injective.comp (B3Algebraic.sigmaΩ_bijective Ω).1
  have htop : (⊤ : Subgroup (adjointGroup .F4 Ω)).map f = adjointGroup .F4 Ω := by
    dsimp only [f]
    rw [← Subgroup.map_map,
      Subgroup.map_top_of_surjective (B3Algebraic.sigmaΩF4 Ω)
        (B3Algebraic.sigmaΩ_bijective Ω).2,
      Subgroup.map_top, Subgroup.range_subtype]
  have hfactor : (C3Levi Ω).map f = rootSpan .F4 Ω b3LeviRoots := by
    have h := B3Algebraic.iBΩ_map_range Ω
    change (f.comp (C3Algebraic.iOmega Ω)).range = _ at h
    rw [MonoidHom.range_comp, B3Algebraic.range_iOmega_eq_C3Levi] at h
    exact h
  have hr : IsRoot .F4 rootR := by
    rw [← orbitCertRoot_47_eq_rootR]
    exact highestRoot_long.1
  have hdual : F4.dualRoot rootR = rootS := dualRoot_rootR_rootS_root1221_root1242.1
  have hneg : F4.dualRoot (-rootR) = -rootS :=
    (dualRoot_neg (t := .F4) hr).trans (congrArg (fun x => -x) hdual)
  calc
    _ = (Subgroup.centralizer (C3Levi Ω : Set (adjointGroup .F4 Ω))).map f := by
      simpa only [htop, hfactor, top_inf_eq] using
        map_inf_centralizer_map (f := f) hf
          (⊤ : Subgroup (adjointGroup .F4 Ω)) (C3Levi Ω)
    _ = _ := by
      rw [centralizer_C3Levi_eq_of_isAlgClosed]
      dsimp only [f]
      rw [← Subgroup.map_map, Subgroup.map_sup,
        ShortPairStabilizer.UA_map_sigma Ω hr,
        ShortPairStabilizer.UA_map_sigma Ω (IsRoot.neg hr), hdual, hneg,
        Subgroup.map_sup, ShortPairStabilizer.UA_map_incl, ShortPairStabilizer.UA_map_incl]

theorem centralizer_conjBM_eq (n : ModGL .F4 Ω) (hn : n ∈ adjointGroup .F4 Ω) :
    adjointGroup .F4 Ω ⊓
        Subgroup.centralizer ((RationalB3.conjBM Ω n).range : Set (ModGL .F4 Ω)) =
      (rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS)).map
        (MulAut.conj n).toMonoidHom := by
  have hnmap : (adjointGroup .F4 Ω).map (MulAut.conj n).toMonoidHom =
      adjointGroup .F4 Ω := by
    exact Subgroup.conj_smul_eq_self_of_mem hn
  rw [RationalB3.range_conjBM]
  calc
    _ = (adjointGroup .F4 Ω ⊓ Subgroup.centralizer
        (rootSpan .F4 Ω b3LeviRoots : Set (ModGL .F4 Ω))).map
          (MulAut.conj n).toMonoidHom := by
      simpa only [hnmap] using map_inf_centralizer_map
        (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective
        (adjointGroup .F4 Ω) (rootSpan .F4 Ω b3LeviRoots)
    _ = _ := by rw [centralizer_b3Levi_eq_of_isAlgClosed]

theorem centralizer_conjBM_canonicalRep_eq (v : WeylGroup .F4) :
    adjointGroup .F4 Ω ⊓ Subgroup.centralizer
        ((RationalB3.conjBM Ω (canonicalRep (coxeterSystem .F4) Ω v)).range :
          Set (ModGL .F4 Ω)) =
      (rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS)).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) Ω v)).toMonoidHom :=
  centralizer_conjBM_eq _ (canonicalRep_mem_adjointGroup (coxeterSystem .F4) Ω v)

end CFSG.StandardType.F4ExplicitPos
