module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.LieType.AlgebraicGroups.ToralRootCoverAlgebra
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem lk0xu7e_kernelRoots_joint_subset
    {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
    (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hDB : D ≤ B₁) {e : X} (he : e ∈ D) :
    kernelRoots P.chiD ⊆ kernelRoots (P.chiAt e) := by
  intro γ hγ
  rw [kernelRoots] at hγ ⊢
  obtain ⟨hγroot, hγchar⟩ := hγ
  have hxchar : rootChar (P.coord x) γ = 1 := by
    have h := congrArg Prod.fst hγchar
    simpa [ExcPacket.chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom] using h
  have hdchar : rootChar (P.coord P.d) γ = 1 := by
    have h := congrArg Prod.snd hγchar
    simpa [ExcPacket.chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom] using h
  have hxD : x ∈ D := by
    have hx : x ∈ Subgroup.closure ({x, P.d} : Set X) :=
      Subgroup.subset_closure (by simp)
    rwa [P.closure_eq] at hx
  have hdD : P.d ∈ D := by
    have hd : P.d ∈ Subgroup.closure ({x, P.d} : Set X) :=
      Subgroup.subset_closure (by simp)
    rwa [P.closure_eq] at hd
  let ΘD : ↥D →* ModGL Tag.E6 (ExcOmega f) := P.Θ.comp (Subgroup.inclusion hDB)
  have hcoord : ∀ b : ↥D, ΘD b = rootDiagUnit Tag.E6 (P.coord b) := by
    intro b
    exact P.Θ_eq_coord (Subgroup.inclusion hDB b) b.2
  let Q : Subgroup ↥D :=
    (Subgroup.centralizer
      ({pinnedX Tag.E6 (ExcOmega f) γ 1} : Set (ModGL Tag.E6 (ExcOmega f)))).comap ΘD
  have hxQ : (⟨x, hxD⟩ : ↥D) ∈ Q := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_pinnedX (P.coord x) hγroot 1
    rw [hxchar, Units.val_one, one_mul] at h
    have h' := mul_inv_eq_iff_eq_mul.1 h
    simpa only [ΘD, MonoidHom.comp_apply, hcoord ⟨x, hxD⟩] using h'
  have hdQ : (⟨P.d, hdD⟩ : ↥D) ∈ Q := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_pinnedX (P.coord P.d) hγroot 1
    rw [hdchar, Units.val_one, one_mul] at h
    have h' := mul_inv_eq_iff_eq_mul.1 h
    simpa only [ΘD, MonoidHom.comp_apply, hcoord ⟨P.d, hdD⟩] using h'
  have hsub : ({x, P.d} : Set X) ⊆ (Q.map D.subtype : Subgroup X) := by
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]; exact Subgroup.mem_map.mpr ⟨⟨x, hxD⟩, hxQ, rfl⟩
    · rw [h]; exact Subgroup.mem_map.mpr ⟨⟨P.d, hdD⟩, hdQ, rfl⟩
  have hDle : D ≤ Q.map D.subtype := by
    have h := (Subgroup.closure_le (Q.map D.subtype)).mpr hsub
    rwa [P.closure_eq] at h
  obtain ⟨q, hqQ, hqval⟩ := Subgroup.mem_map.mp (hDle he)
  have heQ : (⟨e, he⟩ : ↥D) ∈ Q := by
    have hqe : (⟨e, he⟩ : ↥D) = q := Subtype.ext hqval.symm
    rwa [hqe]
  have heMem : ΘD ⟨e, he⟩ ∈
      Subgroup.centralizer
        ({pinnedX Tag.E6 (ExcOmega f) γ 1} : Set (ModGL Tag.E6 (ExcOmega f))) :=
    Subgroup.mem_comap.mp heQ
  have hcomm : ΘD ⟨e, he⟩ * pinnedX Tag.E6 (ExcOmega f) γ 1 =
      pinnedX Tag.E6 (ExcOmega f) γ 1 * ΘD ⟨e, he⟩ :=
    Subgroup.mem_centralizer_singleton_iff.mp heMem
  have hstep : rootDiagUnit Tag.E6 (P.coord e) * pinnedX Tag.E6 (ExcOmega f) γ 1 *
      (rootDiagUnit Tag.E6 (P.coord e))⁻¹ = pinnedX Tag.E6 (ExcOmega f) γ 1 := by
    rw [← hcoord ⟨e, he⟩, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj := rootDiagUnit_conj_pinnedX (P.coord e) hγroot 1
  rw [hstep] at hconj
  have hparam : (((rootChar (P.coord e) γ : (ExcOmega f)ˣ) : ExcOmega f) * 1) = 1 :=
    (pinnedX_injective Tag.E6 (ExcOmega f) γ hconj).symm
  refine ⟨hγroot, ?_⟩
  have hroot : rootChar (P.coord e) γ = 1 := Units.ext (by simpa using hparam)
  simpa [ExcPacket.chiAt, CFSG.LieType.AlgebraicGroups.rootCharHom] using hroot

theorem excU7_swapped {X : Type} [Group X] {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    {R Rm : Subgroup X} (P : ExcPacket Tag.E6 f p G₀ B₁ D J x R Rm) (hb : P.b = 2)
    (hDB : D ≤ B₁) {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) (hSD : S.D = P.Δ) (hSρ : S.ρ = P.ρ)
    {e : X} (he : e ∈ D) {iK : KernelComponent (P.chiAt e)}
    (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK)
    {i₂ : KernelComponent P.chiD} (hi₂ : i₂ ≠ P.iJ)
    (hi₂roots : componentRoots P.chiD i₂ = (fun u => P.ρ u) '' P.rootsJ)
    (hsub₂ : (fun u => P.ρ u) '' P.rootsJ ⊆ componentRoots (P.chiAt e) iK) :
    ExcSwapped S (P.coord e) iK f ((R.subgroupOf G₀).map P.η) := by
  have hk : kernelRoots P.chiD ⊆ kernelRoots (P.chiAt e) :=
    lk0xu7e_kernelRoots_joint_subset P hDB he
  obtain ⟨hstableΔ, hAleΔ, hcardΔ⟩ := P.pair_two hb
  have himg : S.ρ '' componentRoots P.chiD P.iJ = componentRoots P.chiD i₂ := by
    rw [hSρ]
    simpa only [ExcPacket.rootsJ] using hi₂roots.symm
  have hnorm : torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots P.chiD) ≤
      Subgroup.normalizer (rootSpan Tag.E6 GGL (componentRoots P.chiD P.iJ)) := by
    refine sup_le ?_ ?_
    · exact torusGroup_le_normalizer_rootSpan
        (S := componentRoots P.chiD P.iJ) (fun _ hα => isRoot_of_mem_componentRoots hα)
    · simpa only [CFSG.LieType.Chevalley.componentRootSpan,
        CFSG.LieType.Chevalley.componentRoots] using
        (rootSpan_le_normalizer (K := GGL) (χ := P.chiD) P.iJ)
  have hwNorm : P.wD ∈
      Subgroup.normalizer (rootSpan Tag.E6 GGL (componentRoots P.chiD P.iJ)) :=
    hnorm P.wD_mem
  have hVJ : excCurve P.α P.wD ≤ rootSpan Tag.E6 GGL (componentRoots P.chiD P.iJ) := by
    rw [excCurve]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    change P.wD * z * P.wD⁻¹ ∈ rootSpan Tag.E6 GGL (componentRoots P.chiD P.iJ)
    exact (Subgroup.mem_normalizer_iff.mp hwNorm z).mp
      (rootSubgroup_le_rootSpan (S := componentRoots P.chiD P.iJ) (α := P.α) P.α_mem hz)
  have hmapV : (excCurve P.α P.wD).map S.D.step ≤
      rootSpan Tag.E6 GGL (componentRoots P.chiD i₂) := by
    calc (excCurve P.α P.wD).map S.D.step
        ≤ (rootSpan Tag.E6 GGL (componentRoots P.chiD P.iJ)).map S.D.step :=
          Subgroup.map_mono hVJ
      _ = rootSpan Tag.E6 GGL (S.ρ '' componentRoots P.chiD P.iJ) :=
          map_rootSpan_step S _ (fun _ hα => isRoot_of_mem_componentRoots hα)
      _ = rootSpan Tag.E6 GGL (componentRoots P.chiD i₂) := by rw [himg]
  refine ⟨?_, ?_, ?_⟩
  · have hf : f ≠ 0 := Nat.one_le_iff_ne_zero.mp P.one_le_f
    rw [hcardΔ, CFSG.StandardType.ChevTwo.card_galoisField_two hf]
  · calc (R.subgroupOf G₀).map P.η ≤ P.η.range :=
          Subgroup.map_le_range P.η (R.subgroupOf G₀)
      _ = P.Δ.Γ := P.range_η
      _ = S.Γ := by
            show P.Δ.Γ = S.D.Γ
            rw [hSD]
  · refine ⟨P.α, P.wD, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsub P.α_mem
    · exact (sup_le_sup le_rfl (rootSpan_mono hk)) P.wD_mem
    · exact hVJ.trans (rootSpan_mono hsub)
    · rw [hSD]
      exact hstableΔ
    · intro v hv v' hv'
      have hvJ : v ∈ componentRootSpan GGL P.chiD P.iJ := by
        simpa only [CFSG.LieType.Chevalley.componentRootSpan,
          CFSG.LieType.Chevalley.componentRoots] using hVJ hv
      have hv'₂ : v' ∈ componentRootSpan GGL P.chiD i₂ := by
        simpa only [CFSG.LieType.Chevalley.componentRootSpan,
          CFSG.LieType.Chevalley.componentRoots] using hmapV hv'
      exact commute_of_mem_componentRootSpan (i := P.iJ) (i' := i₂) hi₂.symm hvJ hv'₂
    · rw [hSD]
      exact hAleΔ

end CFSG.StandardType.LieKnownR2.ExcPos
