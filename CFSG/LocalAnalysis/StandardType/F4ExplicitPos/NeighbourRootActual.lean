module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NeighbourSquare
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6NeighbourRoot
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6RootDictionary

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.NeighbourRootActual

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.LieCore CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.S2MathFi1035Pos CFSG.SeitzReduction.F4Pilot
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.F4ExplicitPos.C3Range CFSG.StandardType.F4ExplicitPos.Sp6RootDictionary
  CFSG.StandardType.F4ExplicitPos.RationalC3 CFSG.StandardType.F4ExplicitPos.RationalB3

theorem ggRootVia_of_actual_rankThree
    (f : ℕ) (hf : 1 ≤ f)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]
    [Algebra (GaloisField 2 f) Ω]
    {X : Type} [Group X]
    (G0 K R : Subgroup X) (hKG : K ≤ G0) (hRK : R ≤ K)
    (η : G0 →* ModGL Tag.F4 Ω) (hη : Function.Injective η)
    (D : LangDatum Tag.F4 Ω) (hq : D.q = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Ωˣ)
    (i : KernelComponent (rootCharHom a))
    (hker : ∀ γ ∈ kernelRoots (rootCharHom a),
      ρ γ ∈ kernelRoots (rootCharHom a))
    (hstable : (fun γ => ρ γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (h3 : compRank (componentRoots (rootCharHom a) i) = 3)
    (h18 : (componentRoots (rootCharHom a) i).ncard = 18)
    (v : WeylGroup Tag.F4)
    (hshape :
      componentRoots (rootCharHom a) i =
        (fun γ => v • γ) '' CFSG.SeitzReduction.F4Pilot.b3LeviRoots ∨
      componentRoots (rootCharHom a) i =
        (fun γ => v • γ) '' _root_.CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet)
    (hKcomp : CFSG.Assembly.IsComponentOf ((K.subgroupOf G0).map η)
      (D.Γ ⊓ Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 Ω))))
    (hKspan : (K.subgroupOf G0).map η ≤
      rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i))
    (hcard : Nat.card ((R.subgroupOf G0).map η) = Nat.card (GaloisField 2 f))
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots (rootCharHom a) i)
    {wD : ModGL Tag.F4 Ω}
    (hwD : wD ∈ CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub (rootCharHom a))
    (hRcurve : (R.subgroupOf G0).map η ≤
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom) :
    ∃ β ∈ (ggU .PSp 3 f).D.roots, GGRootVia (ggU .PSp 3 f) K R β := by
  classical
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let Ccent : Subgroup (ModGL Tag.F4 Ω) := Subgroup.centralizer {rootDiagUnit Tag.F4 a}
  let Kbar : Subgroup (ModGL Tag.F4 Ω) := (K.subgroupOf G0).map η
  have hS : componentRoots (rootCharHom a) i ⊆ rootCharKernel a := by
    intro γ hγ
    obtain ⟨hγk, -⟩ := hγ
    exact ⟨hγk.1, by simpa [rootCharHom] using hγk.2⟩
  have hHC : rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i) ≤ Ccent :=
    rootSpan_le_centralizer a hS
  have hmodel : ∃ (Φ : StatedSp 3 Ω →* ModGL Tag.F4 Ω) (ze : ModGL Tag.F4 Ω)
      (κ : StatedSp 3 (GaloisField 2 f) →* ModGL Tag.F4 Ω),
      Function.Injective Φ ∧
      Φ.range = componentRootSpan Ω (rootCharHom a) i ∧
      ze ∈ CFSG.StandardType.F4ExplicitPos.NativePinFinal.Zsub (rootCharHom a) ∧
      κ = ((MulAut.conj ze).toMonoidHom.comp Φ).comp
        (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3) ∧
      κ.range = (K.subgroupOf G0).map η ∧
      ∃ β ∈ (Symplectic.rootDatum 3 Ω).roots,
        ((Symplectic.rootDatum 3 Ω).rootGroup β).map Φ =
          rootSubgroup Tag.F4 Ω α := by
    rcases hshape with hshapeB | hshapeC
    ·
      obtain ⟨_, z, Φp, _, hze, _, _, _, hΦform, _, _, hPeq⟩ :=
        CFSG.StandardType.F4ExplicitPos.RankThreeModels.f4_rankThree_b3_actual_model_producer
          Ω D f hf hq hk ρ hρ i hker hstable h3 h18 v hshapeB Ccent hHC Kbar hKcomp hKspan
      refine ⟨conjBM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v), z, Φp,
        ?_, ?_, hze, ?_, ?_, ?_⟩
      · exact conjBM_injective Ω _
      · rw [range_conjBM_canonicalRep Ω v, ← hshapeB]
        rfl
      · exact hΦform.trans (PhiB_eq Ω (canonicalRep (coxeterSystem Tag.F4) Ω v) z)
      · exact hPeq.symm
      · obtain ⟨β, hβ, hβmap⟩ :=
          Sp6RootDictionary.exists_rootGroup_map_eq_rootSubgroup_b3 Ω v
            (hshapeB ▸ hα)
        refine ⟨β, hβ, ?_⟩
        have hphi : CFSG.StandardType.F4ExplicitPos.Sp6RootDictionary.phiB Ω v =
            conjBM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v) :=
          (conjBM_eq Ω (canonicalRep (coxeterSystem Tag.F4) Ω v)).symm
        rw [hphi] at hβmap
        exact hβmap
    ·
      obtain ⟨_, z, Φp, _, hze, _, _, _, hΦform, _, _, hPeq⟩ :=
        CFSG.StandardType.F4ExplicitPos.RankThreeModels.f4_rankThree_c3_actual_model_producer
          Ω D f hf hq hk ρ hρ i hker hstable h3 h18 v hshapeC Ccent hHC Kbar hKcomp hKspan
      refine ⟨RationalC3.conjIM Ω (canonicalRep (coxeterSystem Tag.F4) Ω v),
        z, Φp, ?_, ?_, hze, ?_, ?_, ?_⟩
      · exact CFSG.StandardType.F4ExplicitPos.RationalC3.conjIM_injective Ω _
      · rw [CFSG.StandardType.F4ExplicitPos.RationalC3.range_conjIM_canonicalRep Ω v, ← hshapeC]
        rfl
      · exact hΦform
      · exact hPeq.symm
      · obtain ⟨β, hβ, hβmap⟩ :=
          Sp6RootDictionary.exists_rootGroup_map_eq_rootSubgroup_c3 Ω v
            (hshapeC ▸ hα)
        refine ⟨β, hβ, ?_⟩
        rw [CFSG.StandardType.F4ExplicitPos.Sp6RootDictionary.phiC_eq_conjIM Ω v] at hβmap
        exact hβmap
  obtain ⟨Φ, ze, κ, hΦinj, hΦrange, hze, hκformula, hκrange, β, hβ, hβmap⟩ := hmodel
  let Λ : StatedSp 3 Ω →* ModGL Tag.F4 Ω := (MulAut.conj ze).toMonoidHom.comp Φ
  have hΛ : Function.Injective Λ := (MulAut.conj ze).injective.comp hΦinj
  have hκ : κ = Λ.comp (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3) := hκformula
  have hRG : R ≤ G0 := hRK.trans hKG
  have hRbar : (R.subgroupOf G0).map η ≤ κ.range := by
    rw [hκrange]
    exact Subgroup.map_mono (Subgroup.comap_mono hRK)
  have hw : ze⁻¹ * wD ∈ torusGroup Tag.F4 Ω ⊔
      rootSpan Tag.F4 Ω (kernelRoots (rootCharHom a)) :=
    (CFSG.StandardType.F4ExplicitPos.NativePinFinal.mem_Zsub_iff (rootCharHom a) (ze⁻¹ * wD)).mp
      (mul_mem (inv_mem hze) hwD)
  obtain ⟨vΩ, hsqAll⟩ :=
    CFSG.StandardType.F4ExplicitPos.NeighbourSquare.exists_vOmega_neighbour_square_allU
      (χ := rootCharHom a) i hΦrange hw
  have hsqβ := hsqAll ((Symplectic.rootDatum 3 Ω).rootGroup β)
  rw [hβmap] at hsqβ
  rw [Subgroup.map_map] at hsqβ
  have hplus : (R.subgroupOf G0).map η ≤
      (((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom).map Λ := by
    rw [hsqβ]
    exact hRcurve
  exact CFSG.StandardType.F4ExplicitPos.Sp6NeighbourRoot.ggRootVia_of_Sp6_neighbour
    f hf G0 K R hKG hRG η hη Λ hΛ κ hκ hκrange hcard hRbar hβ vΩ hplus

end CFSG.StandardType.F4ExplicitPos.NeighbourRootActual

end

end
