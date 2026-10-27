module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairFix
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCover
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem rckConj_conj_mul {G : Type*} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  show a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹
  group

private theorem rckConj_map_map {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G)
    (A : Subgroup G) :
    (A.map (MulAut.conj a).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  show f (a * x * a⁻¹) = f a * f x * (f a)⁻¹
  rw [map_mul, map_mul, map_inv]

private theorem rckConj_map_conj {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map, rckConj_conj_mul]

private theorem rckImage_eq_fixed
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {σ : GGL ≃+* GGL}
    {Cg : Subgroup (ModGL τ (fixSubfield σ))} {G : Type*} [Group G]
    {f : G →* ModGL τ GGL} {Ψ : G →* ↥Cg} {z : ModGL τ GGL}
    (hf : f = (MulAut.conj z).toMonoidHom.comp
      ((baseChangeGL (fixSubfield σ).subtype).comp (Cg.subtype.comp Ψ)))
    {X : Subgroup G} {g : ModGL τ (fixSubfield σ)} {γ : Fin τ.rank → ℤ}
    (hX : X.map (Cg.subtype.comp Ψ) =
      (rootSubgroup τ (fixSubfield σ) γ).map (MulAut.conj g).toMonoidHom)
    (hstep : ∀ y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      S.D.step ((z * baseChangeGL (fixSubfield σ).subtype g) * y *
          (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹) =
        (z * baseChangeGL (fixSubfield σ).subtype g) * frobGL σ y *
          (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹)
    (hγ : γ ∈ componentRoots (rootCharHom a) i) :
    X.map f =
      (rootSubgroup τ GGL γ).map
          (MulAut.conj (z * baseChangeGL (fixSubfield σ).subtype g)).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  calc X.map f
      = X.map ((MulAut.conj z).toMonoidHom.comp
          ((baseChangeGL (fixSubfield σ).subtype).comp (Cg.subtype.comp Ψ))) := by rw [hf]
    _ = (X.map ((baseChangeGL (fixSubfield σ).subtype).comp (Cg.subtype.comp Ψ))).map
          (MulAut.conj z).toMonoidHom :=
        (Subgroup.map_map X (MulAut.conj z).toMonoidHom
          ((baseChangeGL (fixSubfield σ).subtype).comp (Cg.subtype.comp Ψ))).symm
    _ = (((X.map (Cg.subtype.comp Ψ)).map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom) :=
        congrArg (fun V : Subgroup (ModGL τ GGL) => V.map (MulAut.conj z).toMonoidHom)
          (Subgroup.map_map X (baseChangeGL (fixSubfield σ).subtype) (Cg.subtype.comp Ψ)).symm
    _ = ((((rootSubgroup τ (fixSubfield σ) γ).map (MulAut.conj g).toMonoidHom).map
            (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom) := by rw [hX]
    _ = ((((rootSubgroup τ (fixSubfield σ) γ).map
            (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj (baseChangeGL (fixSubfield σ).subtype g)).toMonoidHom).map
            (MulAut.conj z).toMonoidHom) :=
        congrArg (fun V : Subgroup (ModGL τ GGL) => V.map (MulAut.conj z).toMonoidHom)
          (rckConj_map_map (baseChangeGL (fixSubfield σ).subtype) g
            (rootSubgroup τ (fixSubfield σ) γ))
    _ = ((rootSubgroup τ (fixSubfield σ) γ).map
            (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj (z * baseChangeGL (fixSubfield σ).subtype g)).toMonoidHom :=
        rckConj_map_conj ((rootSubgroup τ (fixSubfield σ) γ).map
          (baseChangeGL (fixSubfield σ).subtype))
          (baseChangeGL (fixSubfield σ).subtype g) z
    _ = (rootSubgroup τ GGL γ).map
          (MulAut.conj (z * baseChangeGL (fixSubfield σ).subtype g)).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) :=
        (rckPair_stable_fixed S σ _ hstep (isRoot_of_mem_componentRoots hγ) hγ).2

theorem rckFrameCoverPair_of_rootSpanCover
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (h : ℕ)
    (hq : S.D.q = 2 ^ h)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {Mod : LieUniversal → ℕ → Prop} (M : LieUniversal)
    (hMod : Mod M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hADE : RCKADEModel M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hfin : Finite M.K) (hperf : Group.IsPerfect M.K)
    (hsplit : CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K)
    (hcover : ∀ σ : GGL ≃+* GGL, Finite ↥(fixSubfield σ) →
      Nat.card ↥(fixSubfield σ) =
        2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →
      ∃ Ψ : M.K →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i),
        Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center M.K ∧
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
          ∀ β ∈ M.D.roots, GGLongRoot M.D β →
          ∃ γ ∈ componentRoots (rootCharHom a) i,
          ∃ g ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
            (M.D.rootGroup β).map
                ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).subtype.comp Ψ) =
              (rootSubgroup τ (fixSubfield σ) γ).map (MulAut.conj g).toMonoidHom ∧
            (M.D.rootGroup (-β)).map
                ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).subtype.comp Ψ) =
              (rootSubgroup τ (fixSubfield σ) (-γ)).map (MulAut.conj g).toMonoidHom)) :
    RCKFrameCoverPair S a i h Mod := by
  classical
  obtain ⟨σ, -, hfinK, hcardK, f, hf1, hf2, hf3, hz⟩ := rckInnerCoverExplicit S hT i hinner
  obtain ⟨Ψ, hΨsurj, hΨker, hΨpair⟩ := hcover σ hfinK (by rw [hcardK, hq, ← pow_mul])
  let C : Subgroup (ModGL τ (fixSubfield σ)) :=
    componentRootSpan (fixSubfield σ) (rootCharHom a) i
  have hperfC : ⁅C, C⁆ = C := by
    apply Subgroup.isPerfect_iff.1
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map Ψ) (Group.isPerfect_def.1 hperf)
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective Ψ hΨsurj] at h1
    rw [commutator_def]
    exact h1
  have hrange : (f.comp Ψ).range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΨsurj, Subgroup.map_top]
  have hker : (f.comp Ψ).ker ≤ Subgroup.center M.K := by
    intro x hx
    have hx' : x ∈ (Subgroup.center ↥C).comap Ψ := hf2 (show Ψ x ∈ f.ker from hx)
    rwa [CFSG.LocalCores.comap_center_eq_of_perfect hperf Ψ hΨsurj hΨker] at hx'
  refine ⟨M, f.comp Ψ, hMod, hADE, hrange.trans (le_antisymm (hf3 hperfC) hf1), hker, hfin,
    hperf, hsplit, ?_⟩
  intro hs1 β hβ hlong
  obtain ⟨z, -, hzstep, hfz, hzC, -⟩ := hz hs1
  obtain ⟨γ, hγ, g, hg, himg, himg'⟩ := hΨpair hs1 β hβ hlong
  have hfeq : f.comp Ψ = (MulAut.conj z).toMonoidHom.comp
      ((baseChangeGL (fixSubfield σ).subtype).comp (C.subtype.comp Ψ)) :=
    MonoidHom.ext fun c => hfz (Ψ c)
  have hιC : baseChangeGL (fixSubfield σ).subtype g ∈ CQ σ i := by
    rw [CQ_eq_map]
    exact ⟨g, hg, rfl⟩
  have hgS : baseChangeGL (fixSubfield σ).subtype g ∈
      rootSpan τ GGL (componentRoots (rootCharHom a) i) :=
    CQ_le_rootSpan σ i hιC
  have hz'step : ∀ y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      S.D.step ((z * baseChangeGL (fixSubfield σ).subtype g) * y *
          (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹) =
        (z * baseChangeGL (fixSubfield σ).subtype g) * frobGL σ y *
          (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹ := by
    intro y hy
    have hfixg : frobGL σ (baseChangeGL (fixSubfield σ).subtype g) =
        baseChangeGL (fixSubfield σ).subtype g :=
      frobGL_eq_self_of_mem_CQ σ i hιC
    have h1 := hzstep _ (mul_mem (mul_mem hgS hy) (inv_mem hgS))
    have h2 : frobGL σ (baseChangeGL (fixSubfield σ).subtype g * y *
        (baseChangeGL (fixSubfield σ).subtype g)⁻¹) =
        baseChangeGL (fixSubfield σ).subtype g * frobGL σ y *
          (baseChangeGL (fixSubfield σ).subtype g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hfixg]
    rw [h2] at h1
    have e1 : (z * baseChangeGL (fixSubfield σ).subtype g) * y *
        (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹ =
        z * (baseChangeGL (fixSubfield σ).subtype g * y *
          (baseChangeGL (fixSubfield σ).subtype g)⁻¹) * z⁻¹ := by group
    have e2 : (z * baseChangeGL (fixSubfield σ).subtype g) * frobGL σ y *
        (z * baseChangeGL (fixSubfield σ).subtype g)⁻¹ =
        z * (baseChangeGL (fixSubfield σ).subtype g * frobGL σ y *
          (baseChangeGL (fixSubfield σ).subtype g)⁻¹) * z⁻¹ := by group
    rw [e1, e2]
    exact h1
  have hneg : -γ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem γ hγ
  exact ⟨γ, hγ, z * baseChangeGL (fixSubfield σ).subtype g,
    mul_mem hzC (Subgroup.mem_sup_right (rootSpan_mono (fun _ hδ => hδ.1) hgS)),
    (rckPair_stable_fixed S σ _ hz'step (isRoot_of_mem_componentRoots hγ) hγ).1,
    (rckPair_stable_fixed S σ _ hz'step (isRoot_of_mem_componentRoots hneg) hneg).1,
    rckImage_eq_fixed S hfeq himg hz'step hγ, rckImage_eq_fixed S hfeq himg' hz'step hneg⟩

end CFSG.StandardType.RCKRP
