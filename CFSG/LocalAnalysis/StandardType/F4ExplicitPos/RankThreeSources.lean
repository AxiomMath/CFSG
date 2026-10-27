module
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart2

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal.Symplectic
  CFSG.LieType.RootSystem CFSG.Timmesfeld.LieEmbed CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.RankThreeModels
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.F4ExplicitPos.RationalC3 CFSG.StandardType.F4ExplicitPos.RationalB3
  CFSG.StandardType.F4ExplicitPos.NativePinFinal


private theorem lift_injective_of_range_map {U V W : Type} [Group U] [Group V] [Group W]
    (η : U →* W) (hη : Function.Injective η) (Q : Subgroup U)
    (Φ : V →* W) (hΦ : Function.Injective Φ) (hrange : Φ.range = Q.map η) :
    ∃ lam : V →* U, Function.Injective lam ∧ lam.range = Q ∧ η.comp lam = Φ := by
  let e := Q.equivMapOfInjective η hη
  let ΦQ := Φ.codRestrict (Q.map η) (fun x => hrange ▸ (show Φ x ∈ Φ.range from ⟨x, rfl⟩))
  let lam : V →* U := Q.subtype.comp (e.symm.toMonoidHom.comp ΦQ)
  have hcomp : η.comp lam = Φ := by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply (ΦQ x))
  have hinj : Function.Injective lam := by
    intro x y hxy
    apply hΦ
    rw [← DFunLike.congr_fun hcomp x, ← DFunLike.congr_fun hcomp y]
    exact congrArg η hxy
  have hr : lam.range = Q := by
    apply Subgroup.map_injective hη
    rw [← MonoidHom.range_comp, hcomp, hrange]
  exact ⟨lam, hinj, hr, hcomp⟩

theorem exists_sp6_source_of_rankThree
    {K Ω U : Type} [Field K] [Finite K] [CharP K 2] [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra K Ω] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω] [Group U]
    (η : U →* ModGL .F4 Ω) (hη : Function.Injective η) (Q : Subgroup U)
    {M : Type} [CommGroup M] (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (D : LangDatum .F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f) (hK : Nat.card K = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ) (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i)
    (h3 : compRank (componentRoots χ i) = 3) (h18 : (componentRoots χ i).ncard = 18)
    (hshape : (∃ v : WeylGroup .F4, componentRoots χ i = (fun α => v • α) '' C3Range.c3RootSet) ∨
      ∃ v : WeylGroup .F4, componentRoots χ i = (fun α => v • α) '' b3LeviRoots)
    (C : Subgroup (ModGL .F4 Ω)) (hHC : rootSpan .F4 Ω (componentRoots χ i) ≤ C)
    (hQ : IsComponentOf (Q.map η) (D.Γ ⊓ C)) (hle : Q.map η ≤ rootSpan .F4 Ω (componentRoots χ i)) :
    ∃ (σ : Ω ≃+* Ω) (z : ModGL .F4 Ω) (v : WeylGroup .F4)
      (Φ : CFSG.Open.StatedSp 3 K →* ModGL .F4 Ω) (lam : CFSG.Open.StatedSp 3 K →* U),
      (∀ c, σ c = c ^ D.q) ∧ z ∈ Zsub χ ∧ normalizesAll χ z ∧
      (∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
        D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
      Function.Injective lam ∧ lam.range = Q ∧ η.comp lam = Φ ∧
      ((componentRoots χ i = (fun α => v • α) '' C3Range.c3RootSet ∧
          Φ = (((MulAut.conj z).toMonoidHom.comp
            (conjIM Ω (canonicalRep (coxeterSystem .F4) Ω v))).comp
            (statedSpMap (algebraMap K Ω) 3))) ∨
        (componentRoots χ i = (fun α => v • α) '' b3LeviRoots ∧
          Φ = PhiB (K := K) Ω (canonicalRep (coxeterSystem .F4) Ω v) z)) := by
  rcases hshape with ⟨v, hv⟩ | ⟨v, hv⟩
  · obtain ⟨σ, z, Φ, hσ, hz, hn, _, hstep, hΦ, hΦinj, _, hΦrange⟩ :=
      RankThreeModels.f4_rankThree_c3_actual_model_producer Ω D f hf hq hK ρ hρ i
        hker hstable h3 h18 v hv C hHC (Q.map η) hQ hle
    obtain ⟨lam, hlam, hlamrange, hcomp⟩ := lift_injective_of_range_map η hη Q Φ hΦinj hΦrange.symm
    refine ⟨σ, z, v, Φ, lam, hσ, hz, hn, ?_, hlam, hlamrange, hcomp, Or.inl ⟨hv, hΦ⟩⟩
    intro g hg
    have hgH : g ∈ (conjIM Ω (canonicalRep (coxeterSystem .F4) Ω v)).range := by
      rw [range_conjIM_canonicalRep, ← hv]
      exact hg
    rw [frobGL_eq_bcGL]
    exact hstep g hgH
  · obtain ⟨σ, z, Φ, hσ, hz, hn, _, hstep, hΦ, hΦinj, _, hΦrange⟩ :=
      RankThreeModels.f4_rankThree_b3_actual_model_producer Ω D f hf hq hK ρ hρ i
        hker hstable h3 h18 v hv C hHC (Q.map η) hQ hle
    obtain ⟨lam, hlam, hlamrange, hcomp⟩ := lift_injective_of_range_map η hη Q Φ hΦinj hΦrange.symm
    refine ⟨σ, z, v, Φ, lam, hσ, hz, hn, ?_, hlam, hlamrange, hcomp, Or.inr ⟨hv, hΦ⟩⟩
    intro g hg
    have hgH : g ∈ (conjBM Ω (canonicalRep (coxeterSystem .F4) Ω v)).range := by
      rw [range_conjBM_canonicalRep, ← hv]
      exact hg
    rw [frobGL_eq_bcGL]
    exact hstep g hgH

end CFSG.StandardType.F4ExplicitPos
