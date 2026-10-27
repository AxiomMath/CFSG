module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToral
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRank
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeKernelLarge
public import CFSG.LocalAnalysis.StandardType.GGE0ShapePairWeyl
public import Certificates.Certificate716800

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem context_kernel_data
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : Shape t f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
      (I : Subgroup (MulAut (ggG0 3 B x L D J)))
      (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
      (a : Fin 2 → Fin Tag.E6.rank → Ωˣ),
      (letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) ∧
      contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I ∧
      contextImage (ggG0 3 B x L D J) Bs ≤ I ∧
      contextImage (ggG0 3 B x L D J) D ≤ I ∧
      planeGroup a = realizedSubgroup R (contextImage (ggG0 3 B x L D J) D) ∧
      KernelContext R.setup
        (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B))
        (realizedSubgroup R (contextImage (ggG0 3 B x L D J) J)) a := by
  obtain ⟨Ω, hF, hA, h2, I, R, a, halg, hG1, hBs, hT, hsplit, htw, hD, heq, htoral⟩ :=
    context_toral_data hctx s1 hshape
  letI := hF
  letI := hA
  letI := h2
  refine ⟨Ω, hF, hA, h2, I, R, a, halg, hG1, hBs, hD, heq, ⟨htoral, ?_⟩⟩
  rcases hshape with ⟨rfl, hdiv⟩ | ⟨rfl, -⟩
  · exact Or.inl (split_context_rank hctx s1 hdiv R hBs)
  · exact Or.inr (twisted_context_root hctx s1 halg R hBs hT (htw rfl))

private theorem map_conj_one_eq_self {L : Type} [Field L] (E : Subgroup (ModGL .E6 L)) :
    E.map (MulAut.conj (1 : ModGL .E6 L)).toMonoidHom = E := by
  rw [map_one MulAut.conj]
  have h : MulEquiv.toMonoidHom (1 : MulAut (ModGL .E6 L)) = MonoidHom.id _ := by
    ext x
    rfl
  rw [h, Subgroup.map_id]

theorem context_to_model
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : Shape t f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
      (I : Subgroup (MulAut (ggG0 3 B x L D J)))
      (R : ShapeRealization (ggG0 3 B x L D J) I Ω),
      (letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) ∧
      contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I ∧
      RigidToralPlane (realizedSubgroup R (contextImage (ggG0 3 B x L D J) D)) := by
  obtain ⟨Ω, hF, hA, h2, I, R, a, halg, hG1, hBs, hD, heq, hkc⟩ :=
    context_kernel_data hctx s1 hshape
  letI := hF
  letI := hA
  letI := h2
  have hlarge : 6 < (familyKernel a).ncard := KernelContext.large hkc
  have hpwg : PairWeylGood a :=
    pairWeylGood_of_large_kernel a hkc.pair_exp
      (by simpa only [planeGroup] using hkc.D_card) hlarge
  refine ⟨Ω, hF, hA, h2, I, R, halg, hG1, ?_⟩
  refine ⟨a, 1, Subgroup.one_mem _, hkc.pair_exp, ?_, ?_, hpwg⟩
  · rw [map_conj_one_eq_self, ← heq]
    rfl
  · rw [← heq]
    exact hkc.D_card

end CFSG.StandardType
