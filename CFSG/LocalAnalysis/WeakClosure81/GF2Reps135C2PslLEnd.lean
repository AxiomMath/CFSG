module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
variable {L : Subgroup (MulAut W)} {G : Type} [Group G]

private lemma c2slle_LEnd_comm (φ : G →* ↥L) (ψ : ↥(LEnd L)) (g : G) (v : Additive W) :
    (ψ : Additive W →+ Additive W) (pslRep φ g v) =
      pslRep φ g ((ψ : Additive W →+ Additive W) v) :=
  ψ.2 (φ g) (φ g).2 v

private lemma c2slle_map_asAlgebraHom (φ : G →* ↥L) (ψ : Additive W →+ Additive W)
    (hψ : ∀ (g : G) (v : Additive W), ψ (pslRep φ g v) = pslRep φ g (ψ v))
    (a : MonoidAlgebra (ZMod 2) G) (v : Additive W) :
    ψ ((pslRep φ).asAlgebraHom a v) = (pslRep φ).asAlgebraHom a (ψ v) := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      rw [Representation.asAlgebraHom_of]
      exact hψ g v
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul r x hx =>
      simp only [map_smul, LinearMap.smul_apply, ZMod.map_smul, hx]

private lemma c2slle_smul_eq (φ : G →* ↥L) (a : MonoidAlgebra (ZMod 2) G)
    (x : (pslRep φ).asModule) :
    a • x = (pslRep φ).asAlgebraHom a x :=
  rfl

private lemma c2slle_of_smul (φ : G →* ↥L) (g : G) (x : (pslRep φ).asModule) :
    MonoidAlgebra.of (ZMod 2) G g • x = pslRep φ g x := by
  rw [c2slle_smul_eq, Representation.asAlgebraHom_of]

private noncomputable def c2slle_toEnd (φ : G →* ↥L) (ψ : ↥(LEnd L)) :
    Module.End (MonoidAlgebra (ZMod 2) G) (pslRep φ).asModule where
  toFun := fun x => (ψ : Additive W →+ Additive W) x
  map_add' := fun x y => (ψ : Additive W →+ Additive W).map_add x y
  map_smul' := fun a x => by
    rw [c2slle_smul_eq]
    exact c2slle_map_asAlgebraHom φ (ψ : Additive W →+ Additive W)
      (c2slle_LEnd_comm φ ψ) a x

private noncomputable def c2slle_ofEnd (φ : G →* ↥L) (hφ : Function.Surjective φ)
    (T : Module.End (MonoidAlgebra (ZMod 2) G) (pslRep φ).asModule) : ↥(LEnd L) :=
  ⟨(T : (pslRep φ).asModule →ₗ[ZMod 2] (pslRep φ).asModule).toAddMonoidHom, by
    intro l hl w
    obtain ⟨g, hg⟩ := hφ ⟨l, hl⟩
    have hgl : ((φ g : ↥L) : MulAut W) = l := congrArg Subtype.val hg
    have hT : ∀ x : (pslRep φ).asModule, T (pslRep φ g x) = pslRep φ g (T x) := by
      intro x
      rw [← c2slle_of_smul φ g x, T.map_smul, c2slle_of_smul φ g (T x)]
    rw [← hgl]
    exact hT w⟩

theorem w135c2_psl_lend_card {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (φ : G →* ↥L) (hφ : Function.Surjective φ) :
    Nat.card (LEnd L) =
      Nat.card (Module.End (MonoidAlgebra (ZMod 2) G) (pslRep φ).asModule) := by
  refine Nat.card_congr ?_
  exact
    { toFun := c2slle_toEnd φ
      invFun := c2slle_ofEnd φ hφ
      left_inv := by
        intro ψ
        apply Subtype.ext
        apply AddMonoidHom.ext
        intro v
        rfl
      right_inv := by
        intro T
        apply LinearMap.ext
        intro x
        rfl }

end CFSG.LocalAnalysis.WeakClosure81
