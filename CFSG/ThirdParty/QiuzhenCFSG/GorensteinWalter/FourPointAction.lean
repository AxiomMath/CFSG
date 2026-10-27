module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Units.Equiv

namespace CFSG
end CFSG
open CFSG

/-!
# Faithful four-point actions for split normal Klein-four extensions

The four-group step in Proposition 9 uses the affine action of a split
extension `V₄ ⋊ K` on its normal four-group.  The source argument supplies the
split/self-centralizing context immediately before the sentence; a bare normal
Klein-four subgroup is not enough.  This module isolates the constructive
action and leaves those source-specific hypotheses explicit.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## The affine action of a semidirect product -/

private theorem affine_action_of_injective_action
    {H K : Type u} [Group H] [Group K]
    (φ : K →* MulAut H) (hφ : Function.Injective φ) :
    ∃ ψ : (H ⋊[φ] K) →* Equiv.Perm H, Function.Injective ψ := by
  let affineSmul : (H ⋊[φ] K) → H → H := fun z x => z.left * (φ z.right) x
  let : SMul (H ⋊[φ] K) H := ⟨affineSmul⟩
  let : MulAction (H ⋊[φ] K) H :=
    { smul := affineSmul
      one_smul := by
        intro x
        change affineSmul (1 : H ⋊[φ] K) x = x
        dsimp [affineSmul]
        simp
      mul_smul := by
        intro a b x
        change affineSmul (a * b) x = affineSmul a (affineSmul b x)
        dsimp [affineSmul]
        rw [map_mul, MulAut.mul_apply, (φ a.right).map_mul]
        rw [mul_assoc] }
  let : FaithfulSMul (H ⋊[φ] K) H :=
    ⟨by
      intro x y hxy
      apply SemidirectProduct.ext
      · have h1 := hxy (1 : H)
        change x.left * (φ x.right) (1 : H) =
          y.left * (φ y.right) (1 : H) at h1
        simpa using h1
      · have hleft : x.left = y.left := by
          have h1 := hxy (1 : H)
          change x.left * (φ x.right) (1 : H) =
            y.left * (φ y.right) (1 : H) at h1
          simpa using h1
        have hpermeq : ∀ z : H, (φ x.right) z = (φ y.right) z := by
          intro z
          have hz := hxy (x.left⁻¹ * (x.left * z))
          change x.left * (φ x.right) (x.left⁻¹ * (x.left * z)) =
            y.left * (φ y.right) (x.left⁻¹ * (x.left * z)) at hz
          simp only [hleft, inv_mul_cancel_left] at hz
          exact mul_left_cancel hz
        apply hφ
        apply MulEquiv.ext
        exact hpermeq⟩
  exact ⟨MulAction.toPermHom (H ⋊[φ] K) H, MulAction.toPerm_injective⟩

/-! ## The canonical conjugation action on a normal subgroup -/

/-- The action of a subgroup on a normal subgroup by restriction of
conjugation.  The normality instance makes the inclusion into the normalizer
canonical, so this homomorphism is the one used by
`SemidirectProduct.mulEquivSubgroup`. -/
public def normalSubgroupConj
    {G : Type u} [Group G] (H K : Subgroup G) [H.Normal] :
    (↥K) →* MulAut (↥H) :=
  H.normalizerMonoidHom.comp
    (Subgroup.inclusion (H := K) (K := Subgroup.normalizer (H : Set G))
      (by rw [H.normalizer_eq_top]; exact le_top))

/-! ## Ambient transport to `Fin 4` -/

/-- A split normal Klein-four extension has a faithful permutation action on
four points, provided the restricted conjugation action of the complement on
the normal four-group is faithful. -/
public theorem faithful_four_point_action_of_split_normal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hHnormal : H.Normal)
    (hH : IsKleinFour H) (hcomp : H.IsComplement' K)
    (hact : Function.Injective (normalSubgroupConj H K)) :
    ∃ ψ : G →* Equiv.Perm (Fin 4), Function.Injective ψ := by
  let : H.Normal := hHnormal
  let φ : (↥K) →* MulAut (↥H) := normalSubgroupConj H K
  rcases affine_action_of_injective_action φ hact with ⟨aff, haff⟩
  let eS : (↥H ⋊[φ] ↥K) ≃* G := SemidirectProduct.mulEquivSubgroup hcomp
  let eFin : (↥H) ≃ Fin 4 := Finite.equivFinOfCardEq hH.card_four
  let ψ : G →* Equiv.Perm (Fin 4) :=
    (eFin.permCongrHom.toMonoidHom.comp aff).comp eS.symm.toMonoidHom
  refine ⟨ψ, ?_⟩
  intro x y hxy
  apply eS.symm.injective
  apply haff
  apply eFin.permCongrHom.injective
  exact hxy

/-! ## A direct centralizer specialization -/

/-- If the centralizer of a normal Klein-four subgroup is contained in the
subgroup itself, then the restricted conjugation action of a complement is
faithful.  This is the form needed by the split-extension construction; the
usual self-centralizing hypothesis is the special case where the containment
is an equality. -/
public theorem faithful_four_point_action_of_centralizer_le_split_normal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hHnormal : H.Normal)
    (hH : IsKleinFour H) (hcomp : H.IsComplement' K)
    (hcent : Subgroup.centralizer (H : Set G) ≤ H) :
    ∃ ψ : G →* Equiv.Perm (Fin 4), Function.Injective ψ := by
  let : H.Normal := hHnormal
  have hconjmap : ∀ a : ↥K,
      normalSubgroupConj H K a = MulAut.conjNormal (a : G) := by
    intro a
    apply MulEquiv.ext
    intro h
    apply Subtype.ext
    simp only [normalSubgroupConj, Subgroup.normalizerMonoidHom,
      MulDistribMulAction.toMulAut, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, Function.comp_apply, MulDistribMulAction.toMulEquiv_apply]
    change ((Subgroup.inclusion (H := K)
        (K := Subgroup.normalizer (H : Set G)) _) a : G) * (h : G) *
        ((Subgroup.inclusion (H := K)
          (K := Subgroup.normalizer (H : Set G)) _) a : G)⁻¹ = _
    rfl
  have hact : Function.Injective (normalSubgroupConj H K) := by
    intro a b hab
    have hcentral : (a : G)⁻¹ * (b : G) ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hab' := DFunLike.congr_fun hab ⟨h, hh⟩
      rw [hconjmap a, hconjmap b] at hab'
      have hconj : (a : G) * h * (a : G)⁻¹ =
          (b : G) * h * (b : G)⁻¹ := by
        simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hab'
      have hconj' := congrArg (fun x : G => (a : G)⁻¹ * x * (b : G)) hconj
      simpa [mul_assoc] using hconj'
    have hcentralH : (a : G)⁻¹ * (b : G) ∈ H := hcent hcentral
    have hKmem : (a : G)⁻¹ * (b : G) ∈ K :=
      K.mul_mem (K.inv_mem a.property) b.property
    have hone : (a : G)⁻¹ * (b : G) = 1 :=
      (Subgroup.disjoint_def.mp hcomp.disjoint) hcentralH hKmem
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  exact faithful_four_point_action_of_split_normal_kleinFour H K hHnormal hH hcomp hact

/-! ## A direct self-centralizing specialization -/

/-- A self-centralizing normal Klein-four subgroup supplies the faithful
restricted conjugation action needed by the split-extension construction when
a complement is given. -/
public theorem faithful_four_point_action_of_selfCentralizing_split_normal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hHnormal : H.Normal)
    (hH : IsKleinFour H) (hcomp : H.IsComplement' K)
    (hcent : Subgroup.centralizer (H : Set G) = H) :
    ∃ ψ : G →* Equiv.Perm (Fin 4), Function.Injective ψ := by
  apply faithful_four_point_action_of_centralizer_le_split_normal_kleinFour
    H K hHnormal hH hcomp
  rw [hcent]

end CFSG.GorensteinWalter
