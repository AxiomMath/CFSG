module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection

namespace CFSG
end CFSG
open CFSG

/-!
# Normal PSL₂ extensions inside `PΓL₂`

Assuming the classical surjectivity statement

`PΓL₂(K) → Aut(PSL₂(K))`,

conjugation on a self-centralizing normal subgroup `N ≃ PSL₂(K)` gives a
faithful embedding of the ambient group into `PΓL₂(K)`.  Its range contains
the canonical inner PSL₂ layer.  Combining this with the linear-kernel
package reduces the Gorenstein--Walter extension step to one further input:
oddness of the transported field-automorphism image.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The canonical semilinear action becomes an equivalence once surjectivity
is supplied. -/
@[expose] public def pGammaL2EquivMulAutPSL2
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard)) :
    PGammaL2 K ≃* MulAut (PSL2 K) :=
  MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hcard)
    ⟨pGammaL2ToMulAutPSL2_injective K hK hcard, hsurj⟩

/-- Conjugation on `N`, transported across an identification
`N ≃ PSL₂(K)`. -/
@[expose] public def normalPSL2ConjAction
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K]
    (e : N ≃* PSL2 K) : R →* MulAut (PSL2 K) :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))

/-- The explicit projective-semilinear embedding arising from conjugation on
a normal PSL₂ subgroup, assuming the semilinear automorphism theorem. -/
@[expose] public def normalPSL2ToPGammaL2
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard)) :
    R →* PGammaL2 K :=
  (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).symm.toMonoidHom.comp
    (normalPSL2ConjAction N K e)

/-- Conjugation on a normal subgroup is faithful when the subgroup
centralizer is trivial. -/
public theorem conjNormal_injective_of_centralizer_eq_bot
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (hC : Subgroup.centralizer (N : Set R) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := N)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hker : Subgroup.centralizer (N : Set R) =
      (MulAut.conjNormal (H := N)).ker := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      ext x
      rw [MulAut.conjNormal_apply]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hg) (x : R) x.2
      calc
        g * (x : R) * g⁻¹ = ((x : R) * g) * g⁻¹ := by rw [hcomm]
        _ = x := by group
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hval := congrArg (fun y : N => (y : R))
        (DFunLike.congr_fun hg ⟨x, hx⟩)
      change g * x * g⁻¹ = x at hval
      calc
        x * g = (g * x * g⁻¹) * g := by rw [hval]
        _ = g * x := by group
  rw [← hker, hC]

/-- The explicit normal-extension map to `PΓL₂` is faithful when the normal
PSL₂ core is self-centralizing. -/
public theorem normalPSL2ToPGammaL2_injective
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set R) = ⊥)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard)) :
    Function.Injective
      (normalPSL2ToPGammaL2 N K hK hcard e hsurj) := by
  exact (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).symm.injective.comp
    ((MulAut.congr e).injective.comp
      (conjNormal_injective_of_centralizer_eq_bot N hC))

private theorem mulAut_congr_conj
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr, MulAut.conj_apply]

/-- The range of the transported conjugation embedding contains the
canonical inner PSL₂ layer. -/
public theorem normalPSL2ToPGammaL2_range_contains_psl
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard)) :
    pGammaL2PSLRange K ≤
      (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range := by
  intro x hx
  rw [mem_pGammaL2PSLRange_iff] at hx
  rcases hx with ⟨y, rfl⟩
  let n : N := e.symm y
  refine ⟨(n : R), ?_⟩
  apply (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).injective
  simp only [normalPSL2ToPGammaL2, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change normalPSL2ConjAction N K e (n : R) =
    pGammaL2ToMulAutPSL2 K hK hcard
      (SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
  rw [pGammaL2ToMulAutPSL2_inl]
  rw [pgl2InnerAutPSL2_toPGL]
  change MulAut.congr e (MulAut.conjNormal (n : R)) = MulAut.conj y
  rw [MulAut.conjNormal_val]
  rw [mulAut_congr_conj]
  simp [n]

/-- For the transported conjugation embedding, dihedral Sylow structure
leaves exactly two possibilities: the field image is odd, or the
projective-linear kernel is the canonical PSL₂ layer. -/
public theorem normalPSL2Extension_fieldProjection_odd_or_linearKernel_eq_psl
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set R) = ⊥)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard)) :
    Odd (Nat.card
      (pGammaL2FieldProjection K
        (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range).range) ∨
      pGammaL2LinearKernel K
          (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range =
        (pGammaL2PSLRange K).subgroupOf
          (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range := by
  exact pGammaL2_embedding_field_projection_odd_or_linearKernel_eq_psl
    K hK hcard hSylow
    (normalPSL2ToPGammaL2 N K hK hcard e hsurj)
    (normalPSL2ToPGammaL2_injective N K hK hcard e hC hsurj)
    (normalPSL2ToPGammaL2_range_contains_psl N K hK hcard e hsurj)

/-- The normal-extension endpoint after supplying semilinear surjectivity and
oddness of the transported field-automorphism image. -/
public theorem normalPSL2Extension_linear_kernel
    {R : Type u} [Group R] [Finite R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set R) = ⊥)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))
    (hodd : Odd (Nat.card
      (pGammaL2FieldProjection K
        (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range).range)) :
    ∃ L : Subgroup R, L.Normal ∧ Odd L.index ∧
      (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) := by
  exact exists_normal_odd_index_iso_psl_or_pgl_of_pGammaL2_embedding
    K hK (normalPSL2ToPGammaL2 N K hK hcard e hsurj)
    (normalPSL2ToPGammaL2_injective N K hK hcard e hC hsurj)
    (normalPSL2ToPGammaL2_range_contains_psl N K hK hcard e hsurj)
    hodd

private theorem hasCyclicOrDihedral_of_hasDihedral
    {R : Type u} [Group R] (h : HasDihedralSylowTwo R) :
    HasCyclicOrDihedralSylowTwo R := by
  intro S
  exact Or.inr (h S)

/-- The `IsDGroup` endpoint after supplying the two remaining hard inputs:
semilinear surjectivity and oddness of the transported field image. -/
public theorem normalPSL2Extension_isDGroup
    {R : Type u} [Group R] [Finite R]
    (hSylow : HasDihedralSylowTwo R)
    (hO : pPrimeCore 2 R = ⊥)
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set R) = ⊥)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))
    (hodd : Odd (Nat.card
      (pGammaL2FieldProjection K
        (normalPSL2ToPGammaL2 N K hK hcard e hsurj).range).range)) :
    IsDGroup R := by
  rcases normalPSL2Extension_linear_kernel
      N K hK hcard e hC hsurj hodd with
    ⟨L, hLnormal, hLindex, hLmodel⟩
  let qE : (R ⧸ pPrimeCore 2 R) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq (G := R) hO).trans
      (QuotientGroup.quotientBot (G := R))
  let L' : Subgroup (R ⧸ pPrimeCore 2 R) := L.map qE.symm.toMonoidHom
  have hL'normal : L'.Normal := by
    simpa [L'] using
      (hLnormal.map qE.symm.toMonoidHom qE.symm.surjective)
  have hL'index : Odd L'.index := by
    change Odd (L.map qE.symm.toMonoidHom).index
    rw [Subgroup.index_map]
    have hker : qE.symm.toMonoidHom.ker = ⊥ :=
      MonoidHom.ker_eq_bot qE.symm.toMonoidHom qE.symm.injective
    have hrange : qE.symm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr qE.symm.surjective
    rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
    exact hLindex
  let eL : L ≃* L' := by
    simpa [L'] using
      (L.equivMapOfInjective qE.symm.toMonoidHom qE.symm.injective)
  refine IsDGroup.quotientHasLinearNormalSubgroup
    (hasCyclicOrDihedral_of_hasDihedral hSylow) K hK L' hL'normal hL'index ?_
  rcases hLmodel with hLpsl | hLpgl
  · exact Or.inl ⟨eL.symm.trans hLpsl.some⟩
  · exact Or.inr ⟨eL.symm.trans hLpgl.some⟩

end CFSG.GorensteinWalter
