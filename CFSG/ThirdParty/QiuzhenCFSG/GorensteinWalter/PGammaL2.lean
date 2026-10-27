module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedCoordinates
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.SemidirectProduct

namespace CFSG
end CFSG
open CFSG

/-!
# The projective semilinear group in dimension two

We define

`PΓL₂(K) = PGL₂(K) ⋊ Aut(K)`

using the entrywise coefficient action.  The canonical `PGL₂` layer is
normal, its quotient is the cyclic automorphism group of the finite field,
and the projective-linear and coefficient actions combine to a homomorphism
`PΓL₂(K) → Aut(PSL₂(K))`.

The projective-line reconstruction and affine-coordinate argument prove that
this last homomorphism is both injective and surjective.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped MatrixGroups

/-- The automorphism group of an odd-prime-power finite field is cyclic. -/
public theorem finiteField_ringAut_isCyclic_of_oddPrimePower
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    IsCyclic (K ≃+* K) := by
  rcases hK with ⟨p, n, hp, _hpOdd, _hn, hcard⟩
  let : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

/-- The dimension-two projective semilinear group. -/
public abbrev PGammaL2 (K : Type u) [CommRing K] :=
  PGL2 K ⋊[pgl2FieldAut K] (K ≃+* K)

/-- The canonical `PGL₂` layer is normal in `PΓL₂`. -/
public instance pGammaL2PGLRangeNormal
    (K : Type u) [CommRing K] :
    ((SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The quotient of `PΓL₂(K)` by its canonical `PGL₂(K)` layer is
the coefficient automorphism group. -/
public def pGammaL2QuotientPGL2
    (K : Type u) [CommRing K] :
    PGammaL2 K ⧸ (SemidirectProduct.inl :
      PGL2 K →* PGammaL2 K).range ≃* (K ≃+* K) := by
  let N : Subgroup (PGammaL2 K) :=
    (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range
  let q : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom
  have hNker : N = q.ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  letI : N.Normal := hNker ▸ inferInstance
  exact (QuotientGroup.quotientMulEquivOfEq hNker).trans
    (QuotientGroup.quotientKerEquivOfRightInverse
      (φ := q)
      (SemidirectProduct.inr : (K ≃+* K) → PGammaL2 K)
      SemidirectProduct.rightHom_inr)

/-- The field-automorphism quotient of `PΓL₂(K)` is cyclic. -/
public theorem pGammaL2_quotient_pgl_isCyclic
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    IsCyclic (PGammaL2 K ⧸ (SemidirectProduct.inl :
      PGL2 K →* PGammaL2 K).range) := by
  exact (pGammaL2QuotientPGL2 K).isCyclic.mpr
    (finiteField_ringAut_isCyclic_of_oddPrimePower K hK)

/-- Coefficient automorphisms conjugate the projective-linear action in the
same way that they conjugate `PGL₂` itself. -/
public theorem pgl2InnerAutPSL2_fieldAut
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) :
    (pgl2InnerAutPSL2 K hK hcard).comp
        (((pgl2FieldAut K) sigma).toMonoidHom) =
      (MulAut.conj ((psl2FieldAut K) sigma)).toMonoidHom.comp
        (pgl2InnerAutPSL2 K hK hcard) := by
  ext g x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (pgl2InnerAutPSL2 K hK hcard ((pgl2FieldAut K) sigma g) x) =
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (MulAut.conj ((psl2FieldAut K) sigma)
        (pgl2InnerAutPSL2 K hK hcard g) x)
  rw [toPGL_pgl2InnerAutPSL2_apply]
  rw [MulAut.conj_apply]
  rw [← map_inv (psl2FieldAut K) sigma]
  rw [MulAut.mul_apply, MulAut.mul_apply]
  symm
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((psl2FieldAut K) sigma
        (pgl2InnerAutPSL2 K hK hcard g
          ((psl2FieldAut K) sigma⁻¹ x))) = _
  rw [psl2FieldAut_toPGL]
  rw [toPGL_pgl2InnerAutPSL2_apply]
  rw [psl2FieldAut_toPGL]
  simp

/-- The projective-linear and coefficient actions combine to an action of
`PΓL₂(K)` on `PSL₂(K)`. -/
public def pGammaL2ToMulAutPSL2
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    PGammaL2 K →* MulAut (PSL2 K) :=
  SemidirectProduct.lift
    (pgl2InnerAutPSL2 K hK hcard) (psl2FieldAut K)
    (pgl2InnerAutPSL2_fieldAut K hK hcard)

@[simp]
public theorem pGammaL2ToMulAutPSL2_inl
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (g : PGL2 K) :
    pGammaL2ToMulAutPSL2 K hK hcard
        (SemidirectProduct.inl g) =
      pgl2InnerAutPSL2 K hK hcard g := by
  simp [pGammaL2ToMulAutPSL2]

@[simp]
public theorem pGammaL2ToMulAutPSL2_inr
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) :
    pGammaL2ToMulAutPSL2 K hK hcard
        (SemidirectProduct.inr sigma) =
      psl2FieldAut K sigma := by
  simp [pGammaL2ToMulAutPSL2]

private def unitTransvectionPSL
    (K : Type u) [Field K] (i j : Fin 2) (hij : i ≠ j) : PSL2 K :=
  QuotientGroup.mk' (Subgroup.center _)
    (Matrix.SpecialLinearGroup.transvection hij 1)

/-- A projective linear transformation that commutes with the two unit
upper/lower transvections is trivial. -/
private theorem pgl2_eq_one_of_commutes_unit_transvections
    (K : Type u) [Field K]
    (g : PGL2 K)
    (hU : Commute g
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (unitTransvectionPSL K 0 1 (by decide))))
    (hL : Commute g
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (unitTransvectionPSL K 1 0 (by decide)))) :
    g = 1 := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      let U : Matrix.SpecialLinearGroup (Fin 2) K :=
        Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 2) ≠ 1 by decide) 1
      let L : Matrix.SpecialLinearGroup (Fin 2) K :=
        Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 2) ≠ 0 by decide) 1
      have hUq :
          Matrix.ProjGenLinGroup.mk
              (A * Matrix.SpecialLinearGroup.toGL U) =
            Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL U * A) := by
        rw [map_mul, map_mul]
        simpa [unitTransvectionPSL, U] using hU.eq
      have hLq :
          Matrix.ProjGenLinGroup.mk
              (A * Matrix.SpecialLinearGroup.toGL L) =
            Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL L * A) := by
        rw [map_mul, map_mul]
        simpa [unitTransvectionPSL, L] using hL.eq
      rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hUq with ⟨r, hr⟩
      rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hLq with ⟨s, hs⟩
      have hU10 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 1 0)) hr
      have hU11 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 1 1)) hr
      have hr1 : (r : K) = 1 := by
        by_contra hrne
        have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
          by_contra hcne
          apply hrne
          apply mul_left_cancel₀ hcne
          simpa [U, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hU10
        have hd : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
          by_contra hdne
          apply hrne
          apply mul_left_cancel₀ hdne
          simpa [U, hc, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hU11
        apply A.det_ne_zero
        apply Matrix.det_eq_zero_of_row_eq_zero 1
        intro j
        fin_cases j <;> assumption
      have hU00 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) hr
      have hU01 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 0 1)) hr
      have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
        simpa [U, hr1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] using hU00
      have had : (A : Matrix (Fin 2) (Fin 2) K) 0 0 =
          (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
        have h := hU01
        simp [U, hr1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] at h
        apply add_right_cancel
          (b := (A : Matrix (Fin 2) (Fin 2) K) 0 1)
        simpa [add_comm] using h
      have hL00 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) hs
      have hL01 := congrArg (fun B : GL (Fin 2) K ↦
        ((B : Matrix (Fin 2) (Fin 2) K) 0 1)) hs
      have hs1 : (s : K) = 1 := by
        by_contra hsne
        have hb : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
          by_contra hbne
          apply hsne
          apply mul_left_cancel₀ hbne
          simpa [L, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hL01
        have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
          by_contra hane
          apply hsne
          apply mul_left_cancel₀ hane
          simpa [L, hb, Matrix.GeneralLinearGroup.scalar,
            Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.mul_apply, Fin.sum_univ_two] using hL00
        apply A.det_ne_zero
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        fin_cases j <;> assumption
      have hb : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
        simpa [L, hs1, Matrix.GeneralLinearGroup.scalar,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Fin.sum_univ_two] using hL00
      refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, hb, hc, had]

private theorem psl2FieldAut_unitTransvectionPSL
    (K : Type u) [Field K] (sigma : K ≃+* K)
    (i j : Fin 2) (hij : i ≠ j) :
    psl2FieldAut K sigma (unitTransvectionPSL K i j hij) =
      unitTransvectionPSL K i j hij := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center _)
        (Matrix.SpecialLinearGroup.transvection hij 1)) = _
  rw [psl2RingEquiv_mk]
  congr 1
  ext a b
  by_cases h : i = a ∧ j = b <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, h]

/-- The canonical projective-semilinear action on `PSL₂(K)` is faithful. -/
public theorem pGammaL2ToMulAutPSL2_injective
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Injective (pGammaL2ToMulAutPSL2 K hK hcard) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' :
      pgl2InnerAutPSL2 K hK hcard x.left *
          psl2FieldAut K x.right = 1 := by
    have hdecomp := SemidirectProduct.inl_left_mul_inr_right x
    have h := congrArg (pGammaL2ToMulAutPSL2 K hK hcard) hdecomp
    rw [map_mul, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr] at h
    exact h.trans (MonoidHom.mem_ker.mp hx)
  let U : PSL2 K :=
    unitTransvectionPSL K 0 1 (by decide)
  let L : PSL2 K :=
    unitTransvectionPSL K 1 0 (by decide)
  have hUfield : psl2FieldAut K x.right U = U := by
    exact psl2FieldAut_unitTransvectionPSL K x.right 0 1 (by decide)
  have hLfield : psl2FieldAut K x.right L = L := by
    exact psl2FieldAut_unitTransvectionPSL K x.right 1 0 (by decide)
  have hUfix : pgl2InnerAutPSL2 K hK hcard x.left U = U := by
    have h := congrArg (fun f : MulAut (PSL2 K) ↦ f U) hx'
    simpa [hUfield] using h
  have hLfix : pgl2InnerAutPSL2 K hK hcard x.left L = L := by
    have h := congrArg (fun f : MulAut (PSL2 K) ↦ f L) hx'
    simpa [hLfield] using h
  have hUconj :
      x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL U * x.left⁻¹ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL U := by
    rw [← toPGL_pgl2InnerAutPSL2_apply K hK hcard]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hUfix
  have hLconj :
      x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL L * x.left⁻¹ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL L := by
    rw [← toPGL_pgl2InnerAutPSL2_apply K hK hcard]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hLfix
  have hUcomm : Commute x.left
      (Matrix.ProjectiveSpecialLinearGroup.toPGL U) := by
    rw [Commute]
    calc
      x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL U =
          (x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL U * x.left⁻¹) *
            x.left := by group
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL U * x.left := by
        rw [hUconj]
  have hLcomm : Commute x.left
      (Matrix.ProjectiveSpecialLinearGroup.toPGL L) := by
    rw [Commute]
    calc
      x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL L =
          (x.left * Matrix.ProjectiveSpecialLinearGroup.toPGL L * x.left⁻¹) *
            x.left := by group
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL L * x.left := by
        rw [hLconj]
  have hg : x.left = 1 :=
    pgl2_eq_one_of_commutes_unit_transvections K x.left hUcomm hLcomm
  have hsigmaAut : psl2FieldAut K x.right = 1 := by
    simpa [hg] using hx'
  have hsigma : x.right = 1 := by
    apply psl2FieldAut_injective K
    simpa using hsigmaAut
  apply SemidirectProduct.ext
  · exact hg
  · exact hsigma

/-- Every automorphism of `PSL₂(K)` over an odd finite field is induced by a
projective semilinear transformation. -/
public theorem pGammaL2ToMulAutPSL2_surjective
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard) := by
  intro alpha
  let g : PGL2 K := psl2MulAutNormalizerPGL K hKcard alpha
  let sigma : K ≃+* K :=
    psl2NormalizedAffineRingEquiv K hKcard hK hcard alpha
  refine ⟨SemidirectProduct.inl g⁻¹ * SemidirectProduct.inr sigma, ?_⟩
  rw [map_mul, pGammaL2ToMulAutPSL2_inl,
    pGammaL2ToMulAutPSL2_inr]
  have hnormalized :=
    psl2NormalizedMulAut_eq_fieldAut K hKcard hK hcard alpha
  rw [psl2NormalizedMulAut] at hnormalized
  change pgl2InnerAutPSL2 K hK hcard g * alpha =
    psl2FieldAut K sigma at hnormalized
  rw [map_inv]
  calc
    (pgl2InnerAutPSL2 K hK hcard g)⁻¹ * psl2FieldAut K sigma =
        (pgl2InnerAutPSL2 K hK hcard g)⁻¹ *
          (pgl2InnerAutPSL2 K hK hcard g * alpha) := by
      rw [hnormalized]
    _ = alpha := by group

end CFSG.GorensteinWalter
