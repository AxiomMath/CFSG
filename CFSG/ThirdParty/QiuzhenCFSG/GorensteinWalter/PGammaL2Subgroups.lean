module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

namespace CFSG
end CFSG
open CFSG

/-!
# Linear layers of subgroups of `PΓL₂`

The canonical `PSL₂` layer has relative index two in the canonical `PGL₂`
layer of `PΓL₂`.  For a subgroup `A ≤ PΓL₂`, the kernel of the restricted
field-automorphism projection is normal, and its index is the cardinality of
the projection range.

Consequently, if `A` contains the canonical `PSL₂` layer and its field image
has odd order, this kernel is a normal odd-index subgroup of `A` isomorphic to
either `PSL₂` or `PGL₂`.  This is the formal endpoint needed after the two
remaining hard inputs in Gorenstein--Walter Lemma 3.3(vi): automorphism
recognition and oddness of the field-automorphism image.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped MatrixGroups

/-- The canonical `PGL₂(K)` layer inside `PΓL₂(K)`. -/
@[expose]
public def pGammaL2PGLRange
    (K : Type u) [CommRing K] : Subgroup (PGammaL2 K) :=
  (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range

/-- The named canonical PGL₂ layer is normal. -/
public instance pGammaL2PGLRange_normal
    (K : Type u) [CommRing K] :
    (pGammaL2PGLRange K).Normal := by
  unfold pGammaL2PGLRange
  infer_instance

/-- The canonical `PSL₂(K)` layer inside `PΓL₂(K)`. -/
@[expose]
public def pGammaL2PSLRange
    (K : Type u) [Field K] : Subgroup (PGammaL2 K) :=
  ((SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K))).range

/-- The canonical PGL₂ layer is naturally equivalent to `PGL₂(K)`. -/
@[expose]
public def pGammaL2PGLRangeEquiv
    (K : Type u) [CommRing K] : PGL2 K ≃* pGammaL2PGLRange K := by
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  exact MulEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab =>
        SemidirectProduct.inl_injective (congrArg Subtype.val hab),
      i.rangeRestrict_surjective⟩

@[simp]
public theorem pGammaL2PGLRangeEquiv_coe
    (K : Type u) [CommRing K] (g : PGL2 K) :
    ((pGammaL2PGLRangeEquiv K g : pGammaL2PGLRange K) : PGammaL2 K) =
      SemidirectProduct.inl g := rfl

/-- The canonical PSL₂ layer is naturally equivalent to `PSL₂(K)`. -/
@[expose]
public def pGammaL2PSLRangeEquiv
    (K : Type u) [Field K] : PSL2 K ≃* pGammaL2PSLRange K := by
  let f : PSL2 K →* PGammaL2 K :=
    (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K))
  exact MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _a _b hab =>
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (SemidirectProduct.inl_injective (congrArg Subtype.val hab)),
      f.rangeRestrict_surjective⟩

@[simp]
public theorem pGammaL2PSLRangeEquiv_coe
    (K : Type u) [Field K] (y : PSL2 K) :
    ((pGammaL2PSLRangeEquiv K y : pGammaL2PSLRange K) : PGammaL2 K) =
      SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := rfl

/-- Membership in the canonical PSL₂ layer has an explicit PSL₂
representative. -/
public theorem mem_pGammaL2PSLRange_iff
    (K : Type u) [Field K] (x : PGammaL2 K) :
    x ∈ pGammaL2PSLRange K ↔
      ∃ y : PSL2 K,
        SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL y) = x := by
  constructor
  · intro hx
    let xH : pGammaL2PSLRange K := ⟨x, hx⟩
    refine ⟨(pGammaL2PSLRangeEquiv K).symm xH, ?_⟩
    have h := congrArg Subtype.val
      ((pGammaL2PSLRangeEquiv K).apply_symm_apply xH)
    calc
      SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL
            ((pGammaL2PSLRangeEquiv K).symm xH)) =
          ((pGammaL2PSLRangeEquiv K
            ((pGammaL2PSLRangeEquiv K).symm xH) :
              pGammaL2PSLRange K) : PGammaL2 K) :=
        (pGammaL2PSLRangeEquiv_coe K _).symm
      _ = x := h
  · rintro ⟨y, rfl⟩
    exact (pGammaL2PSLRangeEquiv K y).property

/-- The field-automorphism projection restricted to a subgroup of `PΓL₂`. -/
@[expose]
public def pGammaL2FieldProjection
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K)) : A →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp A.subtype

/-- The projective-linear kernel of a subgroup of `PΓL₂`. -/
public def pGammaL2LinearKernel
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K)) : Subgroup A :=
  (pGammaL2FieldProjection K A).ker

@[simp]
public theorem mem_pGammaL2LinearKernel_iff
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K)) (x : A) :
    x ∈ pGammaL2LinearKernel K A ↔
      pGammaL2FieldProjection K A x = 1 := by
  exact MonoidHom.mem_ker

public instance pGammaL2LinearKernel_normal
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K)) :
    (pGammaL2LinearKernel K A).Normal := by
  change (pGammaL2FieldProjection K A).ker.Normal
  infer_instance

/-- The index of the projective-linear kernel is the cardinality of the
restricted field-automorphism image. -/
public theorem pGammaL2LinearKernel_index_eq_card_range
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K)) :
    (pGammaL2LinearKernel K A).index =
      Nat.card (pGammaL2FieldProjection K A).range := by
  change (pGammaL2FieldProjection K A).ker.index = _
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr
    (QuotientGroup.quotientKerEquivRange
      (pGammaL2FieldProjection K A)).toEquiv

/-- An odd field-automorphism image gives the projective-linear kernel odd
index. -/
public theorem pGammaL2LinearKernel_index_odd
    (K : Type u) [CommRing K]
    (A : Subgroup (PGammaL2 K))
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range)) :
    Odd (pGammaL2LinearKernel K A).index := by
  rw [pGammaL2LinearKernel_index_eq_card_range]
  exact hodd

/-- The canonical PSL₂ layer has relative index two in the canonical PGL₂
layer of `PΓL₂`. -/
public theorem pGammaL2_psl_range_relIndex_pgl_eq_two
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (pGammaL2PSLRange K).relIndex (pGammaL2PGLRange K) = 2 := by
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  let t : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  change (i.comp t).range.relIndex i.range = 2
  rw [← MonoidHom.map_range]
  have htop : i.range = (⊤ : Subgroup (PGL2 K)).map i := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subgroup.mem_top y, rfl⟩
    · rintro ⟨y, _hy, rfl⟩
      exact ⟨y, rfl⟩
  rw [htop]
  rw [Subgroup.relIndex_map_map_of_injective t.range ⊤
    SemidirectProduct.inl_injective]
  rw [Subgroup.relIndex_top_right]
  exact pgl2_psl2Range_index_eq_two K hK

/-- A subgroup of `PΓL₂(K)` containing the canonical PSL₂ layer and having
odd field-automorphism image has a normal odd-index subgroup isomorphic to
`PSL₂(K)` or `PGL₂(K)`. -/
public theorem pGammaL2_linear_kernel_normal_odd_index_iso_psl_or_pgl
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range)) :
    ∃ L : Subgroup A, L.Normal ∧ Odd L.index ∧
      (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) := by
  let L : Subgroup A := pGammaL2LinearKernel K A
  let M : Subgroup (PGammaL2 K) := L.map A.subtype
  have hHM : pGammaL2PSLRange K ≤ M := by
    intro x hx
    have hxA : x ∈ A := hPSL hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    change pGammaL2FieldProjection K A ⟨x, hxA⟩ = 1
    rcases hx with ⟨y, rfl⟩
    simp [pGammaL2FieldProjection]
  have hMP : M ≤ pGammaL2PGLRange K := by
    rintro _x ⟨a, ha, rfl⟩
    change (a : PGammaL2 K) ∈ pGammaL2PGLRange K
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    change SemidirectProduct.rightHom (a : PGammaL2 K) = 1
    exact ha
  have hrel :
      (pGammaL2PSLRange K).relIndex (pGammaL2PGLRange K) = 2 :=
    pGammaL2_psl_range_relIndex_pgl_eq_two K hK
  have hmul := Subgroup.relIndex_mul_relIndex
    (pGammaL2PSLRange K) M (pGammaL2PGLRange K) hHM hMP
  rw [hrel] at hmul
  have hcase : (pGammaL2PSLRange K).relIndex M = 1 ∨
      M.relIndex (pGammaL2PGLRange K) = 1 := by
    have hdiv : (pGammaL2PSLRange K).relIndex M ∣ 2 :=
      ⟨M.relIndex (pGammaL2PGLRange K), hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hleft | hleft
    · exact Or.inl hleft
    · right
      rw [hleft] at hmul
      omega
  have hM : M = pGammaL2PSLRange K ∨ M = pGammaL2PGLRange K := by
    rcases hcase with hleft | hright
    · left
      apply le_antisymm
      · exact Subgroup.relIndex_eq_one.mp hleft
      · exact hHM
    · right
      apply le_antisymm
      · exact hMP
      · exact Subgroup.relIndex_eq_one.mp hright
  have hLnormal : L.Normal := inferInstance
  have hLodd : Odd L.index := pGammaL2LinearKernel_index_odd K A hodd
  let eL : L ≃* M := L.equivMapOfInjective A.subtype A.subtype_injective
  refine ⟨L, hLnormal, hLodd, ?_⟩
  rcases hM with hMpsl | hMpgl
  · left
    rw [hMpsl] at eL
    exact ⟨eL.trans (pGammaL2PSLRangeEquiv K).symm⟩
  · right
    rw [hMpgl] at eL
    exact ⟨eL.trans (pGammaL2PGLRangeEquiv K).symm⟩

/-- Pull the projective-linear kernel package back through a faithful
embedding into `PΓL₂(K)`. -/
public theorem exists_normal_odd_index_iso_psl_or_pgl_of_pGammaL2_embedding
    {R : Type u} [Group R] [Finite R]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (f : R →* PGammaL2 K) (hf : Function.Injective f)
    (hPSL : pGammaL2PSLRange K ≤ f.range)
    (hodd : Odd
      (Nat.card (pGammaL2FieldProjection K f.range).range)) :
    ∃ L : Subgroup R, L.Normal ∧ Odd L.index ∧
      (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) := by
  rcases pGammaL2_linear_kernel_normal_odd_index_iso_psl_or_pgl
      K hK f.range hPSL hodd with
    ⟨M, hMnormal, hModd, hMmodel⟩
  let eR : R ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨fun a b hab => hf (congrArg Subtype.val hab),
        f.rangeRestrict_surjective⟩
  let L : Subgroup R := M.map eR.symm.toMonoidHom
  have hLnormal : L.Normal := by
    simpa [L] using
      (hMnormal.map eR.symm.toMonoidHom eR.symm.surjective)
  have hLodd : Odd L.index := by
    change Odd (M.map eR.symm.toMonoidHom).index
    rw [Subgroup.index_map]
    have hker : eR.symm.toMonoidHom.ker = ⊥ :=
      MonoidHom.ker_eq_bot eR.symm.toMonoidHom eR.symm.injective
    have hrange : eR.symm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr eR.symm.surjective
    rw [hker, hrange, Subgroup.index_top, mul_one, sup_bot_eq]
    exact hModd
  let eM : M ≃* L := by
    simpa [L] using
      (M.equivMapOfInjective eR.symm.toMonoidHom eR.symm.injective)
  refine ⟨L, hLnormal, hLodd, ?_⟩
  rcases hMmodel with hMpsl | hMpgl
  · exact Or.inl ⟨eM.symm.trans hMpsl.some⟩
  · exact Or.inr ⟨eM.symm.trans hMpgl.some⟩

end CFSG.GorensteinWalter
