module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Projective linear groups under coefficient-ring equivalence

An equivalence of commutative coefficient rings induces equivalences of the
corresponding special/general linear groups and hence of `PSL₂` and `PGL₂`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

private def sl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃*
      Matrix.SpecialLinearGroup (Fin 2) S := by
  let f : Matrix.SpecialLinearGroup (Fin 2) R →*
      Matrix.SpecialLinearGroup (Fin 2) S :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) S →*
      Matrix.SpecialLinearGroup (Fin 2) R :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    simp [f, g]
  · ext x i j
    simp [f, g]

/-- `PSL₂` is invariant under equivalence of its coefficient rings. -/
public def psl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : PSL2 R ≃* PSL2 S := by
  let eSL : Matrix.SpecialLinearGroup (Fin 2) R ≃*
      Matrix.SpecialLinearGroup (Fin 2) S := sl2RingEquiv e
  apply QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) eSL
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    obtain ⟨w, rfl⟩ := eSL.surjective z
    simpa using congrArg eSL (hy w)
  · intro hx
    refine ⟨eSL.symm x, ?_, eSL.apply_symm_apply x⟩
    intro z
    apply eSL.injective
    simpa using hx (eSL z)

/-- `psl2RingEquiv` applies the coefficient equivalence entrywise to a
special-linear representative. -/
@[simp]
public theorem psl2RingEquiv_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    psl2RingEquiv e (QuotientGroup.mk' (Subgroup.center _) x) =
      QuotientGroup.mk' (Subgroup.center _)
        (Matrix.SpecialLinearGroup.map e.toRingHom x) := by
  rfl

/-- Entrywise transport by the identity coefficient equivalence is the
identity on `PSL₂`. -/
@[simp]
public theorem psl2RingEquiv_one
    (R : Type u) [CommRing R] :
    psl2RingEquiv (1 : R ≃+* R) = 1 := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

/-- Entrywise transport respects composition of coefficient automorphisms. -/
@[simp]
public theorem psl2RingEquiv_mul
    {R : Type u} [CommRing R] (e f : R ≃+* R) :
    psl2RingEquiv (e * f) = psl2RingEquiv e * psl2RingEquiv f := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

private def gl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.GeneralLinearGroup (Fin 2) R ≃*
      Matrix.GeneralLinearGroup (Fin 2) S := by
  let f : Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 2) S :=
    Matrix.GeneralLinearGroup.map e.toRingHom
  let g : Matrix.GeneralLinearGroup (Fin 2) S →*
      Matrix.GeneralLinearGroup (Fin 2) R :=
    Matrix.GeneralLinearGroup.map e.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    simp [f, g]
  · ext x i j
    simp [f, g]

/-- `PGL₂` is invariant under equivalence of its coefficient rings. -/
public def pgl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : PGL2 R ≃* PGL2 S := by
  let eGL : Matrix.GeneralLinearGroup (Fin 2) R ≃*
      Matrix.GeneralLinearGroup (Fin 2) S := gl2RingEquiv e
  apply QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) eGL
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    obtain ⟨w, rfl⟩ := eGL.surjective z
    simpa using congrArg eGL (hy w)
  · intro hx
    refine ⟨eGL.symm x, ?_, eGL.apply_symm_apply x⟩
    intro z
    apply eGL.injective
    simpa using hx (eGL z)

/-- `pgl2RingEquiv` applies the coefficient equivalence entrywise to a
general-linear representative. -/
@[simp]
public theorem pgl2RingEquiv_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : Matrix.GeneralLinearGroup (Fin 2) R) :
    pgl2RingEquiv e (QuotientGroup.mk' (Subgroup.center _) x) =
      QuotientGroup.mk' (Subgroup.center _)
        (Matrix.GeneralLinearGroup.map e.toRingHom x) := by
  rfl

/-- Entrywise transport by the identity coefficient equivalence is the
identity on `PGL₂`. -/
@[simp]
public theorem pgl2RingEquiv_one
    (R : Type u) [CommRing R] :
    pgl2RingEquiv (1 : R ≃+* R) = 1 := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

/-- Entrywise transport respects composition of coefficient automorphisms. -/
@[simp]
public theorem pgl2RingEquiv_mul
    {R : Type u} [CommRing R] (e f : R ≃+* R) :
    pgl2RingEquiv (e * f) = pgl2RingEquiv e * pgl2RingEquiv f := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

end CFSG.GorensteinWalter
