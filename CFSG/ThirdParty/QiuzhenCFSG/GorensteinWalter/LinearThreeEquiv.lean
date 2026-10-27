module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.ZMod.Torsion

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# The small-field projective actions

The projective line over `𝔽₃` has four points.  Its natural actions give
faithful permutation representations of `PSL₂(3)` and `PGL₂(3)` on four
points.  Computing the orders of the two source groups identifies the first
image as the unique index-two subgroup `A₄` of `S₄`, and the second image as
all of `S₄`.

The implementation deliberately keeps the finite projective-line
enumeration abstract: `Fintype.equivFinOfCardEq` supplies an arbitrary
equivalence with `Fin 4`, while the index-two API identifies the resulting
image independently of that choice.
-/

noncomputable section

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace CFSG.GorensteinWalter

private abbrev F3 := ZMod 3
private abbrev X3 := ℙ F3 (Fin 2 → F3)
private abbrev PSL3 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F3
private abbrev PGL3 := Matrix.ProjGenLinGroup (Fin 2) F3

noncomputable instance : Fintype X3 := Fintype.ofFinite _

set_option maxRecDepth 100000 in
private lemma projectiveLine_three_card : Nat.card X3 = 4 := by
  rw [Projectivization.card_of_finrank_two]
  · simp
  · simp [Module.finrank_fintype_fun_eq_card]

private noncomputable def projectiveLine_three_equiv : X3 ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact projectiveLine_three_card)

private noncomputable def psl_three_raw : PSL3 →* Equiv.Perm X3 :=
  Projectivization.PSLAction.toPermHom

private noncomputable def psl_three_action : PSL3 →* Equiv.Perm (Fin 4) :=
  projectiveLine_three_equiv.permCongrHom.toMonoidHom.comp psl_three_raw

private lemma psl_three_action_injective : Function.Injective psl_three_action := by
  exact projectiveLine_three_equiv.permCongrHom.injective.comp
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective

private lemma psl_three_card : Nat.card PSL3 = 12 := by
  change Nat.card (PSL2 F3) = 12
  have hodd : IsOddPrimePower (Nat.card F3) :=
    ⟨3, 1, Nat.prime_three, by decide, by omega, by simp⟩
  rw [psl2_card_formula F3 hodd]
  norm_num

private lemma psl_three_range_card : Nat.card psl_three_action.range = 12 := by
  have hrange : Nat.card psl_three_action.range = Nat.card PSL3 := by
    let e : PSL3 ≃* psl_three_action.range :=
      MulEquiv.ofBijective psl_three_action.rangeRestrict
        ⟨fun a b h => psl_three_action_injective (congrArg Subtype.val h),
          psl_three_action.rangeRestrict_surjective⟩
    exact (Nat.card_congr e.toEquiv).symm
  rw [hrange, psl_three_card]

private lemma psl_three_range_index : psl_three_action.range.index = 2 := by
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  have h := Subgroup.index_mul_card psl_three_action.range
  rw [psl_three_range_card, hperm] at h
  omega

private lemma psl_three_range_eq_alt :
    psl_three_action.range = alternatingGroup (Fin 4) := by
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two psl_three_range_index

private noncomputable def psl_three_action_alt : PSL3 →* alternatingGroup (Fin 4) :=
  psl_three_action.codRestrict (alternatingGroup (Fin 4)) (by
    intro g
    rw [← psl_three_range_eq_alt]
    exact ⟨g, rfl⟩)

private lemma psl_three_action_alt_injective :
    Function.Injective psl_three_action_alt := by
  intro g h gh
  apply psl_three_action_injective
  exact congrArg Subtype.val gh

private lemma psl_three_action_alt_surjective :
    Function.Surjective psl_three_action_alt := by
  intro a
  have ha : (a : Equiv.Perm (Fin 4)) ∈ psl_three_action.range := by
    rw [psl_three_range_eq_alt]
    exact a.property
  rcases (MonoidHom.mem_range.mp ha) with ⟨g, hg⟩
  refine ⟨g, Subtype.ext ?_⟩
  exact hg

private noncomputable def psl_three_equiv_alt :
    PSL3 ≃* alternatingGroup (Fin 4) :=
  MulEquiv.ofBijective psl_three_action_alt
    ⟨psl_three_action_alt_injective, psl_three_action_alt_surjective⟩

private theorem pgl_mk_action_eq_of_projective_fixed
    (A : Matrix.GeneralLinearGroup (Fin 2) F3)
    (h : ∀ x : X3, (Matrix.ProjGenLinGroup.mk A : PGL3) • x = x) :
    ∀ x : X3, A • x = x := by
  intro x
  have hx := h x
  change A • x = x at hx
  exact hx

private theorem gl_center_of_projective_fixed
    (A : Matrix.GeneralLinearGroup (Fin 2) F3)
    (h : ∀ x : X3, A • x = x) :
    A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F3) := by
  let f : (Fin 2 → F3) →ₗ[F3] (Fin 2 → F3) := Matrix.toLin' A.1
  obtain ⟨a, ha⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent (by
    intro v
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · have hvproj := h (Projectivization.mk F3 v hv)
      rw [Projectivization.smul_mk] at hvproj
      simpa [f, LinearIndependent.pair_iff' hv, Projectivization.mk_eq_mk_iff'] using! hvproj)
  have hscalar : A.1 = Matrix.scalar (Fin 2) a := by
    calc
      A.1 = LinearMap.toMatrix' f := by
        change A.1 = LinearMap.toMatrix' (Matrix.toLin' A.1)
        rw [LinearMap.toMatrix'_toLin']
      _ = (algebraMap F3 (Module.End F3 (Fin 2 → F3)) a).toMatrix' :=
        congrArg LinearMap.toMatrix' ha
      _ = Matrix.scalar (Fin 2) a := LinearMap.toMatrix'_algebraMap a
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨a, hscalar.symm⟩

private theorem pgl_action_trivial_eq_one :
    ∀ g : PGL3, (∀ x : X3, g • x = x) → g = 1 := by
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      apply gl_center_of_projective_fixed A
      intro x
      exact (pgl_mk_action_eq_of_projective_fixed A hg) x

private lemma pgl_three_raw_injective :
    Function.Injective (MulAction.toPermHom PGL3 X3) := by
  let : FaithfulSMul PGL3 X3 := faithfulSMul_iff.2 pgl_action_trivial_eq_one
  exact MulAction.toPerm_injective

private noncomputable def pgl_three_raw : PGL3 →* Equiv.Perm X3 :=
  MulAction.toPermHom PGL3 X3

private noncomputable def pgl_three_action : PGL3 →* Equiv.Perm (Fin 4) :=
  projectiveLine_three_equiv.permCongrHom.toMonoidHom.comp pgl_three_raw

private lemma pgl_three_action_injective : Function.Injective pgl_three_action := by
  exact projectiveLine_three_equiv.permCongrHom.injective.comp pgl_three_raw_injective

private lemma gl_scalar_injective :
    Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : F3ˣ →* Matrix.GeneralLinearGroup (Fin 2) F3) := by
  intro a b hab
  apply Units.ext
  have hentry := congrArg
    (fun M : Matrix.GeneralLinearGroup (Fin 2) F3 => M.1 0 0) hab
  simpa using hentry

private lemma gl_center_card :
    Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F3)) = 2 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  let e : F3ˣ ≃* (Matrix.GeneralLinearGroup.scalar (Fin 2)).range :=
    MulEquiv.ofBijective (Matrix.GeneralLinearGroup.scalar (Fin 2)).rangeRestrict
      ⟨fun a b h => gl_scalar_injective (congrArg Subtype.val h),
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).rangeRestrict_surjective⟩
  rw [← Nat.card_congr e.toEquiv]
  simpa using (Nat.totient_prime (by decide : Nat.Prime 3))

private lemma pgl_three_card : Nat.card PGL3 = 24 := by
  change Nat.card (Matrix.GeneralLinearGroup (Fin 2) F3 ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F3)) = 24
  rw [← Subgroup.index_eq_card]
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F3) = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fintype.card_fin]
  have h := Subgroup.index_mul_card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F3))
  rw [hgl, gl_center_card] at h
  omega

private lemma pgl_three_range_card : Nat.card pgl_three_action.range = 24 := by
  have hrange : Nat.card pgl_three_action.range = Nat.card PGL3 := by
    let e : PGL3 ≃* pgl_three_action.range :=
      MulEquiv.ofBijective pgl_three_action.rangeRestrict
        ⟨fun a b h => pgl_three_action_injective (congrArg Subtype.val h),
          pgl_three_action.rangeRestrict_surjective⟩
    exact (Nat.card_congr e.toEquiv).symm
  rw [hrange, pgl_three_card]

private lemma pgl_three_range_index : pgl_three_action.range.index = 1 := by
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  have h := Subgroup.index_mul_card pgl_three_action.range
  rw [pgl_three_range_card, hperm] at h
  omega

private lemma pgl_three_range_eq_top : pgl_three_action.range = ⊤ := by
  exact Subgroup.index_eq_one.mp pgl_three_range_index

private lemma pgl_three_action_surjective : Function.Surjective pgl_three_action :=
  MonoidHom.range_eq_top.mp pgl_three_range_eq_top

private noncomputable def pgl_three_equiv_perm :
    PGL3 ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective pgl_three_action
    ⟨pgl_three_action_injective, pgl_three_action_surjective⟩

/-- The exceptional isomorphism `PSL₂(3) ≃ A₄`, obtained from the faithful
projective-line action on the four points of `ℙ 𝔽₃²`. -/
public noncomputable def psl2_three_equiv_alternatingGroup :
    PSL2 (ZMod 3) ≃* alternatingGroup (Fin 4) :=
  psl_three_equiv_alt

/-- The projective line over `𝔽₃` has four points. -/
public theorem projectiveLine_zmod3_card :
    Nat.card (ℙ (ZMod 3) (Fin 2 → ZMod 3)) = 4 :=
  projectiveLine_three_card

/-- `PSL₂(3)` has order `12`. -/
public theorem nat_card_psl2_zmod3 : Nat.card (PSL2 (ZMod 3)) = 12 :=
  psl_three_card

/-- The exceptional isomorphism `PGL₂(3) ≃ S₄`, obtained from the faithful
projective-line action on the four points of `ℙ 𝔽₃²`. -/
public noncomputable def pgl2_three_equiv_perm :
    PGL2 (ZMod 3) ≃* Equiv.Perm (Fin 4) :=
  pgl_three_equiv_perm

/-- `PGL₂(3)` has order `24`. -/
public theorem nat_card_pgl2_zmod3 : Nat.card (PGL2 (ZMod 3)) = 24 :=
  pgl_three_card

end CFSG.GorensteinWalter
