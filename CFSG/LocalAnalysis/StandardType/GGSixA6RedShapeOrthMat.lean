module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeOrthAbs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open QuadraticMap
open scoped Matrix

private theorem polar_toFun {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar (fun v => Φ.Q v) x y = Φ.polar.β x y := by
  rw [QuadraticMap.polar, Φ.Q_add x y]
  abel

private noncomputable def ggA6_toQuadraticForm {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Φ : QuadForm F (ι → F)) : QuadraticForm F (ι → F) :=
  QuadraticMap.ofPolar (fun v => Φ.Q v)
    (by
      intro a x
      rw [Φ.Q_smul, smul_eq_mul, pow_two])
    (by
      intro x x' y
      rw [polar_toFun Φ (x + x') y, polar_toFun Φ x y, polar_toFun Φ x' y]
      exact Φ.polar.add_left x x' y)
    (by
      intro a x y
      rw [polar_toFun Φ (a • x) y, polar_toFun Φ x y, smul_eq_mul, Φ.polar.smul_left,
        Φ.polar_σ]
      simp)

private theorem ggA6_polar_toQuadraticForm {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Φ : QuadForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar (ggA6_toQuadraticForm Φ) x y = Φ.polar.β x y :=
  polar_toFun Φ x y

private theorem nondegenerate_toQuadraticForm {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Φ : QuadForm F (ι → F)) :
    (QuadraticMap.polarBilin (ggA6_toQuadraticForm Φ)).Nondegenerate := by
  constructor
  · intro u hu
    exact Φ.polar.nondeg u fun v => by
      have h := hu v
      rwa [QuadraticMap.polarBilin_apply_apply, ggA6_polar_toQuadraticForm] at h
  · intro v hv
    exact Φ.polar.nondeg v fun w => by
      rw [Φ.polar_symm v w]
      have h := hv w
      rwa [QuadraticMap.polarBilin_apply_apply, ggA6_polar_toQuadraticForm] at h

private noncomputable def ggA6_glLinearEquiv {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  TauCeti.matrixGeneralLinearEquiv.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

private theorem ggA6_glLinearEquiv_apply {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : GL ι F) (v : ι → F) :
    (ggA6_glLinearEquiv (F := F) (ι := ι) A) v = (A : Matrix ι ι F) *ᵥ v := by
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))
      (TauCeti.matrixGeneralLinearEquiv A)) v = (A : Matrix ι ι F) *ᵥ v
  rw [TauCeti.matrixGeneralLinearEquiv_apply]

private theorem mem_orthGroup_iff {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : (ι → F) → F} {A : GL ι F} :
    A ∈ orthGroup Q ↔ ∀ v, Q ((A : Matrix ι ι F) *ᵥ v) = Q v := by
  constructor
  · intro hA v
    exact orthGroup_preserves Q hA v
  · intro hA
    exact Subgroup.subset_closure hA

private theorem map_orthGroup {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadForm F (ι → F)) :
    (orthGroup Φ.Q).map (ggA6_glLinearEquiv (F := F) (ι := ι)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (ggA6_toQuadraticForm Φ) := by
  apply le_antisymm
  · rintro f ⟨A, hA, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [MulEquiv.coe_toMonoidHom, ggA6_glLinearEquiv_apply]
    change Φ.Q ((A : Matrix ι ι F) *ᵥ v) = Φ.Q v
    exact (mem_orthGroup_iff.mp hA) v
  · intro f hf
    have hsymm : (ggA6_glLinearEquiv (F := F) (ι := ι)).toMonoidHom
        ((ggA6_glLinearEquiv (F := F) (ι := ι)).symm f) = f := by
      rw [MulEquiv.coe_toMonoidHom]
      exact (ggA6_glLinearEquiv (F := F) (ι := ι)).apply_symm_apply f
    refine Subgroup.mem_map.mpr ⟨(ggA6_glLinearEquiv (F := F) (ι := ι)).symm f, ?_, hsymm⟩
    rw [mem_orthGroup_iff]
    intro v
    have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hf) v
    have h1 := ggA6_glLinearEquiv_apply ((ggA6_glLinearEquiv (F := F) (ι := ι)).symm f) v
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    change (ggA6_toQuadraticForm Φ) (f v) = (ggA6_toQuadraticForm Φ) v
    exact h

private theorem ggA6_map_centralizer {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((P.map e.toMonoidHom : Subgroup H) : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro p hp
    obtain ⟨p0, hp0, rfl⟩ := Subgroup.mem_map.mp hp
    simpa using congrArg (⇑e) (hc p0 hp0)
  · intro hx
    have hsymm : e.toMonoidHom (e.symm x) = x := by
      rw [MulEquiv.coe_toMonoidHom]
      exact e.apply_symm_apply x
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, hsymm⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro p hp
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e p) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)

theorem ggA6_shape_orthCentralizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : QuadForm F (ι → F)) (P : Subgroup (GL ι F))
    (hPO : P ≤ orthGroup Φ.Q) (hP : Odd (Nat.card P)) (hPn : Group.IsNilpotent ↥P)
    (J : Subgroup (GL ι F)) (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJsub : IsSubnormal J (orthGroup Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F)))) :
    GGA6CharTwoLie J := by
  let e : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) := ggA6_glLinearEquiv (F := F) (ι := ι)
  let Q' : QuadraticForm F (ι → F) := ggA6_toQuadraticForm Φ
  let A : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := P.map e.toMonoidHom
  let J' : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := J.map e.toMonoidHom
  have hmapO : (orthGroup Φ.Q).map e.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' := map_orthGroup Φ
  have hmapC : (Subgroup.centralizer (P : Set (GL ι F))).map e.toMonoidHom =
      Subgroup.centralizer (A : Set ((ι → F) ≃ₗ[F] (ι → F))) := ggA6_map_centralizer e P
  have hmapI : (orthGroup Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F))).map e.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q' ⊓
        Subgroup.centralizer (A : Set ((ι → F) ≃ₗ[F] (ι → F))) := by
    rw [Subgroup.map_inf _ _ _ e.injective, hmapO, hmapC]
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q' := by
    rw [← hmapO]
    exact Subgroup.map_mono hPO
  have hodd : Odd (Nat.card A) := by
    rw [Subgroup.card_map_of_injective (K := P) e.injective]
    exact hP
  have hnil : Group.IsNilpotent ↥A := by
    haveI : Group.IsNilpotent ↥P := hPn
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective)
  have hJq' : CFSG.Assembly.IsQuasisimple ↥J' :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm hJq
  have hJsub' : IsSubnormal J' (TauCeti.QuadraticMap.orthogonalGroup Q' ⊓
      Subgroup.centralizer (A : Set ((ι → F) ≃ₗ[F] (ι → F)))) := by
    have h := CFSG.Assembly.IsSubnormal.map e.toMonoidHom hJsub
    rw [← hmapI]
    exact h
  have hmain : GGA6CharTwoLie ↥J' :=
    ggA6_shape_orthCentralizer_abs Q' (nondegenerate_toQuadraticForm Φ) A hAO hodd hnil hJq'
      hJsub'
  exact GGA6CharTwoLie.of_mulEquiv
    (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm hmain

end CFSG.StandardType.A6Red

end
