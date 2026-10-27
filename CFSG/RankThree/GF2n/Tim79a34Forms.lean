module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
public import TauCeti.RepresentationTheory.InvariantForm
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.GF2n.Tim79a

open TauCeti Representation in
theorem exists_eq_smul_of_isAbsolutelyIrreducible
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {ρ : Representation F G V} [CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ]
    {B C : LinearMap.BilinForm F V} (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hC : IsInvariantForm ρ C) : ∃ c : F, C = c • B := by
  haveI : ρ.IsIrreducible :=
    CFSG.Theory.Representation.IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  have hBnd : B.Nondegenerate := hB.nondegenerate hB0
  let φ : V →ₗ[F] V := C.symmCompOfNondegenerate B hBnd
  have hφB : ∀ v w : V, B (φ v) w = C v w := fun v w =>
    C.symmCompOfNondegenerate_left_apply hBnd w v
  have hφ : ∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v) := by
    intro g v
    refine sub_eq_zero.mp (hBnd.1 _ fun w => ?_)
    rw [map_sub, LinearMap.sub_apply, hφB, hB.apply_left, hφB, hC.apply_left, sub_self]
  obtain ⟨c, hc⟩ := (CFSG.Theory.Representation.isAbsolutelyIrreducible_iff_surjective ρ).mp
    inferInstance (φ.intertwiningMap_of_isIntertwiningMap ρ ρ hφ)
  have hφc : ∀ v, φ v = c • v := fun v =>
    (congrArg (fun h : CFSG.Theory.Representation.End ρ => h v) hc).symm
  refine ⟨c, LinearMap.ext fun v => LinearMap.ext fun w => ?_⟩
  have h := hφB v w
  rw [hφc v, map_smul, LinearMap.smul_apply] at h
  rw [LinearMap.smul_apply]
  exact h.symm

theorem no_invariant_bilinear_map_onto_plane
    {L U A : Type*} [Group L] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup A] [Module (ZMod 2) A]
    [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) L U)
    [CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ]
    (κ : U →ₗ[ZMod 2] U →ₗ[ZMod 2] A) (hκ : ∀ g x y, κ (ρ g x) (ρ g y) = κ x y)
    (hspan : ∀ l : Module.Dual (ZMod 2) A, (∀ x y, l (κ x y) = 0) → l = 0)
    (hA : Module.finrank (ZMod 2) A = 2) : False := by
  let b : Module.Basis (Fin 2) (ZMod 2) A := Module.finBasisOfFinrankEq (ZMod 2) A hA
  have hb00 : b.coord 0 (b 0) = 1 := by simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hb11 : b.coord 1 (b 1) = 1 := by simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hb01 : b.coord 0 (b 1) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  have hinv : ∀ l : Module.Dual (ZMod 2) A,
      TauCeti.Representation.IsInvariantForm ρ (κ.compr₂ l) := fun l =>
    TauCeti.Representation.isInvariantForm_iff.mpr fun g x y => by
      simp only [LinearMap.compr₂_apply, hκ]
  have hκ0 : κ.compr₂ (b.coord 0) ≠ 0 := by
    intro h
    have hz : b.coord 0 = 0 := hspan (b.coord 0) fun x y => by
      simpa [LinearMap.compr₂_apply] using LinearMap.congr_fun (LinearMap.congr_fun h x) y
    have h0 := LinearMap.congr_fun hz (b 0)
    simp [hb00] at h0
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isAbsolutelyIrreducible (hinv (b.coord 0)) hκ0
    (hinv (b.coord 1))
  have hfun : b.coord 1 = c • b.coord 0 := by
    have hzero : ∀ x y, (b.coord 1 - c • b.coord 0) (κ x y) = 0 := by
      intro x y
      have h1 := LinearMap.congr_fun (LinearMap.congr_fun hc x) y
      simp only [LinearMap.compr₂_apply, LinearMap.smul_apply, smul_eq_mul] at h1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h1, sub_self]
    exact sub_eq_zero.mp (hspan (b.coord 1 - c • b.coord 0) hzero)
  have h2 := LinearMap.congr_fun hfun (b 1)
  simp [hb11, hb01] at h2

end CFSG.RankThree.GF2n.Tim79a

end
