module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LinearAlgebra.SteinbergBQKernelBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
public import CFSG.LinearAlgebra.RestrictEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra
open CFSG.LinearAlgebra.SteinbergBQ
open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem qtwoDB41_restrictEquiv_mem_orthogonalGroup [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} {Q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ w ∈ W, g w ∈ W) (hgO : g ∈ orthogonalGroup Q) :
    restrictEquiv hg ∈ orthogonalGroup (Q.restrict W) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  show Q ((restrictEquiv hg w : W) : V) = Q (w : V)
  rw [restrictEquiv_apply]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO (w : V)

@[expose] noncomputable def qtwoDB41_restrictHom [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} (E : Subgroup (V ≃ₗ[ZMod 2] V))
    (hW : ∀ g ∈ E, ∀ w ∈ W, g w ∈ W) : E →* (W ≃ₗ[ZMod 2] W) where
  toFun g := restrictEquiv (hW g g.2)
  map_one' := by
    ext w
    rw [restrictEquiv_apply]
    rfl
  map_mul' g h := by
    ext w
    rw [restrictEquiv_apply, LinearEquiv.mul_apply, restrictEquiv_apply, restrictEquiv_apply]
    rfl

theorem qtwoDB41_restrictHom_apply [FiniteDimensional (ZMod 2) V]
    {W : Submodule (ZMod 2) V} (E : Subgroup (V ≃ₗ[ZMod 2] V))
    (hW : ∀ g ∈ E, ∀ w ∈ W, g w ∈ W) (g : E) (w : W) :
    ((qtwoDB41_restrictHom E hW g w : W) : V) = (g : V ≃ₗ[ZMod 2] V) w :=
  restrictEquiv_apply (hW g g.2) w

theorem qtwoDB41_fixedSub_nondegenerate [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : E ≤ orthogonalGroup Q) (hodd : Odd (Nat.card E)) :
    ∀ x ∈ fixedSub E, (∀ y ∈ fixedSub E, polar Q x y = 0) → x = 0 := by
  letI : Finite E := Nat.finite_of_card_ne_zero (by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]; positivity)
  intro x hx hperp
  refine hQ.2 x fun y => ?_
  have h1 : polar Q x (avgMap E y) = 0 := hperp _ (avgMap_mem_fixedSub y)
  have h2 : polar Q x (avgMap E y) = polar Q x y := by
    rw [← polar_avgMap hE x y, avgMap_apply_of_mem hodd hx]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, ← h2]
  exact h1

theorem qtwoDB41_polarBilin_isAlt (Q : QuadraticForm (ZMod 2) V) :
    (QuadraticMap.polarBilin Q).IsAlt := fun x => by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, zmod2_vec_add_self]

theorem qtwoDB41_even_finrank_of_nondegenerate [FiniteDimensional (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank (ZMod 2) V) :=
  hB.even_finrank hnd

theorem qtwoDB41_isPlaneSystem_iff [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {m : ℕ} {U : Fin m → Submodule (ZMod 2) V}
    (hU : CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem Q U)
    (hdim : Module.finrank (ZMod 2) V = 2 * m) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m :=
  hU.isPlusType_iff_of_finrank hdim

theorem qtwoDB41_isElementaryAbelian_range {m : ℕ}
    (τ : Multiplicative (DVec m) →* (V ≃ₗ[ZMod 2] V)) :
    IsElementaryAbelian 3 (τ.range) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
  rintro ⟨x, hx⟩
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨u, rfl⟩ := (Multiplicative.ofAdd : DVec m ≃ Multiplicative (DVec m)).surjective w
  apply Subtype.ext
  show (τ (Multiplicative.ofAdd u)) ^ 3 = (1 : V ≃ₗ[ZMod 2] V)
  rw [← map_pow]
  have h3 : (Multiplicative.ofAdd u : Multiplicative (DVec m)) ^ 3 = 1 := by
    have h3v : (3 : ℕ) • u = 0 := by
      ext i
      show (3 : ℕ) • (u i) = (0 : ZMod 3)
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 (u i), smul_eq_zero]
      exact Or.inl (by decide)
    change Multiplicative.ofAdd ((3 : ℕ) • u) = (1 : Multiplicative (DVec m))
    rw [h3v]
    rfl
  rw [h3, map_one]

theorem qtwoDB41_odd_card_range {m : ℕ} [FiniteDimensional (ZMod 2) V]
    (τ : Multiplicative (DVec m) →* (V ≃ₗ[ZMod 2] V)) :
    Odd (Nat.card τ.range) := by
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_zmod2
  have hP : IsPGroup 3 (τ.range) := (qtwoDB41_isElementaryAbelian_range τ).isPGroup 3 _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  exact Odd.pow (by decide)

theorem qtwoDB41_not_isPlusType_of_aniso {W : Submodule (ZMod 2) V}
    {q : QuadraticForm (ZMod 2) ↥W} {P : Submodule (ZMod 2) ↥W}
    (hfr : Module.finrank (ZMod 2) P = 2) (han : ∀ x ∈ P, q x = 0 → x = 0) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (q.comp P.subtype) := by
  rintro ⟨U, hU, hU0⟩
  have hUfr : Module.finrank (ZMod 2) U = 1 := by omega
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hUfr
    omega
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  exact hx0 (Subtype.ext (han x x.2 (hU0 x hxU)))

end CFSG.StandardType.QTwo

end
