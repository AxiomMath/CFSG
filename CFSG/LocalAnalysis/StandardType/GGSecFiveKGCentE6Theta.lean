module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6FixedFive

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

@[expose] noncomputable def thetaLinE6 (w : WeylGroup Tag.E6) :
    (Fin Tag.E6.rank → ℤ) →ₗ[ℤ] (Fin Tag.E6.rank → ℤ) where
  toFun v := w • permLattice diagPermE6 v
  map_add' x y := smul_add w (permLattice diagPermE6 x) (permLattice diagPermE6 y)
  map_smul' c x := smul_comm w c (permLattice diagPermE6 x)

theorem thetaLinE6_apply (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) :
    thetaLinE6 w v = w • permLattice diagPermE6 v :=
  rfl

theorem thetaLinE6_iso (w : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    iform (thetaLinE6 w x) (thetaLinE6 w y) = iform x y := by
  rw [thetaLinE6_apply, thetaLinE6_apply, iform_smul_E6, iform_permLattice_diagPermE6]

theorem thetaLinE6_root (w : WeylGroup Tag.E6) (j : Fin Tag.E6.rank) :
    thetaLinE6 w (Pi.single j 1) ∈ roots72 := by
  rw [thetaLinE6_apply]
  refine mem_roots72_of_isRoot (IsRoot.smul ?_ w)
  have h : permLattice diagPermE6 (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (diagPermE6 j) 1 := by
    ext k
    simp only [permLattice, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  rw [h]
  exact IsRoot.basis _

theorem mod3_yE6 (w : WeylGroup Tag.E6) : ¬ (3 : ℤ) ∣ (thetaLinE6 w yE6 - yE6) idxZeroE6 := by
  have h1 := three_dvd_smul_sub (permLattice diagPermE6 yE6) (by decide +kernel) w idxZeroE6
  have h3 : (permLattice diagPermE6 yE6 - yE6) idxZeroE6 = -2 := by decide +kernel
  have h4 : (thetaLinE6 w yE6 - yE6) idxZeroE6 =
      (w • permLattice diagPermE6 yE6 - permLattice diagPermE6 yE6) idxZeroE6 +
        (permLattice diagPermE6 yE6 - yE6) idxZeroE6 := by
    simp only [thetaLinE6_apply, Pi.sub_apply]
    ring
  rw [h4, h3]
  omega

theorem not_linearIndependent_fix_E6 (w : WeylGroup Tag.E6)
    (hθθ : ∀ v : Fin Tag.E6.rank → ℤ, w • permLattice diagPermE6 (w • permLattice diagPermE6 v) = v)
    {f : Fin 5 → Fin Tag.E6.rank → ℤ} (hf : ∀ i, w • permLattice diagPermE6 (f i) = f i) :
    ¬ LinearIndependent ℤ f :=
  not_linearIndependent_fixed_five_E6 (θ := thetaLinE6 w) hθθ (thetaLinE6_iso w)
    (thetaLinE6_root w) (mod3_yE6 w) hf

end CFSG.StandardType.KGCentE6
