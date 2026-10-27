module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint

theorem e6Admissible_neg {b : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)}
    {v : Fin Tag.E6.rank → ZMod 3}
    {r : ZMod 3} (h : E6Admissible b v r) : E6Admissible (fun i => -b i) v (-r) := by
  have hb : (fun i => -b i) = (-b : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) := rfl
  rw [hb]
  refine ⟨fun i => IsRoot.neg (h.1 i), fun i j => ?_, fun i => ?_⟩
  · have hneg : iform ((-b) i) ((-b) j) = iform (b i) (b j) := by
      simp only [iform, Pi.neg_apply]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hneg, h.2.1 i j]
  · simp only [Pi.neg_apply]
    have hterm : ∀ k, ((-(b i k) : ℤ) : ZMod 3) * v k =
        -((((b i k : ℤ)) : ZMod 3) * v k) := by
      intro k
      rw [Int.cast_neg]
      exact neg_mul _ _
    have hsum : (∑ k, ((-(b i k) : ℤ) : ZMod 3) * v k) =
        -(∑ k, (((b i k : ℤ)) : ZMod 3) * v k) :=
      (Finset.sum_congr rfl fun k _ => hterm k).trans (Finset.sum_neg_distrib _)
    rw [hsum, h.2.2 i]
    exact (neg_mul r (v i)).symm

theorem e6CosetW_of_eq_smul {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) {u : WeylGroup Tag.E6}
    (hu : ∀ γ, IsRoot Tag.E6 γ → ρ γ = u • γ) : E6CosetW ρ := by
  have hρ : ∀ x, ρ x = u • x := by
    let f : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) := AddMonoidHom.mk' ρ hadd
    let g : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
      DistribSMul.toAddMonoidHom (Fin Tag.E6.rank → ℤ) u
    have hfg : f = g := by
      apply AddMonoidHom.functions_ext'
      intro i
      apply AddMonoidHom.ext_int
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
      show ρ (Pi.single i 1) = u • Pi.single i 1
      exact hu (Pi.single i 1) (IsRoot.basis i)
    intro x
    simpa only [f, g, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply]
      using DFunLike.congr_fun hfg x
  have he6 : e6ThreeVarpiOne = e6Omega3 := rfl
  intro k
  rw [hρ e6ThreeVarpiOne, he6, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact three_dvd_smul_e6Omega3_sub u k

end CFSG.StandardType.TablePThreeKG

end
