module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenF
public import CFSG.LocalAnalysis.WeakClosure81.W15SixG
public import CFSG.Goldschmidt.Steps.G2Grp
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam
public import CFSG.LocalAnalysis.WeakClosure81.W16POneMod
public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.LocalAnalysis.WeakClosure81.W19Min

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def eRep (V₀ X T : Subgroup G)
    [Fact (IsElemAbelian 2 (eSub V₀ X T))] :
    ↥X →* LGL 2 (Additive ↥(eSub V₀ X T)) :=
  CFSG.Goldschmidt.G2.conjRep (A := eSub V₀ X T) (le_normalizer_conjClosure _ _)

theorem eRep_apply (V₀ X T : Subgroup G) [Fact (IsElemAbelian 2 (eSub V₀ X T))] (x : ↥X)
    (v : Additive ↥(eSub V₀ X T)) :
    ((Additive.toMul (eRep V₀ X T x v) : ↥(eSub V₀ X T)) : G) =
      (x : G) * (Additive.toMul v : ↥(eSub V₀ X T)) * (x : G)⁻¹ :=
  rfl

theorem ker_eRep (V₀ X T : Subgroup G) [Fact (IsElemAbelian 2 (eSub V₀ X T))] :
    (eRep V₀ X T).ker = (X ⊓ centralizer (eSub V₀ X T : Set G)).subgroupOf X :=
  CFSG.Goldschmidt.G2.ker_conjRep (A := eSub V₀ X T) (le_normalizer_conjClosure _ _)

theorem exists_eRepBar (M V₀ X T : Subgroup G) [Fact (IsElemAbelian 2 (eSub V₀ X T))]
    (hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G)) :
    ∃ ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T)),
      ∀ x : ↥X, ρ (kerQuotMk M X x) = eRep V₀ X T x := by
  have hle : (M.subgroupOf X).normalCore ≤ (eRep V₀ X T).ker := by
    rw [ker_eRep, ← subgroupOf_kerMOf]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 ⟨x.2, hK (Subgroup.mem_subgroupOf.1 hx)⟩
  exact ⟨QuotientGroup.lift _ (eRep V₀ X T) hle, fun x => rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
