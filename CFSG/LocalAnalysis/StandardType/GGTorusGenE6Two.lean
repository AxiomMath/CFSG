module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThreeIrred
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Cent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TableBExc.E6Three

namespace E6TwoGen

section Core


theorem ggTorusGenR_adjoint_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenR 3 4 (adjointGroup .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro E hE hr hsc x hx hx1 J hJ c hc _
  obtain ⟨g, hg⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hr
  have hcent : (MulAut.conj g).toMonoidHom c ∈ Subgroup.centralizer
      ((torusE6Two (K := K) h2).range : Set (adjointGroup .E6 K)) := by
    rw [← hg, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    have hce : e * c = c * e := (Subgroup.mem_centralizer_iff.mp hc) e he
    rw [← map_mul, ← map_mul, hce]
  have hcE : c ∈ E := by
    have hmem : (MulAut.conj g).toMonoidHom c ∈ E.map (MulAut.conj g).toMonoidHom := by
      rw [hg]
      exact CFSG.LocalAnalysis.GLTheoremA.T173O.centralizer_range_torusE6Two_le h2 hK hcent
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).mp hmem
  obtain ⟨w, hwJ, hwE, hw1⟩ :=
    exists_mem_ne_one_of_isComponentOf_e6Two hK h2 hg hsc hx hx1 hJ
  refine ⟨J ⊓ E, Subgroup.normalizer (E : Set (adjointGroup .E6 K)), fun a => ⟨1, ?_⟩,
    fun s hs => ?_, inf_le_left, subset_rfl,
    ExcTwoGen.le_closure_conj_of_ggWeylIrred
      (ggSCWeylIrred_adjoint_E6_two hK E hE hr (le_trans (by norm_num) hr) hsc)
      hwJ hwE hw1 hcE⟩
  · exact Subtype.ext (by simpa using hE.2 a a.2.2)
  · exact Subgroup.mem_centralizer_iff.mpr fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨s, hs.2⟩)

theorem ggTorusGenR_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenR 3 4 (TableBExc.RecipeGroup .E6 K) :=
  ggTorusGenR_of_mulEquiv (TableBExc.recipeEquiv .E6 K) (ggTorusGenR_adjoint_E6_two hK)

end Core

end E6TwoGen

section Label


theorem ggTorusGenTableB_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenTableB 3 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  have hRk := ggTorusGenTableBRk_of_torusGenR (r := 4) Nat.prime_three
    (fun φ hφ _ => recipeID_subset_inn_E6_two hK hφ)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggCenterPrime_recipe_E6_two hK Nat.prime_three)
    (E6TwoGen.ggTorusGenR_E6_two hK)
  exact ggTorusGenTableB_of_rk (r := 5) Nat.prime_three (by norm_num)
    ggTorusLift_E6_two hRk

theorem largeEvenLabelAll_torusGenTableB_e6Two {p : ℕ} {lab : LargeEvenLabel}
    (hrow : GGL48TBExcTwoRow p lab) (hτ : lab.tag = .E6) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hn, rfl⟩ := hrow
  dsimp only at hτ hn
  subst hn hτ
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, ggTorusGenTableB_E6_two (by simpa using hK)⟩

end Label

end CFSG.StandardType
