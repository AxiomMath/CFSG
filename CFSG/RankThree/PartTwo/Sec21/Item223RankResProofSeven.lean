module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofCross
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofEigen
import CFSG.LieType.Chevalley.OddPinnedComponents
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

open CFSG.RankThree.PartOne.SEITZ11 CFSG.RankThree.PartOne.SEITZ11.G2Seven Matrix

theorem card_le_nine_seven_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) (E : Subgroup (GL (Fin 7) L)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hform : E ≤ formSubgroup L) (hcross : E ≤ crossSubgroup L) : Nat.card E ≤ 9 := by
  obtain ⟨b, d, hb⟩ := Sec4.exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have h4 : (4 : L) ≠ 0 := by
    have : (4 : L) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  refine card_le_nine_of_eigen hexp hb (G2Seven.gram L) (gram_det_ne_zero h2)
    (fun x hx => hform hx) cross7 cross7_smul_left cross7_smul_right
    (fun x hx => hcross hx) 4 h4 (fun a c e _ _ hae hce => ?_) ?_
  · have h := cross7_cross7 (b a) (b e) (b c)
    have hae' : bil7 (b a) (b e) = 0 := hae
    have hce' : bil7 (b c) (b e) = 0 := hce
    rw [hae', hce', mul_zero, zero_smul, zero_smul, sub_zero, sub_zero] at h
    exact h
  · exact (Finite.card_subtype_le _).trans (by simp)

section Rep

variable
    (k : Type) [Field k] [Finite k]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.RankTwo

theorem rep7_injective (hk : ringChar k ≠ 2) : Function.Injective (rep7 k) := by
  have hs := (odd_pinned_Chevalley_p_components .G2 k hk).1
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hs.eq_bot_or_eq_top_of_normal (rep7 k).ker with h | h
  · exact h
  · exfalso
    have hx : xPar (rootOperatorFamily .G2) (g2CommRoot 0) (1 : k) ∈ (rep7 k).ker :=
      h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hx
    have h1 := rep7_xPar_pos k (a := 0) (by norm_num) (1 : k)
    rw [hx, Units.val_one] at h1
    have h21 := congrFun (congrFun h1 2) 1
    simp [rootMat, opMat, opMatSq, entMat, ent7, ent7sq] at h21

theorem adjointG2_card_le_nine (hk2 : ringChar k ≠ 2) (hk3 : (3 : k) ≠ 0)
    (F : Subgroup (adjointGroup .G2 k)) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    Nat.card F ≤ 9 := by
  set L := AlgebraicClosure k
  set ρ : adjointGroup .G2 k →* GL (Fin 7) L :=
    (Matrix.GeneralLinearGroup.map (algebraMap k L)).comp (rep7 k) with hρ
  have hρinj : Function.Injective ρ := (Sec4.map_injective_GL _).comp (rep7_injective k hk2)
  have : Finite (adjointGroup .G2 k) := Finite.of_injective _ (rep7_injective k hk2)
  have : Finite (F.map ρ) := Finite.of_surjective _ (ρ.subgroupMap_surjective F)
  have h2 : (2 : L) ≠ 0 := by
    intro h
    apply Ring.two_ne_zero hk2
    apply (algebraMap k L).injective
    rw [map_ofNat, h, map_zero]
  have h3 : (3 : L) ≠ 0 := by
    intro h
    apply hk3
    apply (algebraMap k L).injective
    rw [map_ofNat, h, map_zero]
  have hcommF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h := card_le_nine_seven_of_isAlgClosed h2 h3 (F.map ρ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcommF x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF.2 x hx, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      exact rep7_map_mem_formSubgroup k (algebraMap k L) x)
    (by
      rintro _ ⟨x, -, rfl⟩
      exact rep7_map_mem_crossSubgroup k (algebraMap k L) x)
  rwa [Subgroup.card_map_of_injective hρinj] at h

end Rep

end CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
