module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.PartTwo.Census
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def sp4Emb : SL(2, K) →* StatedProj (StatedSp 2 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))).comp
    (longBlock K 2 1)

theorem sp4Emb_injective : Function.Injective (sp4Emb (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [sp4Emb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hA
  obtain ⟨u, hu⟩ := hA
  have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hu
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have e1 : (((longBlock K 2 1 A : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0) = 1 := by
    change mat 2 K (longBlock K 2 1 A) (Sum.inl 0) (Sum.inl 0) = 1
    rw [mat_longBlock, blockMat_apply_of_not_mem (1 : Fin 2) _ (by simp [mem_coords])]
    simp
  rw [e1] at e
  have hu0 : (u : K) = 1 := by simpa [Matrix.GeneralLinearGroup.coe_scalar] using e
  have hu1 : u = 1 := Units.ext hu0
  subst hu1
  have hA1 : longBlock K 2 1 A = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hu]
    simp
  exact longBlock_injective 1 (hA1.trans (map_one _).symm)

end CFSG.RankThree.PartOne.SRC
