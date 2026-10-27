module

public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem neg_one_mem_statedSp_two : (-1 : GL V₄ K) ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  simp

@[expose] def IsNCInv (d : GL V₄ K) : Prop := d ∈ StatedSp 2 K ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ -1

theorem IsNCInv.neg {d : GL V₄ K} (hd : IsNCInv d) : IsNCInv (-d) := by
  obtain ⟨hS, h2, h1, hm⟩ := hd
  refine ⟨?_, by rw [neg_mul_neg, h2], fun h => hm (by rw [← neg_neg d, h]), fun h => h1 ?_⟩
  · rw [show -d = -1 * d by simp]
    exact mul_mem neg_one_mem_statedSp_two hS
  · rw [← neg_neg d, h, neg_neg]

theorem IsNCInv.conj {d g : GL V₄ K} (hd : IsNCInv d) (hg : g ∈ StatedSp 2 K) :
    IsNCInv (g * d * g⁻¹) := by
  obtain ⟨hS, h2, h1, hm⟩ := hd
  refine ⟨mul_mem (mul_mem hg hS) (inv_mem hg), ?_, ?_, ?_⟩
  · calc g * d * g⁻¹ * (g * d * g⁻¹) = g * (d * d) * g⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]
  · intro h
    apply h1
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hm
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = -1 := by rw [h]; simp

end CFSG.RankThree.SubgroupLists
