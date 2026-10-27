module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def eSub15 (V₀ P H : Subgroup G) : Subgroup G :=
  conjClosure (V₀ ⊓ centralizer (P : Set G)) H

private theorem inf_centralizer_ne_bot_of_normalized {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem inf_centralizer_le_v1Sub15 (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) : V₀ ⊓ centralizer (P : Set G) ≤ v1Sub15 V₀ U := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, ?_⟩
  exact h.inf_centralizer_le_pCoreOf hS
    (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      Subgroup.centralizer_le hP.S_le (Subgroup.mem_inf.1 hx).2⟩)

theorem eSub15_le_iHull15 (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    eSub15 V₀ P H ≤ iHull15 V₀ U H :=
  conjClosure_mono (hP.inf_centralizer_le_v1Sub15 hS h) le_rfl

theorem eSub15_le (hP : Hyp1510 V₀ V U S H P) : eSub15 V₀ P H ≤ H :=
  conjClosure_le fun k hk z hz =>
    H.mul_mem (H.mul_mem hk (hP.V₀_le_H (Subgroup.mem_inf.1 hz).1)) (H.inv_mem hk)

theorem le_normalizer_eSub15 (V₀ P H : Subgroup G) :
    H ≤ normalizer (eSub15 V₀ P H : Set G) := le_normalizer_conjClosure _ _

theorem isMulCommutative_eSub15 (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) : IsMulCommutative ↥(eSub15 V₀ P H) := by
  have hle : eSub15 V₀ P H ≤ zSub15 V₀ U H :=
    (hP.eSub15_le_iHull15 hS h).trans (iHull15_le_zSub15 V₀ U H)
  exact ⟨⟨fun a b => Subtype.ext (hP.fam.comm a (hle a.2) b (hle b.2))⟩⟩

theorem inf_centralizer_ne_bot (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    V₀ ⊓ centralizer (P : Set G) ≠ ⊥ := by
  have hnorm : P ≤ normalizer (V₀ : Set G) := by
    rw [h.hyp.normalizer₀]
    exact hP.le_M hI hS h
  exact inf_centralizer_ne_bot_of_normalized hP.sylow.isPGroup hP.V₀_le hnorm h.hyp.ne_bot

theorem eSub15_inf_ne_bot (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    eSub15 V₀ P H ⊓ V₀ ≠ ⊥ := fun hbot =>
  hP.inf_centralizer_ne_bot hI hS h (eq_bot_iff.2 (hbot ▸ le_inf (le_conjClosure _ _)
    inf_le_left))

theorem mem_omegaSet_self (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    V₀ ∈ omegaSet V₀ H (eSub15 V₀ P H) :=
  ⟨1, (conjSubgroup_one V₀).symm, hP.eSub15_inf_ne_bot hI hS h, hP.fam.not_V₀_le_pCoreOf h⟩

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81
