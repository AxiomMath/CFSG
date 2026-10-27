module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofSubn
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofSteps
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof155R2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev w155 (A M X : Subgroup G) : Subgroup G :=
  inSubgroup perfectResidual (b155 A M X)

@[expose] noncomputable def Step155BSubn2W (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → w155 A M X ≠ ⊥ →
      IsScriptLBlock ⊤ (oResidual 2 ↥(CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X)) →
        (((oResidual 2 ↥(CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X)).map
          (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X).subtype).subgroupOf M).IsSubnormal

@[expose] noncomputable def Step155INormX2W (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → w155 A M X ≠ ⊥ →
      IsScriptLBlock ⊤ (oResidual 2 ↥(CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X)) →
        oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (X : Set G)

@[expose] noncomputable def Step155INormX2WR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155INormX2W A c L

namespace Proof155w2

omit [Finite G] in
theorem le_normalizer_inSubgroup_perfectResidual_of {H B : Subgroup G}
    (hHB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer (inSubgroup perfectResidual B : Set G) :=
  hHB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

end Proof155w2

open Proof155w2

theorem step155BSubn2W_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (h149 : Item149 A (lB A)) (hI : Step155INormX2W A c L) : Step155BSubn2W A c L := by
  intro h X K Y M T P hC hmax hab hE hW1 hbl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 Y with hR
  set I := delta A (lB A) M with hIdef
  set I₀ := oPrimeResidualOf 3 I with hI₀
  set C := centralizerSection X (CFSG.Open.pCoreOf 2 X) with hCdef
  set B := b155 A M X with hBdef
  set W := w155 A M X with hWdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  obtain ⟨h1, h2, -, -⟩ := h149 M hM2.1
  have hI₀n : (I₀.subgroupOf M).Normal := by
    rw [hI₀, h1]
    exact h2
  have hI₀M : I₀ ≤ M := (oPrimeResidualOf_le_self 3 I).trans (delta_le M)
  have hMI₀ : M ≤ Subgroup.normalizer (I₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hI₀M).mp hI₀n
  have hBeq : B = oPrimeResidualOf 3 (I₀ ⊓ C) := by
    refine (oPrimeResidualOf_eq_of_le (inf_le_inf_right C (oPrimeResidualOf_le_self 3 I)) ?_).symm
    intro x hx k hk
    refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hx).2⟩
    show x ∈ oPrimeResidualOf 3 I
    rw [oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨(Subgroup.mem_inf.mp hx).1, k, hk⟩
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hRY : R ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hNC : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerSection le_rfl
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hRB : R ≤ Subgroup.normalizer (B : Set G) := by
    rw [hBeq]
    exact le_normalizer_oPrimeResidualOf (Late.le_normalizer_inf ((hRY.trans hYM).trans hMI₀)
      ((hRY.trans hYX).trans hNC))
  have hI₀X := hI h X K Y M T P hC hmax hab hE hW1 hbl
  have hI₀B : I₀ ≤ Subgroup.normalizer (B : Set G) := by
    rw [hBeq]
    exact le_normalizer_oPrimeResidualOf (Late.le_normalizer_inf Subgroup.le_normalizer
      (hI₀X.trans hNC))
  have hBI₀ : B ≤ I₀ := by
    rw [hBeq]
    exact (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  have hWB : W ≤ B := Subgroup.map_subtype_le _
  have hRW : R ≤ Subgroup.normalizer (W : Set G) := le_normalizer_inSubgroup_perfectResidual_of hRB
  have hI₀W : I₀ ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_inSubgroup_perfectResidual_of hI₀B
  have hWI₀ : W ≤ I₀ := hWB.trans hBI₀
  set O := inSubgroup (oResidual 2) (R ⊔ W) with hO
  have hOW : O ≤ W := inSubgroup_oResidual_two_le hR2 hRW
  have hWO : W ≤ Subgroup.normalizer (O : Set G) :=
    le_sup_right.trans (le_normalizer_inSubgroup_oResidual Subgroup.le_normalizer)
  have hOWs : (O.subgroupOf W).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hOW).mpr hWO).isSubnormal
  have hWI₀s : (W.subgroupOf I₀).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWI₀).mpr hI₀W).isSubnormal
  exact isSubnormal_subgroupOf_trans148 (hOW.trans hWI₀) hI₀M
    (isSubnormal_subgroupOf_trans148 hOW hWI₀ hOWs hWI₀s) hI₀n.isSubnormal

theorem step155BSubn2WR_of (h149 : Sec16.Item149S14) (hI : Step155INormX2WR) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Step155BSubn2W A c L :=
  fun G _ _ A c L hR => step155BSubn2W_of (h149 G A c L hR.toSec14Std) (hI G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
