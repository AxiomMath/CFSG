module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockBorel

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

namespace L246

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonab_of_isPSL {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ a b : X, a * b ≠ b * a := by
  have := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup (A5.C25.fusionIsBenderGroup_of_isPSL h)
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr fun g => hcon g x
  rw [CFSG.Quasithin.GoldMLA.center_eq_bot_of_isPSL h] at htop
  exact bot_ne_top htop

section Block

variable {X T L : Subgroup G}

structure BlockDataS (X T L : Subgroup G) (n : ℕ) : Prop where
  charTwo : CharTwo X
  sylow : IsSylowTwoOf T X
  block : IsBlock2 X L
  normJ : thompsonJ T ≤ Subgroup.normalizer (L : Set G)
  uV : blockU L ≤ VZ T X
  notC : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G)
  psl : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)

namespace BlockDataS

variable {n : ℕ} (D : BlockDataS X T L n)

include D

omit [Finite G] in
theorem toCore : BlockCore X T L :=
  ⟨D.charTwo, D.sylow, D.block, D.normJ, D.uV, D.notC⟩

theorem elem : IsElemAbelian 2 (VZ T X) :=
  D.toCore.elem

theorem XN : X ≤ Subgroup.normalizer (VZ T X : Set G) :=
  D.toCore.XN

omit [Finite G] in
theorem LX : L ≤ X :=
  D.toCore.LX

omit [Finite G] in
theorem TX : T ≤ X :=
  D.toCore.TX

theorem LN : L ≤ Subgroup.normalizer (VZ T X : Set G) :=
  D.toCore.LN

theorem exists_offender : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
    ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G) :=
  D.toCore.exists_offender

omit [Finite G] in
theorem A_le_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  D.toCore.A_le_normalizer hA

theorem isFFStarOffender {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    IsFFStarOffender (autI D.elem X) (autI D.elem A) :=
  D.toCore.isFFStarOffender hA hAc

theorem hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (VZ T X : Set G) ↔ l ∈ CFSG.pCore 2 ↥L :=
  fun l => by
    rw [← centralizer_subgroupOf_eq_pCore D.charTwo D.sylow D.block D.uV, Subgroup.mem_subgroupOf]

theorem trData : TrData (VZ T X) L D.elem := ⟨D.block.1, D.LN, D.uV⟩

theorem autI_equiv_quot : Nonempty (↥(autI D.elem L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hV := D.elem
  have hLN := D.LN
  have hk : (convHom hV L hLN).ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [ker_convHom, ← D.hpc l, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  exact ⟨(MulEquiv.subgroupCongr (range_convHom hV L hLN).symm).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hV L hLN)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))⟩

theorem isPSL_autI : IsPSL 2 2 n ↥(autI D.elem L) := by
  obtain ⟨e⟩ := D.autI_equiv_quot
  exact IsPSL.of_mulEquiv e.symm D.psl

end BlockDataS

end Block

end L246

end CFSG.QuasithinUnique
