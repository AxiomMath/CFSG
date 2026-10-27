module

public import CFSG.Sporadic.Co1I301.ThreeA
public import CFSG.Sporadic.Co1I301.Layer
public import CFSG.Sporadic.Co1I301.RowMax
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1U
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Elem
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Open CFSG.Sporadic.Co1Patterson CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
  CFSG.LocalAnalysis.GLTheoremA.H301B
open CFSG.Blueprint (NativeSporadic.Co1)


theorem normalizer_co1R (D : TwoCentralData 4 aNC co1R) :
    Subgroup.normalizer (co1R : Set NativeSporadic.Co1) =
      centralizer ({aNC} : Set NativeSporadic.Co1) := by
  apply le_antisymm
  · intro g hg
    exact (@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC g).2
      (comm_of_mem_normalizer D.extraspecial D.z_mem D.z_central D.z_ne_one hg)
  · intro g hg
    exact D.normalizes g
      ((@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC g).1 hg)

noncomputable abbrev B1C : Subgroup NativeSporadic.Co1 := Subgroup.closure {dC, eC 0, eC 1, eC 2}

theorem co1_hB : IsElemAbelian 3 B1C ∧ Nat.card B1C = 3 ^ 4 := by
  obtain ⟨he, hee⟩ := e_facts
  have hde : ∀ i < 3, Commute dC (eC i) := fun i hi => ((he i hi).2.1).symm
  exact isElemAbelian_closure_four (hde 0 (by norm_num)) (hde 1 (by norm_num))
    (hde 2 (by norm_num)) (hee 0 (by norm_num) 1 (by norm_num))
    (hee 0 (by norm_num) 2 (by norm_num)) (hee 1 (by norm_num) 2 (by norm_num))
    dC_pow_three (he 0 (by norm_num)).1 (he 1 (by norm_num)).1 (he 2 (by norm_num)).1 e_indep

theorem B1C_le_centralizer : B1C ≤ centralizer ({aNC} : Set NativeSporadic.Co1) := by
  refine (Subgroup.closure_le _).2 ?_
  have he := e_facts.1
  rintro g (rfl | rfl | rfl | rfl)
  · exact dC_mem_centralizer
  · exact (@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC _).2
      (he 0 (by norm_num)).2.2
  · exact (@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC _).2
      (he 1 (by norm_num)).2.2
  · exact (@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC _).2
      (he 2 (by norm_num)).2.2

theorem rowKOf_dC (D : TwoCentralData 4 aNC co1R) : rowKOf 3 dC co1R = GLAPLayer 3 XC := by
  unfold rowKOf
  rw [rowIOf_dC, normalizer_co1R D]

theorem co1_hK6 (D : TwoCentralData 4 aNC co1R) :
    rowKOf 3 dC co1R = GLAPLayer 3 (centralizer ({dC} : Set NativeSporadic.Co1) ⊓
      centralizer (centerOf (rowR0Of dC co1R) : Set NativeSporadic.Co1)) := by
  rw [rowKOf_dC D, centerOf_rowR0, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem i301ARowCfg_co1 (D : TwoCentralData 4 aNC co1R)
    (hOut : ∀ α : MulAut NativeSporadic.Co1, ∃ g : NativeSporadic.Co1, α = MulAut.conj g) :
    I301ARowCfg .co1 co1R B1C dC where
  hR := ⟨D.extraspecial, D.card⟩
  hB := co1_hB
  hBN := B1C_le_centralizer.trans (normalizer_co1R D).ge
  hd := ⟨Subgroup.subset_closure (Set.mem_insert _ _), dC_ne_one⟩
  hI := by
    show IsTypeWithCenter 3 (rowIOf 3 dC) (sporIs .Suz) 3
    rw [rowIOf_dC]
    exact isTypeWithCenter_centralizer_dC
  hK := by
    show IsTypeWithCenter 3 (rowKOf 3 dC co1R) isPSp43 1
    rw [rowKOf_dC D]
    exact isTypeWithCenter_layer_XC
  hR0 := card_rowR0
  hR0t := Or.inl rowR0_extraspecial
  hK6 := Or.inr (co1_hK6 D)
  hNL := fun h => absurd h (by decide)
  hMax := co1_hMax D co1_hB.1 co1_hB.2 B1C_le_centralizer hOut

theorem i301ARow_co1 : I301ARow .co1 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hcfg := i301ARowCfg_co1 (twoCentralData_co1 uCo1)
    (Co1Schreier.full_automorphisms_inner_of_inputs Co2Schreier.CTUC_Co2_full_automorphisms_inner)
  exact @i301ARow_of_model .co1 NativeSporadic.Co1 inferInstance inferInstance ⟨b⟩ _ _ _ hcfg

end CFSG.Sporadic.Co1I301
