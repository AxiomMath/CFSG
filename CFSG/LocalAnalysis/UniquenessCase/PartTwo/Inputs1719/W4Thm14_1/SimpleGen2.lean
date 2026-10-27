module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.Quasithin.Background.RonanE114P7
public import CFSG.Quasithin.MS93.ML3Basic
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open scoped commutatorElement

open CFSG.HardMathSupport.RichardWeiss.Proving
open CFSG.Quasithin.MS93

theorem exists_closure_pair_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (X : Subgroup G) (e : ↥X ≃* H) {a b : H}
    (hgen : Subgroup.closure ({a, b} : Set H) = ⊤) (hnc : a * b ≠ b * a) :
    ∃ y₁ ∈ X, ∃ y₂ ∈ X,
      Subgroup.closure ({y₁, y₂} : Set G) = X ∧ y₁ * y₂ ≠ y₂ * y₁ := by
  have hsub : Subgroup.closure ({(e.symm a : ↥X), (e.symm b : ↥X)} : Set ↥X) = ⊤ := by
    have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective,
      Set.image_pair] at hmap
    exact hmap
  refine ⟨((e.symm a : ↥X) : G), (e.symm a).2, ((e.symm b : ↥X) : G), (e.symm b).2, ?_, ?_⟩
  · have hmap := congrArg (Subgroup.map X.subtype) hsub
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_pair] at hmap
    exact hmap
  · intro h
    apply hnc
    have h' : (e.symm a : ↥X) * (e.symm b : ↥X) = (e.symm b : ↥X) * (e.symm a : ↥X) :=
      Subtype.ext h
    simpa using congrArg e h'

theorem sl3Two_rootElt_cyc_ne :
    rootElt 0 1 (1 : ZMod 2) * cyc ≠ cyc * rootElt 0 1 (1 : ZMod 2) := by
  intro h
  have hx : rootElt 0 1 (1 : ZMod 2) ≠ rootElt 1 2 (1 : ZMod 2) := by
    intro hEq
    have hentry := congrArg (fun g : SL3 (ZMod 2) =>
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1)) hEq
    rw [coe_rootElt (show (0 : Fin 3) ≠ 1 by decide),
      coe_rootElt (show (1 : Fin 3) ≠ 2 by decide)] at hentry
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.isValue,
      Fin.mk_one, Fin.zero_eta, if_true, if_false, and_self, zero_add, add_zero] at hentry
    exact one_ne_zero hentry
  have hconj : cyc * rootElt 0 1 (1 : ZMod 2) * cyc⁻¹ = rootElt 0 1 (1 : ZMod 2) := by
    rw [← h]
    group
  have h12 : cyc * rootElt 0 1 (1 : ZMod 2) * cyc⁻¹ = rootElt 1 2 (1 : ZMod 2) := by
    simpa using cyc_conj_rootElt (i := (0 : Fin 3)) (j := (1 : Fin 3)) (c := (1 : ZMod 2))
  exact hx (hconj.symm.trans h12)

theorem sl3Two_closure_pair_eq_top :
    Subgroup.closure ({rootElt 0 1 (1 : ZMod 2), cyc} : Set (SL3 (ZMod 2))) = ⊤ := by
  set H : Subgroup (SL3 (ZMod 2)) :=
    Subgroup.closure ({rootElt 0 1 (1 : ZMod 2), cyc} : Set (SL3 (ZMod 2))) with hH
  have h01 : rootElt 0 1 (1 : ZMod 2) ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (by simp)
  have hcyc : cyc ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (by simp)
  have h12 : rootElt 1 2 (1 : ZMod 2) ∈ H := by
    have e : cyc * rootElt 0 1 (1 : ZMod 2) * cyc⁻¹ = rootElt 1 2 (1 : ZMod 2) := by
      simpa using cyc_conj_rootElt (i := (0 : Fin 3)) (j := (1 : Fin 3)) (c := (1 : ZMod 2))
    rw [← e]
    exact H.mul_mem (H.mul_mem hcyc h01) (H.inv_mem hcyc)
  have h20 : rootElt 2 0 (1 : ZMod 2) ∈ H := by
    have e : cyc * rootElt 1 2 (1 : ZMod 2) * cyc⁻¹ = rootElt 2 0 (1 : ZMod 2) := by
      simpa using cyc_conj_rootElt (i := (1 : Fin 3)) (j := (2 : Fin 3)) (c := (1 : ZMod 2))
    rw [← e]
    exact H.mul_mem (H.mul_mem hcyc h12) (H.inv_mem hcyc)
  have hcomm : ∀ {a b : SL3 (ZMod 2)}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H := by
    intro a b ha hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have h02 : rootElt 0 2 (1 : ZMod 2) ∈ H := by
    have e : ⁅rootElt 0 1 (1 : ZMod 2), rootElt 1 2 (1 : ZMod 2)⁆ =
        rootElt 0 2 (1 : ZMod 2) := by
      simpa using rootElt_commutator (i := (0 : Fin 3)) (j := (1 : Fin 3)) (l := (2 : Fin 3))
        (by decide) (by decide) (by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [← e]
    exact hcomm h01 h12
  have h10 : rootElt 1 0 (1 : ZMod 2) ∈ H := by
    have e : ⁅rootElt 1 2 (1 : ZMod 2), rootElt 2 0 (1 : ZMod 2)⁆ =
        rootElt 1 0 (1 : ZMod 2) := by
      simpa using rootElt_commutator (i := (1 : Fin 3)) (j := (2 : Fin 3)) (l := (0 : Fin 3))
        (by decide) (by decide) (by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [← e]
    exact hcomm h12 h20
  have h21 : rootElt 2 1 (1 : ZMod 2) ∈ H := by
    have e : ⁅rootElt 2 0 (1 : ZMod 2), rootElt 0 1 (1 : ZMod 2)⁆ =
        rootElt 2 1 (1 : ZMod 2) := by
      simpa using rootElt_commutator (i := (2 : Fin 3)) (j := (0 : Fin 3)) (l := (1 : Fin 3))
        (by decide) (by decide) (by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [← e]
    exact hcomm h20 h01
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hall : ∀ (i j : Fin 3) (c : ZMod 2), i ≠ j → rootElt i j c ∈ H := by
    intro i j c hij
    rcases hc2 c with rfl | rfl
    · rw [rootElt_zero]
      exact H.one_mem
    · fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact h01
        | exact h02
        | exact h10
        | exact h12
        | exact h20
        | exact h21
  exact eq_top_of_rootElt_mem hall

theorem kSimpleGen2_holds : KSimpleGen2 := by
  intro G _ X hX
  rcases hX with hL3 | hA5
  · obtain ⟨e⟩ :=
      CFSG.Quasithin.RonanE114.P7.exists_mulEquiv_sl3_of_isPSL (s16c167_isPSL_of_isL3 hL3)
    exact exists_closure_pair_of_mulEquiv X e sl3Two_closure_pair_eq_top
      sl3Two_rootElt_cyc_ne
  · obtain ⟨e⟩ := hA5
    exact exists_closure_pair_of_mulEquiv X e altFive_closure_pair_eq_top (by decide +kernel)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
