module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationSix
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The reverse equation-(7) two-core containment
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `O2(Hhat)` lies in `O2(H \inter M)`. -/
public theorem secondCase_a7_twoCore_Hhat_le_twoCore_inter
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    twoCoreOf c.Hhat ≤ twoCoreOf (c.H ⊓ w.M) := by
  classical
  obtain ⟨K, B, s, _hsI, _hsH, hK_eq, hK_cyc, hB_def, hjoinX, hKcard,
      _hKleE,
      K0, F, hK0_def, hF_def, hF_eq, hjoinY, hFnormalM,
      hFcentE, hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  let C : Subgroup G := c.H ⊓ w.M
  let O : Subgroup G := twoCoreOf c.Hhat
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hOcentU : O ≤ Subgroup.centralizer (c.U : Set G) := by
    change twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G)
    rw [← h26.2.1]
    exact inf_le_right
  have hOleH : O ≤ c.H := by
    change twoCoreOf c.Hhat ≤ c.H
    rw [← h26.2.1]
    exact inf_le_left.trans (centralizerSetup_S_le_H c)
  have hFleU : F ≤ c.U := by
    intro f hf
    rw [hF_def] at hf
    exact fittingSubgroupOf_le c.U hf.1
  have hOcentF : O ≤ Subgroup.centralizer (F : Set G) :=
    hOcentU.trans (Subgroup.centralizer_le (SetLike.coe_mono hFleU))
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card F = 1 := by rw [hbot]; simp
    omega
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hOleM : O ≤ w.M := by
    intro x hx
    have hxN := Subgroup.centralizer_le_normalizer (F : Set G) (hOcentF hx)
    rwa [hNFeq] at hxN
  have hOleC : O ≤ C := fun x hx => ⟨hOleH hx, hOleM hx⟩
  have hOnormalHhat : IsNormalIn O c.Hhat := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · intro z hz x hx
      rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨z, hz⟩ : c.Hhat) * x0 * (⟨z, hz⟩ : c.Hhat)⁻¹,
          (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
            x0 hx0 (⟨z, hz⟩ : c.Hhat), rfl⟩
  have hCleHhat : C ≤ c.Hhat :=
    inf_le_left.trans c.H_le_Hhat
  have hOnormalC : IsNormalIn O C := by
    refine ⟨hOleC, ?_⟩
    intro z hz x hx
    exact hOnormalHhat.2 z (hCleHhat hz) x hx
  let OC : Subgroup C := O.subgroupOf C
  have hOCnormal : OC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleC]
    intro x z hx hz
    exact hOnormalC.2 z hz x hx
  have hOp : IsPGroup 2 O := by
    change IsPGroup 2 ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact (pCore_isPGroup (p := 2) (G := c.Hhat)).map c.Hhat.subtype
  have hOCp : IsPGroup 2 OC :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOleC).symm
  have hOCle : OC ≤ pCore 2 C := le_sSup ⟨hOCnormal, hOCp⟩
  have hmaple := Subgroup.map_mono (f := C.subtype) hOCle
  have hmapOC : OC.map C.subtype = O :=
    Subgroup.map_subgroupOf_eq_of_le hOleC
  simpa [O, C, twoCoreOf, hmapOC] using hmaple

end CFSG.GorensteinWalter
