module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaInvertedElements
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-! # Normality in the inversion branch of the A7 omega argument -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the inversion branch, the elements of `U` inverted by the chosen
reflection form a subgroup normal in `Hhat`. -/
public theorem secondCase_a7_omega_invertedElements_normal_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hFnotleQ : ¬ od.F ≤ od.Q.map c.FU.subtype)
    (hinvQ : ∀ x : G, x ∈ od.Q.map c.FU.subtype →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) :
    ∃ I : Subgroup G,
      (I : Set G) = invertedElements c.U (od.s : G) ∧
      IsNormalIn I c.Hhat := by
  let QG : Subgroup G := od.Q.map c.FU.subtype
  let C : Subgroup G := c.U ⊓ Subgroup.centralizer (QG : Set G)
  obtain ⟨I, hIdef, hIeq, _hInormalU, _hIleFU⟩ :=
    secondCase_a7_omega_invertedElements_le_fitting
      c w d od hFnotleQ hinvQ
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hUeqOdd : c.U = oddCoreOf c.Hhat := h26.1
  have hUnormalHhat : IsNormalIn c.U c.Hhat := by
    rw [hUeqOdd]
    refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.Hhat) * x0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
        (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
          x0 hx0 ⟨h, hh⟩, by simp⟩
  have hFUnormalHhat : IsNormalIn c.FU c.Hhat := by
    change IsNormalIn ((fittingSubgroup c.U).map c.U.subtype) c.Hhat
    exact map_characteristic_isNormalIn_of_isNormalIn
      (fittingSubgroup c.U) (by infer_instance) hUnormalHhat
  have hQnormalHhat : IsNormalIn QG c.Hhat := by
    exact map_characteristic_isNormalIn_of_isNormalIn
      od.Q od.Q_characteristic hFUnormalHhat
  have hCnormalHhat : IsNormalIn C c.Hhat := by
    refine ⟨inf_le_left.trans hUnormalHhat.1, ?_⟩
    intro h hh x hx
    refine ⟨hUnormalHhat.2 h hh x hx.1, ?_⟩
    change h * x * h⁻¹ ∈ Subgroup.centralizer (QG : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hbackQ : h⁻¹ * q * h ∈ QG := by
      simpa using hQnormalHhat.2 h⁻¹ (c.Hhat.inv_mem hh) q hq
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2)
      (h⁻¹ * q * h) hbackQ
    calc
      q * (h * x * h⁻¹) = h * (h⁻¹ * q * h) * x * h⁻¹ := by group
      _ = h * x * (h⁻¹ * q * h) * h⁻¹ := by
        simpa [mul_assoc] using
          congrArg (fun z : G => h * z * h⁻¹) hcomm
      _ = (h * x * h⁻¹) * q := by group
  have hFCnormalHhat : IsNormalIn (fittingSubgroupOf C) c.Hhat := by
    change IsNormalIn ((fittingSubgroup C).map C.subtype) c.Hhat
    exact map_characteristic_isNormalIn_of_isNormalIn
      (fittingSubgroup C) (by infer_instance) hCnormalHhat
  refine ⟨I, hIeq, ?_⟩
  rw [hIdef]
  exact hFCnormalHhat

end CFSG.GorensteinWalter
