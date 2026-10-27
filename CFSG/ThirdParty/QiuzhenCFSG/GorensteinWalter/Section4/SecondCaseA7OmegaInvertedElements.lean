module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaTrichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddInvertedCentralizesNormalInverted
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Inverted elements in the A7 omega branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the inversion branch of the A7 omega trichotomy, the elements of `U`
inverted by the chosen involution form the Fitting subgroup of `C_U(Q)`.
That subgroup is normal in `U` and lies in `F(U)`. -/
public theorem secondCase_a7_omega_invertedElements_le_fitting
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hFnotleQ : ¬ od.F ≤ od.Q.map c.FU.subtype)
    (hinvQ : ∀ x : G, x ∈ od.Q.map c.FU.subtype →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) :
    ∃ I : Subgroup G,
      I = fittingSubgroupOf
        (c.U ⊓ Subgroup.centralizer
          ((od.Q.map c.FU.subtype : Subgroup G) : Set G)) ∧
      (I : Set G) = invertedElements c.U (od.s : G) ∧
      IsNormalIn I c.U ∧ I ≤ c.FU := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let s : G := od.s
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hsI : IsInvolution s := od.s_involution
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  have hQGnc : ¬ IsCyclic QG := by
    let eQ : od.Q ≃* QG :=
      Subgroup.equivMapOfInjective od.Q c.FU.subtype c.FU.subtype_injective
    intro hcyc
    exact od.Q_not_cyclic (eQ.isCyclic.mpr hcyc)
  have hAcard : Nat.card (od.K ⊔ od.F : Subgroup G) = 9 := by
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hQnotleM : ¬ QG ≤ w.M := by
    intro hQleM
    have hQleA : QG ≤ od.K ⊔ od.F := by
      rw [od.FU_inter_M_eq]
      exact le_inf hQGleFU hQleM
    have hQdiv : Nat.card QG ∣ 3 ^ 2 := by
      norm_num
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hQleA
    obtain ⟨n, hn, hQcard⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp hQdiv
    have hQcard9 : Nat.card QG = 9 := by
      interval_cases n
      · exfalso
        apply hQGnc
        have hbot : QG = ⊥ := by
          apply (Subgroup.eq_bot_iff_card (H := QG)).mpr
          simpa using hQcard
        rw [hbot]
        infer_instance
      · exfalso
        apply hQGnc
        apply isCyclic_of_prime_card (p := 3)
        simpa using hQcard
      · simpa using hQcard
    have hQeqA : QG = od.K ⊔ od.F :=
      Subgroup.eq_of_le_of_card_ge hQleA (by rw [hQcard9, hAcard])
    apply hFnotleQ
    change od.F ≤ QG
    rw [hQeqA]
    exact le_sup_right
  have hQnormalU : IsNormalIn QG c.U := by
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q
      od.Q_characteristic (fittingSubgroupOf_isNormalIn c.U)
  let C : Subgroup G := c.U ⊓ Subgroup.centralizer (QG : Set G)
  have hCleU : C ≤ c.U := inf_le_left
  have hCnormalU : IsNormalIn C c.U := by
    refine ⟨hCleU, ?_⟩
    intro u hu x hx
    refine ⟨c.U.mul_mem (c.U.mul_mem hu (hCleU hx)) (c.U.inv_mem hu), ?_⟩
    change u * x * u⁻¹ ∈ Subgroup.centralizer (QG : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hbackQ : u⁻¹ * q * u ∈ QG :=
      by simpa using hQnormalU.2 u⁻¹ (c.U.inv_mem hu) q hq
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2)
      (u⁻¹ * q * u) hbackQ
    calc
      q * (u * x * u⁻¹) = u * (u⁻¹ * q * u) * x * u⁻¹ := by group
      _ = u * x * (u⁻¹ * q * u) * u⁻¹ := by
        simpa [mul_assoc] using
          congrArg (fun z : G => u * z * u⁻¹) hcomm
      _ = (u * x * u⁻¹) * q := by group
  let FC : Subgroup G := fittingSubgroupOf C
  have hFCnormalU : IsNormalIn FC c.U := by
    change IsNormalIn ((fittingSubgroup C).map C.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn
      (fittingSubgroup C) (by infer_instance) hCnormalU
  have hFCleFU : FC ≤ c.FU :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent hFCnormalU.1 hFCnormalU
      (fittingSubgroupOf_isNilpotent C)
  have hUnormalH : IsNormalIn c.U c.H :=
    centralizerSetup_U_isNormalIn_H c
  have hQnormalH : IsNormalIn QG c.H :=
    map_characteristic_isNormalIn_of_isNormalIn od.Q od.Q_characteristic
      (centralizerSetup_FU_isNormalIn_H c)
  have hsU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ ∈ c.U :=
    hUnormalH.2 s od.s_mem_H
  have hsQ : ∀ x : G, x ∈ QG → s * x * s⁻¹ ∈ QG :=
    hQnormalH.2 s od.s_mem_H
  have hsC : ∀ x : G, x ∈ C → s * x * s⁻¹ ∈ C := by
    intro x hx
    refine ⟨hsU x hx.1, ?_⟩
    change s * x * s⁻¹ ∈ Subgroup.centralizer (QG : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hsqQ : s⁻¹ * q * s ∈ QG := by
      have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hsI.2)
      rw [hsInv]
      simpa [hsInv] using hsQ q hq
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2)
      (s⁻¹ * q * s) hsqQ
    calc
      q * (s * x * s⁻¹) = s * (s⁻¹ * q * s) * x * s⁻¹ := by group
      _ = s * x * (s⁻¹ * q * s) * s⁻¹ := by
        simpa [mul_assoc] using
          congrArg (fun z : G => s * z * s⁻¹) hcomm
      _ = (s * x * s⁻¹) * q := by group
  have hsNormC : s ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hsC x
    · intro hx
      have htwice := hsC (s * x * s⁻¹) hx
      have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hsI.2)
      have hback : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hsInv]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by group
          _ = x := by simp [show s * s = 1 by simpa [pow_two] using hsI.2]
      rw [hback] at htwice
      exact htwice
  have hCnormalNorm : IsNormalIn C (Subgroup.normalizer (C : Set G)) := by
    refine ⟨Subgroup.le_normalizer, ?_⟩
    intro n hn x hx
    exact (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hFCnormalNorm :
      IsNormalIn FC (Subgroup.normalizer (C : Set G)) := by
    change IsNormalIn ((fittingSubgroup C).map C.subtype)
      (Subgroup.normalizer (C : Set G))
    exact map_characteristic_isNormalIn_of_isNormalIn
      (fittingSubgroup C) (by infer_instance) hCnormalNorm
  have hsFC : ∀ x : G, x ∈ FC → s * x * s⁻¹ ∈ FC :=
    hFCnormalNorm.2 s hsNormC
  have hfixedOne : ∀ x : G, x ∈ FC → s * x * s⁻¹ = x → x = 1 := by
    intro x hxFC hxfix
    have hxFU : x ∈ c.FU := hFCleFU hxFC
    have hxF : x ∈ od.F := by
      rw [od.F_fixed]
      refine ⟨hxFU, ?_⟩
      change x ∈ Subgroup.centralizer ({s} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmul := congrArg (fun z : G => z * s) hxfix
      have hcomm : s * x = x * s := by simpa [mul_assoc] using hmul
      exact hcomm.symm
    have hxC : x ∈ C := fittingSubgroupOf_le C hxFC
    by_contra hxne
    have hF_eq_zpowers : od.F = Subgroup.zpowers x := by
      apply le_antisymm
      · intro f hf
        let xF : od.F := ⟨x, hxF⟩
        let fF : od.F := ⟨f, hf⟩
        have hxFne : xF ≠ 1 := by
          intro h
          apply hxne
          exact congrArg Subtype.val h
        have hfz := mem_zpowers_of_prime_card
          (G := od.F) (p := 3) od.F_card (g := xF) (g' := fF) hxFne
        rcases Subgroup.mem_zpowers_iff.mp hfz with ⟨n, hn⟩
        apply Subgroup.mem_zpowers_iff.mpr
        exact ⟨n, congrArg Subtype.val hn⟩
      · exact Subgroup.zpowers_le.mpr hxF
    apply hQnotleM
    intro q hq
    have hqconjx : q * x * q⁻¹ = x := by
      have hxcomm := (Subgroup.mem_centralizer_iff.mp hxC.2) q hq
      calc
        q * x * q⁻¹ = x * q * q⁻¹ := by rw [hxcomm.symm]
        _ = x := by simp
    have hqNormF : q ∈ Subgroup.normalizer (od.F : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hF_eq_zpowers,
        MonoidHom.map_zpowers]
      congr 1
    rw [od.F_normalizer] at hqNormF
    exact hqNormF
  let sFC : Subgroup.normalizer (FC : Set G) :=
    ⟨s, le_normalizer_of_isNormalIn hFCnormalNorm hsNormC⟩
  let phi : MulAut FC := FC.normalizerMonoidHom sFC
  have hphiInv : Function.Involutive phi := by
    intro x
    apply Subtype.ext
    simp only [phi, sFC, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using hsI.2)
    rw [hsInv]
    calc
      s * (s * (x : G) * s) * s = (s * s) * (x : G) * (s * s) := by group
      _ = (x : G) := by
        simp [show s * s = 1 by simpa [pow_two] using hsI.2]
  have hphiFPF : MonoidHom.FixedPointFree phi := by
    intro x hx
    apply Subtype.ext
    apply hfixedOne x x.2
    simpa [phi, sFC, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hx
  have hFCinv : ∀ x : G, x ∈ FC → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    let xFC : FC := ⟨x, hx⟩
    have hinv := congrFun (hphiFPF.coe_eq_inv_of_involutive hphiInv) xFC
    simpa [phi, sFC, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hinv
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hCodd : Odd (Nat.card C) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hCleU)
  have hInvLeFC : ∀ x : G, x ∈ invertedElements c.U s → x ∈ FC := by
    intro x hxInv
    have hxCentQ : x ∈ Subgroup.centralizer (QG : Set G) :=
      inverted_element_centralizes_normal_inverted_subgroup
        c.U QG s hUodd hsU hQnormalU hinvQ hxInv
    have hxC : x ∈ C := ⟨hxInv.1, hxCentQ⟩
    have hxCentFC : x ∈ Subgroup.centralizer (FC : Set G) :=
      inverted_element_centralizes_normal_inverted_subgroup
        c.U FC s hUodd hsU hFCnormalU hFCinv hxInv
    have hCsolv : IsSolvable C := odd_order_theorem C hCodd
    have hxFC : x ∈ FC :=
      fact_1_2_centralizer_fitting_le_fitting C hCsolv ⟨hxC, hxCentFC⟩
    exact hxFC
  have hFCeqInv : (FC : Set G) = invertedElements c.U s := by
    ext x
    constructor
    · intro hx
      exact ⟨hCleU (fittingSubgroupOf_le C hx), hFCinv x hx⟩
    · exact hInvLeFC x
  exact ⟨FC, rfl, hFCeqInv, hFCnormalU, hFCleFU⟩

end CFSG.GorensteinWalter
