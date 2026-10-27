module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
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

/-! # Inverted elements in the linear omega inversion branch -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In the inversion branch of the linear omega trichotomy, the elements of
`U` inverted by the chosen involution form the Fitting subgroup of
`C_U(Q)`.  That subgroup is normal in `U` and lies in `F(U)`.

The hypothesis `hF_full` is the equation-(5) fact `F = C_{F(U)}(s)` (the
data only records the restricted `F = C_{F(U)∩M}(s)`); it is needed to
identify the `s`-fixed elements of `F(U)` with the fixed part `F`. -/
public theorem secondCase_linear_omega_invertedElements_le_fitting
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hF_full : od.F = centralizerIn c.FU (od.s : G))
    (hinvQ : ∀ x : G, x ∈ od.Q.map c.U.subtype →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) :
    ∃ I : Subgroup G,
      I = fittingSubgroupOf
        (c.U ⊓ Subgroup.centralizer
          ((od.Q.map c.U.subtype : Subgroup G) : Set G)) ∧
      (I : Set G) = invertedElements c.U (od.s : G) ∧
      IsNormalIn I c.U ∧ I ≤ c.FU := by
  classical
  let : Fact (Nat.Prime od.p) := ⟨od.hp_prime⟩
  let s : G := od.s
  let QG : Subgroup G := od.Q.map c.U.subtype
  have hsI : IsInvolution s := od.s_involution
  have hQGleFU : QG ≤ c.FU := secondCase_linear_omega_QG_le_FU c w d od
  have hQGnc : ¬ IsCyclic QG := by
    let eQ : od.Q ≃* QG :=
      Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
    intro hcyc
    exact od.Q_not_cyclic (eQ.isCyclic.mpr hcyc)
  have hQnotleM : ¬ QG ≤ w.M := by
    intro hQleM
    have hK0leK : od.K0 ≤ od.K := by
      rw [od.K0_eq]
      exact inf_le_right
    have hQGleY : QG ≤ c.FU ⊓ w.M := by
      intro q hq
      exact ⟨hQGleFU hq, hQleM hq⟩
    have hQGleKF : QG ≤ od.K0 ⊔ od.F := by
      rw [od.FU_inter_M_eq]
      exact hQGleY
    have hFleFU : od.F ≤ c.FU := by
      intro f hf
      rw [od.F_fixed] at hf
      exact hf.1.1
    have hFleNK0 : od.F ≤ Subgroup.normalizer (od.K0 : Set G) := by
      intro f hf
      apply Subgroup.centralizer_le_normalizer (od.K0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (od.F_centralizes_E hf) k
        (od.K_le_E (hK0leK hk)))
    have hInvK0 : ∀ q : G, q ∈ (od.K0 ⊔ od.F : Subgroup G) →
        s * q * s⁻¹ = q⁻¹ → q ∈ od.K0 := by
      intro q hq hqinv
      have hcarrier : ((od.K0 ⊔ od.F : Subgroup G) : Set G) =
          (od.K0 : Set G) * (od.F : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left od.K0 od.F hFleNK0
      have hqprod : q ∈ (od.K0 : Set G) * (od.F : Set G) := by
        change q ∈ ((od.K0 ⊔ od.F : Subgroup G) : Set G) at hq
        rw [hcarrier] at hq
        exact hq
      rcases hqprod with ⟨k, hk, f, hf, rfl⟩
      have hsk : s * k * s⁻¹ = k⁻¹ := by
        have hkI : k ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
          rw [← od.K_inverted]
          exact hK0leK hk
        simpa [s] using hkI.2
      have hsf : s * f * s⁻¹ = f := by
        rw [od.F_fixed] at hf
        have hfs : s * f = f * s :=
          (Subgroup.mem_centralizer_iff.mp hf.2 s (by simp [s]))
        calc
          s * f * s⁻¹ = f * s * s⁻¹ := by rw [hfs]
          _ = f := by simp
      have hskf : s * (k * f) * s⁻¹ = k⁻¹ * f := by
        calc
          s * (k * f) * s⁻¹ =
              (s * k * s⁻¹) * (s * f * s⁻¹) := by group
          _ = k⁻¹ * f := by rw [hsk, hsf]
      have hcomm : k * f = f * k :=
        (Subgroup.mem_centralizer_iff.mp (od.F_centralizes_E hf) k
          (od.K_le_E (hK0leK hk)))
      have h1 : k⁻¹ * f = f⁻¹ * k⁻¹ := by
        calc
          k⁻¹ * f = s * (k * f) * s⁻¹ := hskf.symm
          _ = (k * f)⁻¹ := hqinv
          _ = f⁻¹ * k⁻¹ := by group
      have h1' : k⁻¹ * f = k⁻¹ * f⁻¹ := by
        calc
          k⁻¹ * f = f⁻¹ * k⁻¹ := h1
          _ = k⁻¹ * f⁻¹ := by
            calc
              f⁻¹ * k⁻¹ = (k * f)⁻¹ := by group
              _ = (f * k)⁻¹ := by rw [hcomm]
              _ = k⁻¹ * f⁻¹ := by group
      have hf_inv : f = f⁻¹ := by
        calc
          f = k * (k⁻¹ * f) := by group
          _ = k * (k⁻¹ * f⁻¹) := by rw [h1']
          _ = f⁻¹ := by group
      have hsq : f ^ 2 = 1 := by
        calc
          f ^ 2 = f * f := pow_two f
          _ = f * f⁻¹ := by
            conv_rhs =>
              rw [← hf_inv]
          _ = 1 := by simp
      have hUodd : Odd (Nat.card c.U) := by
        change Odd (Nat.card (oddCoreOf c.H))
        exact odd_card_oddCoreOf c.H
      have hfU : f ∈ c.U := (fittingSubgroupOf_le c.U) (hFleFU hf)
      have hord2 : orderOf f ∣ 2 :=
        (orderOf_dvd_iff_pow_eq_one (x := f) (n := 2)).mpr hsq
      have hordU : orderOf f ∣ Nat.card (↥c.U) :=
        Subgroup.orderOf_dvd_natCard c.U hfU
      have hcop : Nat.Coprime 2 (Nat.card (↥c.U)) :=
        Nat.coprime_two_left.mpr hUodd
      have hord1 : orderOf f ∣ 1 := by
        have hdvd : orderOf f ∣ Nat.gcd 2 (Nat.card (↥c.U)) :=
          Nat.dvd_gcd hord2 hordU
        simpa [hcop.gcd_eq_one] using hdvd
      have hf1 : f = 1 := by
        have hord_eq : orderOf f = 1 := Nat.dvd_one.mp hord1
        exact (orderOf_eq_one_iff.mp hord_eq)
      simpa [hf1] using hk
    have hQGleK0 : QG ≤ od.K0 := by
      intro q hq
      exact hInvK0 q (hQGleKF hq) (hinvQ q hq)
    let : IsCyclic od.K := od.K_cyclic
    have hK0cyc : IsCyclic od.K0 := Subgroup.isCyclic_of_le hK0leK
    let : IsCyclic od.K0 := hK0cyc
    have hQGcyc : IsCyclic QG := Subgroup.isCyclic_of_le hQGleK0
    let eQ : od.Q ≃* QG :=
      Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
    exact od.Q_not_cyclic (eQ.isCyclic.mpr hQGcyc)
  have hQnormalU : IsNormalIn QG c.U := by
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q od.Q_characteristic
      (⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩)
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
      (centralizerSetup_U_isNormalIn_H c)
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
      rw [hF_full]
      refine ⟨hxFU, ?_⟩
      change x ∈ Subgroup.centralizer ({(s : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmul := congrArg (fun z : G => z * s) hxfix
      have hcomm : s * x = x * s := by simpa [mul_assoc] using hmul
      exact hcomm.symm
    have hxC : x ∈ C := fittingSubgroupOf_le C hxFC
    by_contra hxne
    have hQGleM : QG ≤ w.M := by
      intro q hq
      by_contra hqM
      have hqx : q * x = x * q :=
        (Subgroup.mem_centralizer_iff.mp hxC.2 q hq)
      have hxconjF : x ∈ conjugateSubgroup od.F q := by
        refine Subgroup.mem_map.mpr ⟨q⁻¹ * x * q, ?_, ?_⟩
        · have hqxq : q * x * q⁻¹ = x := by
            calc
              q * x * q⁻¹ = x * q * q⁻¹ := by rw [hqx]
              _ = x := by simp
          have hpre : q⁻¹ * x * q = x := by
            calc
              q⁻¹ * x * q = q⁻¹ * (x * q) := by rw [mul_assoc]
              _ = q⁻¹ * (q * x) := by rw [hqx.symm]
              _ = x := by group
          rw [hpre]
          exact hxF
        · simp [MulAut.conj_apply]
          group
      have hxcap : x ∈ od.F ⊓ conjugateSubgroup od.F q := ⟨hxF, hxconjF⟩
      have hbot : od.F ⊓ conjugateSubgroup od.F q = ⊥ := od.F_TI q hqM
      have hx1 : x = 1 := by
        have hxbot : x ∈ (⊥ : Subgroup G) := by rwa [hbot] at hxcap
        exact Subgroup.mem_bot.mp hxbot
      exact hxne hx1
    exact hQnotleM hQGleM
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
