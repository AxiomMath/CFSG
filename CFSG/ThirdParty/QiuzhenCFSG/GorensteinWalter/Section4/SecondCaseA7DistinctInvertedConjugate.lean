module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaDataDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenDistinctInvertedConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KleinBranch
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7InvolutionsInComponent
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A distinct inverted conjugate in the A7 second case

The finite A7 model supplies a conjugator in the quotient of the selected
component by its odd center.  Square-one uniqueness across that central
kernel lifts commutation with the selected reflection and normalization of
the Klein-four two-core back to the component.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The synchronized order-three subgroup has a distinct conjugate inside
`Hhat ∩ E`, still inverted by the selected reflection.  The conjugator lies
in `E` and centralizes that reflection. -/
public theorem
    secondCase_a7_exists_distinct_inverted_conjugate_in_Hhat_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    ∃ e : d.E, ∃ Ke : Subgroup G,
      Ke = od.K.map (MulAut.conj (e : G)).toMonoidHom ∧
      (e : G) * (od.s : G) = (od.s : G) * (e : G) ∧
      (e : G) ^ 2 ∈ c.Hhat ∧
      Ke ≠ od.K ∧
      Ke ≤ c.Hhat ⊓ d.E ∧
      ∀ x : G, x ∈ Ke →
        (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
  classical
  let E : Subgroup G := d.E
  let Z : Subgroup E := Subgroup.center E
  let : Z.Normal := by
    dsimp [Z]
    infer_instance
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let KE : Subgroup E := od.K.subgroupOf E
  have hKleU : od.K ≤ c.U :=
    le_sup_left.trans (od.U_inter_M_eq.le.trans inf_le_left)
  have hsInvK : ∀ x : G, x ∈ od.K →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxInv : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
      rw [← od.K_inverted]
      exact hx
    exact hxInv.2
  have hKEinfZ : KE ⊓ Z = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxK : (x : G) ∈ od.K := Subgroup.mem_subgroupOf.mp hx.1
    have hxInv := hsInvK (x : G) hxK
    have hxcommE : (od.s : d.E) * (x : E) = (x : E) * (od.s : d.E) :=
      Subgroup.mem_center_iff.mp hx.2 (od.s : d.E)
    have hxcomm : (od.s : G) * (x : G) = (x : G) * (od.s : G) :=
      congrArg Subtype.val hxcommE
    have hxFix : (od.s : G) * (x : G) * (od.s : G)⁻¹ = (x : G) := by
      calc
        (od.s : G) * (x : G) * (od.s : G)⁻¹ =
            ((x : G) * (od.s : G)) * (od.s : G)⁻¹ := by rw [hxcomm]
        _ = (x : G) := by simp [mul_assoc]
    have hxEqInv : (x : G) = (x : G)⁻¹ := hxFix.symm.trans hxInv
    have hx2 : (x : G) ^ 2 = 1 := by
      calc
        (x : G) ^ 2 = (x : G) * (x : G) := pow_two _
        _ = (x : G)⁻¹ * (x : G) :=
          congrArg (fun y : G => y * (x : G)) hxEqInv
        _ = 1 := inv_mul_cancel _
    have hord2 : orderOf (x : G) ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := (x : G)) (n := 2)).mpr hx2
    have hord3 : orderOf (x : G) ∣ 3 := by
      rw [← od.K_card]
      exact Subgroup.orderOf_dvd_natCard od.K hxK
    have hord1 : orderOf (x : G) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num) hord2 hord3
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp hord1
  have hKEcard : Nat.card KE = 3 := by
    calc
      Nat.card KE = Nat.card od.K :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe od.K_le_E).toEquiv
      _ = 3 := od.K_card
  let Ubar : Subgroup (E ⧸ Z) := KE.map q
  have hUbarcard : Nat.card Ubar = 3 := by
    have hformula := card_map_eq_card_mul_card_ker q KE
    have hker : q.ker = Z := by
      simp [q]
    rw [hker, hKEinfZ, Subgroup.card_bot, mul_one] at hformula
    exact hformula.symm.trans hKEcard
  have hkleinCore := (secondCase_a7_klein_branch hmin c w d hA7 hmodel).1
  let V : Subgroup G := twoCoreOf c.Hhat
  have hVK : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hkleinCore
  have hVleC : V ≤ c.H ⊓ w.M := by
    dsimp [V]
    rw [← secondCase_a7_twoCore_inter_eq_twoCore_Hhat
      hmin c w d hA7 hmodel]
    exact Subgroup.map_subtype_le (pCore 2 (↥(c.H ⊓ w.M)))
  have hVleE : V ≤ E := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact E.one_mem
    · have hv2 : v ^ 2 = 1 := by
        let vV : V := ⟨v, hv⟩
        simpa [pow_two] using congrArg Subtype.val (hVK.mul_self vV)
      exact secondCase_a7_involutions_in_component hmin c w d hA7 hmodel
        v (hVleC hv).2 ⟨hv1, hv2⟩
  let VE : Subgroup E := V.subgroupOf E
  let eVE : VE ≃* V := Subgroup.subgroupOfEquivOfLe hVleE
  have hVEK : IsKleinFour VE := {
    card_four := (Nat.card_congr eVE.toEquiv).trans hVK.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eVE).trans hVK.exponent_two
  }
  let Vbar : Subgroup (E ⧸ Z) := VE.map q
  have hVbarK : IsKleinFour Vbar := by
    let fV : VE →* E ⧸ Z := q.comp VE.subtype
    have hfVinj : Function.Injective fV := by
      apply (MonoidHom.ker_eq_bot_iff fV).mp
      apply le_bot_iff.mp
      intro v hv
      rw [Subgroup.mem_bot]
      have hqv : q (v : E) = 1 := MonoidHom.mem_ker.mp hv
      have hvZ : (v : E) ∈ Z :=
        (QuotientGroup.eq_one_iff (N := Z) (v : E)).mp hqv
      have hv2 : (v : E) ^ 2 = 1 := by
        simpa [pow_two] using congrArg Subtype.val (hVEK.mul_self v)
      have hord2 : orderOf (v : E) ∣ 2 :=
        (orderOf_dvd_iff_pow_eq_one (x := (v : E)) (n := 2)).mpr hv2
      have hordZ : orderOf (v : E) ∣ Nat.card Z :=
        Subgroup.orderOf_dvd_natCard Z hvZ
      have hord1 : orderOf (v : E) = 1 :=
        Nat.eq_one_of_dvd_coprimes
          (Nat.coprime_two_left.mpr d.center_odd) hord2 hordZ
      exact Subtype.ext (orderOf_eq_one_iff.mp hord1)
    let eVbar : VE ≃* fV.range :=
      MulEquiv.ofBijective fV.rangeRestrict
        ⟨fun a b h => hfVinj (congrArg Subtype.val h),
          MonoidHom.rangeRestrict_surjective fV⟩
    have hrange : fV.range = Vbar := by
      change (q.comp VE.subtype).range = VE.map q
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hrangeK : IsKleinFour fV.range := {
      card_four := (Nat.card_congr eVbar.toEquiv).symm.trans hVEK.card_four
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv eVbar).symm.trans hVEK.exponent_two
    }
    rw [← hrange]
    exact hrangeK
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    dsimp [V]
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_right
  have hVEcentKE : VE ≤ Subgroup.centralizer (KE : Set E) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hcomm := (Subgroup.mem_centralizer_iff.mp
      (hVcentU (Subgroup.mem_subgroupOf.mp hv))) (k : G)
      (hKleU (Subgroup.mem_subgroupOf.mp hk))
    exact Subtype.ext hcomm
  have hVbarcent : Vbar ≤ Subgroup.centralizer (Ubar : Set (E ⧸ Z)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    rcases Subgroup.mem_map.mp hk with ⟨k0, hk0, rfl⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hVEcentKE hv0)) k0 hk0
    simpa using congrArg q hcomm
  let eQ : (E ⧸ Z) ≃* alternatingGroup (Fin 7) := hA7.some
  let U7 : Subgroup (alternatingGroup (Fin 7)) := Ubar.map eQ.toMonoidHom
  let V7 : Subgroup (alternatingGroup (Fin 7)) := Vbar.map eQ.toMonoidHom
  let s7 : alternatingGroup (Fin 7) := eQ (q od.s)
  have hU7card : Nat.card U7 = 3 := by
    rw [Subgroup.card_map_of_injective eQ.injective, hUbarcard]
  have hV7K : IsKleinFour V7 :=
    isKleinFour_map_mulEquiv_cross Vbar hVbarK eQ
  have hV7cent : V7 ≤ Subgroup.centralizer (U7 : Set _) :=
    centralizer_map_le_of_mulEquiv eQ Ubar Vbar hVbarcent
  have hqsI : IsInvolution (q od.s) := by
    have hsIE : IsInvolution (od.s : E) := by
      constructor
      · intro hs1
        exact od.s_involution.1 (congrArg Subtype.val hs1)
      · exact Subtype.ext od.s_involution.2
    constructor
    · intro hq1
      have hsZ : (od.s : E) ∈ Z :=
        (QuotientGroup.eq_one_iff (N := Z) (od.s : E)).mp hq1
      have h2dvd : 2 ∣ Nat.card Z := by
        rw [← orderOf_eq_prime hsIE.2 hsIE.1]
        exact Subgroup.orderOf_dvd_natCard Z hsZ
      exact d.center_odd.not_two_dvd_nat h2dvd
    · simpa [map_pow] using congrArg q hsIE.2
  have hs7I : IsInvolution s7 := by
    constructor
    · intro hs1
      apply hqsI.1
      apply eQ.injective
      simpa [s7] using hs1
    · simpa [s7, map_pow] using congrArg eQ hqsI.2
  have hs7Inv : ∀ x, x ∈ U7 → s7 * x * s7⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xbar, hxbar, rfl⟩
    rcases Subgroup.mem_map.mp hxbar with ⟨xE, hxE, rfl⟩
    have hxInv := hsInvK (xE : G) (Subgroup.mem_subgroupOf.mp hxE)
    have hxInvE : (od.s : E) * xE * (od.s : E)⁻¹ = xE⁻¹ :=
      Subtype.ext hxInv
    simpa [s7, map_mul, map_inv] using congrArg eQ (congrArg q hxInvE)
  obtain ⟨g7, hg7s, hg7sq, hU7ne, hU7norm, _hU7inv⟩ :=
    aSeven_exists_distinct_inverted_conjugate_normalizing_kleinFour
      U7 V7 hU7card hV7K hV7cent s7 hs7I hs7Inv
  let gbar : E ⧸ Z := eQ.symm g7
  obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective Z gbar
  have he7 : eQ (q e) = g7 := by
    rw [he]
    exact eQ.apply_symm_apply g7
  have sqOne_eq_of_q_eq {a b : E}
      (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : q a = q b) : a = b := by
    let z : E := a * b⁻¹
    have hzZ : z ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) z).mp
      change q (a * b⁻¹) = 1
      rw [map_mul, map_inv, hab]
      simp
    have hzcent : z ∈ Subgroup.center E := hzZ
    have hzcomm : b * z = z * b := Subgroup.mem_center_iff.mp hzcent b
    have haeq : a = z * b := by
      dsimp [z]
      group
    have hzb2 : (z * b) ^ 2 = 1 := by rw [← haeq]; exact ha2
    have hprod : (z * b) * (z * b) = (z * z) * (b * b) := by
      calc
        (z * b) * (z * b) = z * (b * z) * b := by group
        _ = z * (z * b) * b := by rw [hzcomm]
        _ = (z * z) * (b * b) := by group
    have hz2 : z ^ 2 = 1 := by
      rw [pow_two]
      calc
        z * z = (z * z) * (b * b) := by
          rw [show b * b = 1 by simpa [pow_two] using hb2, mul_one]
        _ = (z * b) * (z * b) := hprod.symm
        _ = 1 := by simpa [pow_two] using hzb2
    have hord2 : orderOf z ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := z) (n := 2)).mpr hz2
    have hordZ : orderOf z ∣ Nat.card Z :=
      Subgroup.orderOf_dvd_natCard Z hzZ
    have hord1 : orderOf z = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.mpr d.center_odd) hord2 hordZ
    have hz1 : z = 1 := orderOf_eq_one_iff.mp hord1
    rw [haeq, hz1, one_mul]
  have heConjS : e * od.s * e⁻¹ = od.s := by
    have hsE2 : (od.s : E) ^ 2 = 1 := by
      apply Subtype.ext
      exact od.s_involution.2
    refine sqOne_eq_of_q_eq
      (a := e * (od.s : E) * e⁻¹) (b := (od.s : E)) ?_ hsE2 ?_
    · rw [pow_two]
      calc
        (e * (od.s : E) * e⁻¹) * (e * (od.s : E) * e⁻¹) =
            e * ((od.s : E) * (od.s : E)) * e⁻¹ := by group
        _ = 1 := by
          rw [show (od.s : E) * (od.s : E) = 1 by
            simpa [pow_two] using hsE2]
          simp
    · apply eQ.injective
      simp only [map_mul, map_inv]
      rw [he7]
      change g7 * s7 * g7⁻¹ = s7
      calc
        g7 * s7 * g7⁻¹ = (g7 * s7) * g7⁻¹ := by group
        _ = (s7 * g7) * g7⁻¹ := by rw [hg7s]
        _ = s7 := by simp
  have heCommE : e * od.s = od.s * e := by
    calc
      e * od.s = (e * od.s * e⁻¹) * e := by group
      _ = od.s * e := by rw [heConjS]
  have heComm : (e : G) * (od.s : G) = (od.s : G) * (e : G) :=
    congrArg Subtype.val heCommE
  have heSqQ : q (e ^ 2) = q od.s := by
    apply eQ.injective
    simpa [s7, he7, map_pow] using hg7sq
  let z : E := e ^ 2 * (od.s : E)⁻¹
  have hzZ : z ∈ Z := by
    apply (QuotientGroup.eq_one_iff (N := Z) z).mp
    change q (e ^ 2 * (od.s : E)⁻¹) = 1
    rw [map_mul, map_inv, heSqQ]
    simp
  have hzH : (z : G) ∈ c.H := by
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hcommE := Subgroup.mem_center_iff.mp hzZ
      (⟨c.t, d.t_mem_E⟩ : E)
    exact (congrArg Subtype.val hcommE).symm
  have heSqHhat : (e : G) ^ 2 ∈ c.Hhat := by
    have hzHhat : (z : G) ∈ c.Hhat := c.H_le_Hhat hzH
    have hsHhat : (od.s : G) ∈ c.Hhat := c.H_le_Hhat od.s_mem_H
    have heq : (e : G) ^ 2 = (z : G) * (od.s : G) := by
      dsimp [z]
      group
    rw [heq]
    exact c.Hhat.mul_mem hzHhat hsHhat
  let eg : G := e
  let Ke : Subgroup G := od.K.map (MulAut.conj eg).toMonoidHom
  have hKeLeE : Ke ≤ E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    exact E.mul_mem (E.mul_mem e.2 (od.K_le_E hk)) (E.inv_mem e.2)
  let KeE : Subgroup E := Ke.subgroupOf E
  let fQ : E →* alternatingGroup (Fin 7) := eQ.toMonoidHom.comp q
  let U7g : Subgroup (alternatingGroup (Fin 7)) :=
    U7.map (MulAut.conj g7).toMonoidHom
  have hKEmap : KE.map fQ = U7 := by
    dsimp [fQ, U7, Ubar]
    rw [Subgroup.map_map]
  have hKeEmap : KeE.map fQ = U7g := by
    ext y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨xE, hxE, rfl⟩
      have hxKe : (xE : G) ∈ Ke := Subgroup.mem_subgroupOf.mp hxE
      rcases Subgroup.mem_map.mp hxKe with ⟨k, hk, hkx⟩
      let kE : E := ⟨k, od.K_le_E hk⟩
      apply Subgroup.mem_map.mpr
      refine ⟨fQ kE, ?_, ?_⟩
      · rw [← hKEmap]
        exact Subgroup.mem_map.mpr ⟨kE, by simpa [KE, kE], rfl⟩
      · change g7 * fQ kE * g7⁻¹ = fQ xE
        calc
          g7 * fQ kE * g7⁻¹ =
              eQ (q e * q kE * (q e)⁻¹) := by
                simp [fQ, he7]
          _ = eQ (q (e * kE * e⁻¹)) := by simp
          _ = fQ xE := by
            apply congrArg eQ
            apply congrArg q
            apply Subtype.ext
            simpa [eg, kE, MulAut.conj_apply] using hkx
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, hyy⟩
      rw [← hKEmap] at hy0
      rcases Subgroup.mem_map.mp hy0 with ⟨kE, hkE, rfl⟩
      let xE : E := e * kE * e⁻¹
      apply Subgroup.mem_map.mpr
      refine ⟨xE, ?_, ?_⟩
      · apply Subgroup.mem_subgroupOf.mpr
        apply Subgroup.mem_map.mpr
        refine ⟨(kE : G), ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mp hkE
        · simp [xE, eg, MulAut.conj_apply]
      · rw [← hyy]
        change fQ xE = g7 * fQ kE * g7⁻¹
        simp [fQ, xE, he7]
  have hKeNe : Ke ≠ od.K := by
    intro hEq
    have hKeEEq : KeE = KE := by
      ext x
      change (x : G) ∈ Ke ↔ (x : G) ∈ od.K
      rw [hEq]
    apply hU7ne
    calc
      U7g = KeE.map fQ := hKeEmap.symm
      _ = KE.map fQ := by rw [hKeEEq]
      _ = U7 := hKEmap
  have hV7map : VE.map fQ = V7 := by
    dsimp [fQ, V7, Vbar]
    rw [Subgroup.map_map]
  have hKeNormV : Ke ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    have hxE : x ∈ E := hKeLeE hx
    let xE : E := ⟨x, hxE⟩
    have hfx : fQ xE ∈ U7g := by
      rw [← hKeEmap]
      exact Subgroup.mem_map.mpr
        ⟨xE, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hfxNorm : fQ xE ∈ Subgroup.normalizer (V7 : Set _) :=
      hU7norm hfx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      let vE : E := ⟨v, hVleE hv⟩
      have hfv : fQ vE ∈ V7 := by
        rw [← hV7map]
        exact Subgroup.mem_map.mpr
          ⟨vE, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
      have hconj7 : fQ xE * fQ vE * (fQ xE)⁻¹ ∈ V7 :=
        ((Subgroup.mem_normalizer_iff.mp hfxNorm) (fQ vE)).1 hfv
      rw [← hV7map] at hconj7
      rcases Subgroup.mem_map.mp hconj7 with ⟨v0, hv0, hqv0⟩
      let yE : E := xE * vE * xE⁻¹
      have hqy : q yE = q v0 := by
        apply eQ.injective
        change fQ yE = fQ v0
        simpa [fQ, yE, map_mul, map_inv] using hqv0.symm
      have hv2 : vE ^ 2 = 1 := by
        simpa [vE, pow_two] using congrArg Subtype.val
          (hVK.mul_self (⟨v, hv⟩ : V))
      have hy2 : yE ^ 2 = 1 := by
        calc
          yE ^ 2 = xE * (vE ^ 2) * xE⁻¹ := by simp [yE, pow_two, mul_assoc]
          _ = 1 := by rw [hv2]; simp
      have hv02 : (v0 : E) ^ 2 = 1 := by
        let v0VE : VE := ⟨v0, hv0⟩
        simpa [v0VE, pow_two] using
          congrArg Subtype.val (hVEK.mul_self v0VE)
      have hyEq : yE = v0 := sqOne_eq_of_q_eq hy2 hv02 hqy
      have hyV : (yE : G) ∈ V := by
        rw [hyEq]
        exact Subgroup.mem_subgroupOf.mp hv0
      simpa [xE, vE, yE, MulAut.conj_apply] using hyV
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hKeHhat : Ke ≤ c.Hhat := by
    rw [← firstCase_klein_normalizer_twoCore_eq_Hhat hmin c hkleinCore]
    simpa [V] using hKeNormV
  have hKeInv : ∀ x : G, x ∈ Ke →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    calc
      (od.s : G) * (eg * k * eg⁻¹) * (od.s : G)⁻¹ =
          eg * ((od.s : G) * k * (od.s : G)⁻¹) * eg⁻¹ := by
            have hComm' : (od.s : G) * (e : G) =
                (e : G) * (od.s : G) := heComm.symm
            have hinvComm : (e : G)⁻¹ * (od.s : G)⁻¹ =
                (od.s : G)⁻¹ * (e : G)⁻¹ := by
              simpa only [mul_inv_rev] using (congrArg Inv.inv heComm).symm
            dsimp [eg]
            calc
              (od.s : G) * ((e : G) * k * (e : G)⁻¹) * (od.s : G)⁻¹ =
                  ((od.s : G) * (e : G)) * k *
                    ((e : G)⁻¹ * (od.s : G)⁻¹) := by group
              _ = (((e : G) * (od.s : G)) * k) *
                    ((od.s : G)⁻¹ * (e : G)⁻¹) := by
                      rw [hComm', hinvComm]
              _ = (e : G) * ((od.s : G) * k * (od.s : G)⁻¹) *
                    (e : G)⁻¹ := by group
      _ = eg * k⁻¹ * eg⁻¹ := by rw [hsInvK k hk]
      _ = (eg * k * eg⁻¹)⁻¹ := by group
  exact ⟨e, Ke, rfl, heComm, heSqHhat, hKeNe,
    fun x hx => ⟨hKeHhat hx, hKeLeE hx⟩, hKeInv⟩

end CFSG.GorensteinWalter
