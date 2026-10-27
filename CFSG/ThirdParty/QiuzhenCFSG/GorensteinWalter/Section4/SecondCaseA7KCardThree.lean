module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UEQuotientCardThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedElementsInComponent
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The inverted subgroup has order three in the A7 branch

The quotient image of `U ∩ E` has order three.  The fixed/inverted
decomposition therefore has a nontrivial inverted factor, and its map into
`E / Z(E)` is injective because the center is fixed by the reflecting
involution and `U` has odd order.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The subgroup `K = I_{U∩M}(s)` supplied by equations (1)--(2) has order
three in the `A₇` component branch. -/
public theorem secondCase_a7_involution_K_card_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      Nat.card K = 3 := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc,
      hq_s_not_T, hTinv, hTcontain, hUEbar_le_T, hUEbar_cyclic,
      hUEbar_inv, K, B, hK_eq, hK_cyc, hB_def, hjoinX⟩ :=
    secondCase_involution_decomposition c w d
  let E : Subgroup G := d.E
  let Z : Subgroup E := Subgroup.center E
  letI : Z.Normal := by
    dsimp [Z]
    infer_instance
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let UE : Subgroup E := (c.U ⊓ E).subgroupOf E
  let UEbar : Subgroup (E ⧸ Z) := UE.map q
  have hUEbar_card : Nat.card UEbar = 3 := by
    simpa [E, Z, q, UE, UEbar] using
      (secondCase_a7_U_inter_E_quotient_card_eq_three
        hmin c w d hA7 hmodel)
  have hKleE : K ≤ E := by
    intro y hy
    have hy' : y ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hK_eq]
      exact hy
    exact secondCase_invertedElements_le_component c w d SM hSMcent SE
      hSEamb hsSE hy'.1.1 hy'.1.2 hy'.2
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hBeq : B = c.U ⊓ w.M := by
      have h := hjoinX
      rw [hKbot, bot_sup_eq] at h
      exact h
    have hUEbarbot : UEbar = ⊥ := by
      apply le_antisymm
      · intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨x, hxUE, hqx⟩
        have hxUE' : (x : G) ∈ c.U ⊓ E :=
          Subgroup.mem_subgroupOf.mp hxUE
        have hxX : (x : G) ∈ c.U ⊓ w.M :=
          ⟨hxUE'.1, d.E_component.1 hxUE'.2⟩
        have hxB : (x : G) ∈ B := by rw [hBeq]; exact hxX
        have hxCent : (x : G) ∈
            Subgroup.centralizer ({(s : G)} : Set G) := by
          rw [hB_def, centralizerIn] at hxB
          exact hxB.2
        have hxfix : (s : G) * (x : G) * (s : G)⁻¹ = (x : G) := by
          have hcomm : (s : G) * (x : G) = (x : G) * (s : G) :=
            Subgroup.mem_centralizer_iff.mp hxCent (s : G) (by simp)
          rw [hcomm]
          group
        have hqfix : q s * z * (q s)⁻¹ = z := by
          calc
            q s * z * (q s)⁻¹ = q s * q x * (q s)⁻¹ := by rw [hqx]
            _ = q (s * x * s⁻¹) := by simp [map_mul, map_inv]
            _ = q x := by rw [show s * x * s⁻¹ = x from Subtype.ext hxfix]
            _ = z := hqx
        have hqinv : q s * z * (q s)⁻¹ = z⁻¹ := by
          exact hUEbar_inv z hz
        have hzinv : z = z⁻¹ := hqfix.symm.trans hqinv
        have hzsq : z ^ 2 = 1 := by
          calc
            z ^ 2 = z * z := pow_two z
            _ = z⁻¹ * z := congrArg (fun a => a * z) hzinv
            _ = 1 := by simp
        have hord2 : orderOf z ∣ 2 :=
          (orderOf_dvd_iff_pow_eq_one (x := z) (n := 2)).mpr hzsq
        have hord3 : orderOf z ∣ 3 := by
          have h := Subgroup.orderOf_dvd_natCard UEbar hz
          rwa [hUEbar_card] at h
        have hord1 : orderOf z = 1 := by
          have hdvd : orderOf z ∣ Nat.gcd 2 3 := Nat.dvd_gcd hord2 hord3
          rw [show Nat.gcd 2 3 = 1 by norm_num] at hdvd
          exact Nat.dvd_one.mp hdvd
        exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord1)
      · exact bot_le
    have hcardbot : Nat.card UEbar = 1 := by rw [hUEbarbot]; simp
    omega
  let KE : Subgroup E := K.subgroupOf E
  have hKEleUE : KE ≤ UE := by
    intro x hx
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    have hxInv : (x : G) ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hK_eq]
      exact hxK
    exact Subgroup.mem_subgroupOf.mpr ⟨hxInv.1.1, hKleE hxK⟩
  have hKEinfZ : KE ⊓ Z = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx.1
    have hxInv : (x : G) ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hK_eq]
      exact hxK
    have hxfix : (s : G) * (x : G) * (s : G)⁻¹ = (x : G) := by
      have hcommE := Subgroup.mem_center_iff.mp hx.2 s
      have hcomm : (s : G) * (x : G) = (x : G) * (s : G) :=
        congrArg Subtype.val hcommE
      rw [hcomm]
      group
    have hxeq : (x : G) = (x : G)⁻¹ := hxfix.symm.trans hxInv.2
    have hx2 : (x : G) ^ 2 = 1 := by
      calc
        (x : G) ^ 2 = (x : G) * (x : G) := pow_two (x : G)
        _ = (x : G)⁻¹ * (x : G) := congrArg (fun a => a * (x : G)) hxeq
        _ = 1 := by simp
    let xU : c.U := ⟨(x : G), hxInv.1.1⟩
    have hx2U : xU ^ 2 = 1 := Subtype.ext hx2
    have hord2 : orderOf xU ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := xU) (n := 2)).mpr hx2U
    have hordU : orderOf xU ∣ Nat.card c.U := orderOf_dvd_natCard xU
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    have hord1 : orderOf xU = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h1 | h2
      · exact h1
      · exfalso
        apply hUodd.not_two_dvd_nat
        rw [← h2]
        exact hordU
    have hxUone : xU = 1 := orderOf_eq_one_iff.mp hord1
    have hxGone : (x : G) = 1 :=
      congrArg (fun y : c.U => (y : G)) hxUone
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact hxGone
  have hmapcard : Nat.card (KE.map q) = Nat.card K := by
    have hformula := card_map_eq_card_mul_card_ker q KE
    have hker : q.ker = Z := by simp [q]
    rw [hker, hKEinfZ, Subgroup.card_bot, mul_one] at hformula
    have hKEcard : Nat.card KE = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleE).toEquiv
    exact hformula.symm.trans hKEcard
  have hmaple : KE.map q ≤ UEbar := Subgroup.map_mono hKEleUE
  have hmapdvd : Nat.card (KE.map q) ∣ Nat.card UEbar :=
    Subgroup.card_dvd_of_le hmaple
  have hKdvd : Nat.card K ∣ 3 := by
    rw [← hmapcard, ← hUEbar_card]
    exact hmapdvd
  have hKcard : Nat.card K = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hKdvd with h1 | h3
    · exact False.elim (hKne ((Subgroup.eq_bot_iff_card (H := K)).mpr h1))
    · exact h3
  exact ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hKcard⟩

end CFSG.GorensteinWalter
