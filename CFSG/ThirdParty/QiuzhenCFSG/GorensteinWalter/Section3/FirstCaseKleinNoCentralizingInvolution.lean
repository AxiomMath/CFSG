module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinTwoCoreNoCentralize
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinVUInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralThreeNoOrderSix
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# No involution of `Ĥ` centralizes the inverted order-three subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Under the hypotheses of restriction (7), no involution in `Ĥ`
centralizes the inverted subgroup `X` of order three.  Involutions in `VU`
reduce to the two-core exclusion; outside `VU`, a commuting order-two and
order-three pair would give an element of order six in `Ĥ/VU ≃ D₆`. -/
public theorem firstCase_klein_no_centralizing_involution_of_inverted_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hXcard : Nat.card X = 3)
    {s : G} (hsH : s ∈ c.Hhat) (hsI : IsInvolution s) :
    ¬ (∀ x : G, x ∈ X → s * x * s⁻¹ = x) := by
  classical
  intro hsCent
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  by_cases hsB : s ∈ B
  · have hsV : s ∈ twoCoreOf c.Hhat :=
      firstCase_klein_involution_mem_twoCore_of_mem_VU
        hmin c hklein hsB hsI
    exact firstCase_klein_twoCore_not_centralize_inverted_subgroup
      hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv
      hsV hsI.1 hsCent
  · have hXinf : X ⊓ B = ⊥ := by
      simpa [B] using
        firstCase_klein_inverted_subgroup_inf_VU_eq_bot
          hmin c hfirst hklein hy hyH hXle hXinv
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨xX, hxXorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard])
    let x : G := xX
    have hxH : x ∈ c.Hhat := hXle xX.2
    have hxorder : orderOf x = 3 := by
      simpa [x] using (Subgroup.orderOf_coe xX).trans hxXorder
    have hxne : x ≠ 1 := by
      intro hx1
      rw [hx1, orderOf_one] at hxorder
      omega
    have hxB : x ∉ B := by
      intro hxB
      have hxbot : x ∈ X ⊓ B := ⟨xX.2, hxB⟩
      rw [hXinf] at hxbot
      exact hxne (Subgroup.mem_bot.mp hxbot)
    let H : Subgroup G := c.Hhat
    let N0 : Subgroup H := pCore 2 H ⊔ pPrimeCore 2 H
    have hN0normal : N0.Normal := by
      dsimp [N0, H]
      infer_instance
    let : N0.Normal := hN0normal
    let q : H →* (H ⧸ N0) := QuotientGroup.mk' N0
    have hmapN : N0.map H.subtype = B := by
      have hUeq : c.U = oddCoreOf c.Hhat := (theorem_2_6 hmin c).1
      dsimp [N0, H, B]
      rw [Subgroup.map_sup]
      simp [twoCoreOf, oddCoreOf, hUeq]
    let sH : H := ⟨s, hsH⟩
    let xH : H := ⟨x, hxH⟩
    let qs : H ⧸ N0 := q sH
    let qx : H ⧸ N0 := q xH
    have hqsne : qs ≠ 1 := by
      intro hqs
      have hsN : sH ∈ N0 := (QuotientGroup.eq_one_iff sH).mp hqs
      have hsmap : s ∈ N0.map H.subtype :=
        Subgroup.mem_map.mpr ⟨sH, hsN, rfl⟩
      rw [hmapN] at hsmap
      exact hsB hsmap
    have hqxne : qx ≠ 1 := by
      intro hqx
      have hxN : xH ∈ N0 := (QuotientGroup.eq_one_iff xH).mp hqx
      have hxmap : x ∈ N0.map H.subtype :=
        Subgroup.mem_map.mpr ⟨xH, hxN, rfl⟩
      rw [hmapN] at hxmap
      exact hxB hxmap
    have hqs2 : qs ^ 2 = 1 := by
      change q (sH ^ 2) = 1
      have hs2 : s ^ 2 = 1 := hsI.2
      have hsH2 : sH ^ 2 = 1 := by
        apply Subtype.ext
        exact hs2
      rw [hsH2]
      simp
    have hqx3 : qx ^ 3 = 1 := by
      change q (xH ^ 3) = 1
      have hx3 : x ^ 3 = 1 := by
        rw [← hxorder]
        exact pow_orderOf_eq_one x
      have hxH3 : xH ^ 3 = 1 := by
        apply Subtype.ext
        exact hx3
      rw [hxH3]
      simp
    have hqsord : orderOf qs = 2 := by
      have hdvd : orderOf qs ∣ 2 := orderOf_dvd_of_pow_eq_one hqs2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact False.elim (hqsne (orderOf_eq_one_iff.mp h1))
      · exact h2
    have hqxord : orderOf qx = 3 := by
      have hdvd : orderOf qx ∣ 3 := orderOf_dvd_of_pow_eq_one hqx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact False.elim (hqxne (orderOf_eq_one_iff.mp h1))
      · exact h3
    have hsx : s * x = x * s := by
      have h := hsCent x xX.2
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using h)
    have hsxH : sH * xH = xH * sH := by
      apply Subtype.ext
      exact hsx
    have hcomm : Commute qs qx := by
      rw [Commute]
      exact congrArg q hsxH
    have hqprod : orderOf (qs * qx) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime]
      · rw [hqsord, hqxord]
      · rw [hqsord, hqxord]
        norm_num
    obtain ⟨e⟩ := firstCase_klein_quotient_d6 hmin c hfirst hklein
    let e0 : (H ⧸ N0) ≃* DihedralGroup 3 := by
      simpa [H, N0] using e
    exact dihedralGroup_three_orderOf_ne_six (e0 (qs * qx)) (by
      rw [MulEquiv.orderOf_eq]
      exact hqprod)

end CFSG.GorensteinWalter
