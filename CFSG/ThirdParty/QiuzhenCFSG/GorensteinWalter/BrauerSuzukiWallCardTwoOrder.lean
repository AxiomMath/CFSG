module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoNormalizerInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoOutsideInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-sixty endpoint in the order-two branch

When `N_G(H)` is proper, it contains the three nonidentity elements of the
Klein four subgroup `H` as its involutions, while twelve involutions lie
outside it.  Thus the global involution conjugacy class has cardinality
fifteen.  Since its centralizer is `H` of order four, the group has order
sixty.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In the proper `|K| = 2` branch, the ambient group has order sixty. -/
public theorem
    BrauerSuzukiWallHypotheses.card_eq_sixty_of_card_K_eq_two_of_normalizer_ne_top
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    Nat.card G = 60 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let AllInv := {v : G // IsInvolution v}
  let InN := {v : G // IsInvolution v ∧ v ∈ N}
  let OutInv := {v : G // IsInvolution v ∧ v ∉ N}
  let PunctH := {x : h.H // x ≠ 1}
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  let : IsKleinFour h.H := h.isKleinFour_H_of_card_K_eq_two hk
  have hHcard : Nat.card h.H = 4 :=
    (h.isKleinFour_H_of_card_K_eq_two hk).card_four
  let eIn : InN ≃ PunctH := by
    let toFun : InN → PunctH := fun v =>
      ⟨⟨(v : G),
        h.involution_mem_H_of_mem_normalizer_of_card_K_eq_two
          hk v.property.2 v.property.1⟩,
        by
          intro hvOne
          apply v.property.1.1
          exact congrArg Subtype.val hvOne⟩
    let invFun : PunctH → InN := fun x =>
      ⟨(x.1 : G),
        ⟨by
          constructor
          · intro hxOne
            apply x.property
            apply Subtype.ext
            exact hxOne
          · have hxSqH := IsKleinFour.mul_self x.1
            simpa [pow_two] using congrArg Subtype.val hxSqH,
          hHleN x.1.property⟩⟩
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro v
          apply Subtype.ext
          rfl
        right_inv := by
          intro x
          apply Subtype.ext
          rfl }
  have hPunctCard : Nat.card PunctH = 3 := by
    have hpunct : Nat.card PunctH = Nat.card h.H - 1 := by
      let : Fintype h.H := Fintype.ofFinite h.H
      let : Fintype PunctH := Fintype.ofFinite PunctH
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      simp [PunctH]
    rw [hpunct, hHcard]
  have hInNCard : Nat.card InN = 3 := by
    calc
      Nat.card InN = Nat.card PunctH := Nat.card_congr eIn
      _ = 3 := hPunctCard
  have hOutCard : Nat.card OutInv = 12 := by
    simpa [OutInv, N] using
      h.outside_involutions_card_eq_twelve_of_card_K_eq_two hk hNne
  let eSplit : AllInv ≃ InN ⊕ OutInv := by
    let toFun : AllInv → InN ⊕ OutInv := fun v =>
      if hvN : (v : G) ∈ N then
        Sum.inl ⟨(v : G), v.property, hvN⟩
      else
        Sum.inr ⟨(v : G), v.property, hvN⟩
    let invFun : InN ⊕ OutInv → AllInv
      | Sum.inl v => ⟨(v : G), v.property.1⟩
      | Sum.inr v => ⟨(v : G), v.property.1⟩
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro v
          by_cases hvN : (v : G) ∈ N
          · simp [toFun, invFun, hvN]
          · simp [toFun, invFun, hvN]
        right_inv := by
          intro v
          cases v with
          | inl v =>
              dsimp [toFun, invFun]
              rw [dif_pos v.property.2]
          | inr v =>
              dsimp [toFun, invFun]
              rw [dif_neg v.property.2] }
  have hAllCard : Nat.card AllInv = 15 := by
    calc
      Nat.card AllInv = Nat.card (InN ⊕ OutInv) := Nat.card_congr eSplit
      _ = Nat.card InN + Nat.card OutInv := Nat.card_sum
      _ = 15 := by rw [hInNCard, hOutCard]
  have hAllSet :
      ({x : G | IsInvolution x} : Set G) =
        MulAction.orbit (ConjAct G) h.t := by
    ext x
    constructor
    · intro hx
      rw [ConjAct.mem_orbit_conjAct, isConj_iff]
      rcases h.involutions_conjugate x hx with ⟨g, hg⟩
      exact ⟨g, hg⟩
    · intro hx
      rw [ConjAct.mem_orbit_conjAct, isConj_iff] at hx
      rcases hx with ⟨g, hg⟩
      constructor
      · intro hone
        apply h.t_involution.1
        rw [← hg]
        simp [hone]
      · calc
          x ^ 2 = g⁻¹ * (h.t ^ 2) * g := by
            have hc := congrArg (fun z : G => g⁻¹ * z * g) hg
            have hx' : x = g⁻¹ * h.t * g := by
              simpa [mul_assoc] using hc
            rw [hx', pow_two, pow_two]
            group
          _ = 1 := by rw [h.t_involution.2]; simp
  let : Fintype G := Fintype.ofFinite G
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (ConjAct G) h.t
  have horbit' :
      Nat.card ↑(MulAction.orbit (ConjAct G) h.t) *
          Nat.card (MulAction.stabilizer (ConjAct G) h.t) = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using horbit
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) h.t) =
      Nat.card h.H := by
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer h.t,
      ← h.H_eq_centralizer]
  have hmul : Nat.card AllInv * Nat.card h.H = Nat.card G := by
    change Nat.card ↑({x : G | IsInvolution x} : Set G) *
      Nat.card h.H = Nat.card G
    rw [hAllSet, ← hstab]
    exact horbit'
  rw [hAllCard, hHcard] at hmul
  omega

end CFSG.GorensteinWalter
