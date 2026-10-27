module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofG23

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup CFSG.RankThree.PartTwo.Census.Carrier.G2Three
open CFSG.RankThree.PartTwo.Sec4.Res417Five.G23

namespace G23

@[expose] def tLit : List (List ℕ) :=
  (List.range 14).map fun i => (List.range 14).map fun j =>
    if i = j then [1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1].getD i 0 else 0

theorem t_rows : mulR (mulR (mulR (mulR (mulR x1r x1r) y1r) x1r) y1r) (mulR x1r x1r) = tLit := by
  decide +kernel

theorem t_sq : mulR tLit tLit = oneR := by decide +kernel

theorem t_conj : mulR (mulR tLit x0r) tLit = mulR x0r x0r := by decide +kernel

theorem xb_cube : mulR (mulR x0r x0r) x0r = oneR := by decide +kernel

theorem comm_rows : mulR (mulR (mulR x0r x13Lit) (mulR x0r x0r)) (mulR x13Lit x13Lit) = uLit := by
  decide +kernel

theorem u_x0_rows : mulR uLit x0r = mulR x0r uLit := by decide +kernel

section Elements

@[expose] noncomputable def xb : H3 := ⟨gX 0, gX_mem 0⟩

theorem toM_xb : toM xb = decR x0r := coeR_gX0

theorem toM_tH : toM tH = decR tLit := by
  rw [← t_rows]
  exact coeR_mul (coeR_mul (coeR_mul (coeR_mul (coeR_sq coeR_gX1) coeR_gY1) coeR_gX1) coeR_gY1)
    (coeR_sq coeR_gX1)

theorem xb_pow_three : xb ^ 3 = 1 := pow_three_of_rows toM_xb xb_cube

theorem tH_sq : tH * tH = 1 :=
  toM_injective (by rw [toM_mul toM_tH toM_tH, t_sq, decR_oneR, map_one])

theorem tH_conj : tH * xb * tH⁻¹ = xb⁻¹ := by
  have hinv : tH⁻¹ = tH := inv_eq_of_mul_eq_one_right tH_sq
  have h1 : tH * xb * tH = xb * xb :=
    toM_injective (by rw [toM_mul (toM_mul toM_tH toM_xb) toM_tH, toM_mul toM_xb toM_xb, t_conj])
  rw [hinv, h1]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← pow_two, ← pow_succ, xb_pow_three]

theorem inv_eq_sq_of_cube {g : H3} (h : g ^ 3 = 1) : g⁻¹ = g * g :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← pow_succ', h])

theorem x13_pow_three : x13 ^ 3 = 1 := pow_three_of_rows toM_x13 cubes.2.2.1

theorem xu_pow_three : xu ^ 3 = 1 := pow_three_of_rows toM_xu cubes.2.1

theorem xb_x13_comm : xb * x13 * xb⁻¹ * x13⁻¹ = xu := by
  rw [inv_eq_sq_of_cube xb_pow_three, inv_eq_sq_of_cube x13_pow_three]
  exact toM_injective (by
    rw [toM_mul (toM_mul (toM_mul toM_xb toM_x13) (toM_mul toM_xb toM_xb))
      (toM_mul toM_x13 toM_x13), comm_rows, toM_xu])

theorem xu_comm_x13 : xu * x13 = x13 * xu :=
  mul_eq_mul_of_rows toM_xu toM_x13 toM_x13 toM_xu comms.2.1.symm

theorem xu_comm_xb : xu * xb = xb * xu :=
  mul_eq_mul_of_rows toM_xu toM_xb toM_xb toM_xu u_x0_rows

end Elements

end G23

theorem exists_noncentral_G23
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ center X) .G2 3 1) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, pow_one, ZMod.card]
  let ψ : X ⧸ center X ≃* H3 :=
    (e.trans (CFSG.TauCetiBridge.adjointQuotientCongr
      (FiniteField.ringEquivOfCardEq hcardK))).trans adjointQuotientEquivR3
  have hc : ψ.symm G23.xb * ψ.symm x13 * (ψ.symm G23.xb)⁻¹ * (ψ.symm x13)⁻¹ = ψ.symm xu := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, G23.xb_x13_comm]
  refine exists_noncentral_of_heis (center X) le_rfl (x := ψ.symm G23.xb) (t := ψ.symm x13)
    (y := ψ.symm tH) (by rw [← map_pow, G23.xb_pow_three, map_one])
    (by rw [← map_pow, G23.x13_pow_three, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, G23.tH_conj, map_inv]) ?_ ?_ ?_ ?_ S
  · rw [hc]
    intro h
    have h1 := orderOf_xu
    rw [show xu = 1 from ψ.symm.injective (by rw [h, map_one]), orderOf_one] at h1
    exact absurd h1 (by norm_num)
  · rw [hc, ← map_pow, G23.xu_pow_three, map_one]
  · rw [hc, ← map_mul, ← map_mul, G23.xu_comm_x13]
  · rw [hc, ← map_mul, ← map_mul, G23.xu_comm_xb]

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
