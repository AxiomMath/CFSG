module

public import Certificates.Kernel.Co1B.C27207
public import Certificates.Kernel.Co1B.Chk27208

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Cent27207

open CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.EvenSporadicStandard.Co1Cent CFSG.EvenSporadicStandard.Co1Pair
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin

@[expose] noncomputable def gK (x : Nat) : Nat := getL 0 K.CX x

theorem kc : (allN 64 fun x => eqK (gK x) (mxK K.ATK K.CP K.WC x)) = true ∧
    (gdX.all fun x => Nat.beq (mulK (gK x) (invK (gK x))) oneK) = true ∧
    (gdX.all fun x => eqK (mulWK (gK x) (gK x)) oneK || eqK (mulWK (mulWK (gK x) (gK x)) (gK x)) oneK) = true ∧
    (gdX.all fun x => gdX.all fun y =>
      !(eqK (mulWK (gK x) (gK x)) oneK && eqK (mulWK (gK y) (gK y)) oneK) ||
        eqK (mulWK (gK x) (gK y)) (mulWK (gK y) (gK x))) = true ∧
    decide ((gdX.filter fun x => eqK (mulWK (gK x) (gK x)) oneK).length ≤ 4) = true ∧
    (gdX.all fun x => gdX.all fun y =>
      eqK (mulWK (mulWK (mulWK (mulWK (gK x) (gK y)) (invK (gK x))) (invK (gK y)))
        (mulWK (mulWK (mulWK (gK x) (gK y)) (invK (gK x))) (invK (gK y)))) oneK) = true ∧
    ((List.range 64).all fun x => gdX.contains x ||
      singRecs.any (fun r => r.1 == x && singK (gK x) r.2) ||
      exclRecs.any (fun r => r.1 == x && exclK K.X K.A1 twoBTris (gK x) r.2.1 r.2.2)) = true := by
  have h := kClass
  unfold classK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem A_eq : centData.A = K.AK.map (unpackR 24) :=
  A_unpack rfl sRows_eq sInv_eq (spinK_ATK kSpin).1

theorem cx_eq {x : Nat} (hx : x < 64) : cx x = unpackR 24 (gK x) := by
  have hl : K.AK.length = 24 := by
    rw [(spinK_ATK kSpin).1, List.length_map, (spinK_ATK kSpin).2.2]
  have h := mx_unpack rfl hC hW A_eq (spinK_ATK kSpin).2.1 hl x
  rw [cx, h]
  exact (beq_of_eqK (allN_true' kc.1 x hx)).symm

theorem gd_lt : ∀ x ∈ gdX, x < 64 := by decide

theorem gdRows_eq : gdRows = gdX.map fun x => unpackR 24 (gK x) := by
  rw [gdRows]
  exact List.map_congr_left fun x hx => cx_eq (gd_lt x hx)

theorem inv_eq {x : Nat} (hx : x ∈ gdX) : inv (unpackR 24 (gK x)) = unpackR 24 (invK (gK x)) :=
  inv_unpackR (Nat.eq_of_beq_eq_true (List.all_eq_true.1 kc.2.1 x hx))

theorem validR_unpack (P : Nat) : validR 24 (unpackR 24 P) = true := by
  unfold validR
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp [unpackR, Nat.mod_lt]

theorem aR_eq' : aR = unpackR 24 K.A1 := by
  rw [CertificateChecks.KernelSporSch.Co1Packed.aR_u, CFSG.KC.Co1T.unpack_eq_unpackR]
  rfl

theorem orB_eq' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem act_eq (M v : Nat) : act (unpackR 24 M) v = vmF 24 (trK 24 M) v := act_unpackR rfl v

theorem tri_eq (T : Nat) : triTrivial (unpackR 24 T) = triK T twoBTris := by
  unfold triTrivial triK
  refine congrArg (List.all twoBTris) (funext fun p => ?_)
  rw [strictB_eq', vecMulN_unpackR, orB_eq', orB_eq']
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq, or_assoc]
  exact Iff.rfl

theorem singOK_eq {x : Nat} (hx : x < 64) (u : Nat) : singOK x u = singK (gK x) u := by
  unfold singOK singK
  rw [cx_eq hx, act_eq]

theorem exclOK_eq {x : Nat} (hx : x < 64) (e u : Nat) :
    exclOK x e u = exclK K.X K.A1 twoBTris (gK x) e u := by
  unfold exclOK exclK
  dsimp only
  rw [cx_eq hx, pow_unpack', aR_eq', cpX_eq, mul_unpackW, mul_unpackW, beq_unpack,
    transposeRows_unpackR, tri_eq]
  simp only [act_eq]
  rfl

theorem mul_eq (A B : Nat) : mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) := mul_unpackW A B

open Certificates in
open CFSG.EvenSporadicStandard.Co1Cent in
theorem c27208 : classOK = true := by
  obtain ⟨-, k2, k3, k4, k5, k6, k7⟩ := kc
  unfold classOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [gdRows_eq, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply]
    rw [inv_eq hx, validR_unpack, validR_unpack]
    rfl
  · rw [gdRows_eq, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply]
    rw [inv_eq hx, mul_unpack, Nat.eq_of_beq_eq_true (List.all_eq_true.1 k2 x hx), one_eq]
    exact beq_self_eq_true _
  · rw [gdRows_eq, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply]
    rw [mul_eq, mul_eq, one_eq, beq_unpack, beq_unpack]
    exact List.all_eq_true.1 k3 x hx
  · rw [gdRows_eq, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply, List.all_map, List.all_eq_true]
    intro y hy
    rw [mul_eq, mul_eq, mul_eq, mul_eq, one_eq, beq_unpack, beq_unpack, beq_unpack]
    exact List.all_eq_true.1 (List.all_eq_true.1 k4 x hx) y hy
  · rw [gdRows_eq, List.filter_map, List.length_map]
    have e : List.filter ((fun G => mul G G == one) ∘ fun x => unpackR 24 (gK x)) gdX =
        List.filter (fun x => eqK (mulWK (gK x) (gK x)) oneK) gdX := by
      refine List.filter_congr fun x _ => ?_
      rw [Function.comp_apply, mul_eq, one_eq, beq_unpack]
    rw [e]
    exact k5
  · rw [gdRows_eq, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply, List.all_map, List.all_eq_true]
    intro y hy
    rw [inv_eq hx, inv_eq hy, mul_eq, mul_eq, mul_eq, mul_eq, one_eq, beq_unpack]
    exact List.all_eq_true.1 (List.all_eq_true.1 k6 x hx) y hy
  · rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    simp only [singOK_eq hx', exclOK_eq hx']
    exact List.all_eq_true.1 k7 x hx

end CertificateChecks.KernelCo1B.Cent27207

end
