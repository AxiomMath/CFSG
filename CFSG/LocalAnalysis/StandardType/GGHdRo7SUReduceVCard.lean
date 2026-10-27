module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVIrrB

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUReduceVAux_card_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)) (hP3 : SUStabCardLeaf) (hN : SUNormalizerLeaf)
    (hD : SULinData 3 m V b H A) :
    Nat.card H ≤ 2 * 3 ^ m * (m + 1).factorial := by
  have hm7 : 7 ≤ m := hD.hm
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fintype V := Fintype.ofEquiv (Fin m → ZMod 3) b.equivFun.toEquiv.symm
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Fintype (V ≃ₗ[ZMod 3] V) := Fintype.ofFinite _
  haveI : Fintype H := Fintype.ofFinite H
  let x : V := SUOnes 3 b
  haveI : Fintype ↥(MulAction.orbit H x) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer H x) := Fintype.ofFinite _
  have hVcard : Fintype.card V = 3 ^ m := by
    rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hOS : Fintype.card (MulAction.orbit H x) * Fintype.card (MulAction.stabilizer H x) =
      Fintype.card H := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H x
  have horbit : Fintype.card (MulAction.orbit H x) ≤ 3 ^ m := by
    rw [← hVcard]
    exact Fintype.card_le_of_injective (fun v : ↥(MulAction.orbit H x) => v.1)
      Subtype.val_injective
  have hP3' : Nat.card {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a x = x} ≤ 2 * m.factorial :=
    hP3 hN 3 m V b H A hD
  let e : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a x = x} ≃ ↥(MulAction.stabilizer H x) :=
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      invFun := fun q => ⟨q.1.1, q.1.2, by
        have hq := q.2
        change q.1.1 x = x at hq
        exact hq⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hstab : Fintype.card (MulAction.stabilizer H x) ≤ 2 * m.factorial := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
    exact hP3'
  calc Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    _ = Fintype.card (MulAction.orbit H x) * Fintype.card (MulAction.stabilizer H x) :=
        hOS.symm
    _ ≤ 3 ^ m * (2 * m.factorial) := Nat.mul_le_mul horbit hstab
    _ = 2 * 3 ^ m * m.factorial := by ring
    _ ≤ 2 * 3 ^ m * (m + 1).factorial :=
        Nat.mul_le_mul_left _ (Nat.factorial_le (Nat.le_succ m))

end CFSG.StandardType.HdRo7SU
