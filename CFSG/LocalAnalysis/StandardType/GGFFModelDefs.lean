module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

def wt (v : Fin 3 → ZMod 3) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

structure Model (H : Type) [Group H] (z : Fin 3 → H) : Prop where
  simple : IsSimpleGroup H
  pow_z : ∀ i, z i ^ 3 = 1
  comm_z : ∀ i j, z i * z j = z j * z i
  inj : ∀ v, vecElt z v = 1 → v = 0
  inner_odd : ∀ α : MulAut H, ∀ m : ℕ, Odd m → α ^ m = 1 → ∃ h : H, α = MulAut.conj h
  rank : ∀ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 27
  torus : ∀ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    ∃ g : H, ∀ x : H, x ∈ E ↔ ∃ v, x = g * vecElt z v * g⁻¹
  fus : ∀ x : H, x ^ 3 = 1 → ∃ g : H, ∃ v, x = g * vecElt z v * g⁻¹
  conj_iff : ∀ v w, v ≠ 0 → w ≠ 0 → (IsConj (vecElt z v) (vecElt z w) ↔ wt v = wt w)
  mono : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
    ∃ h : H, ∀ i, h * z i * h⁻¹ = z (σ i) ^ (ε i).val
  no_five : ∀ x : H, x ^ 5 = 1 → x * z 0 = z 0 * x → x * z 1 = z 1 * x → x = 1
  five : ∃ x : H, x ≠ 1 ∧ x ^ 5 = 1 ∧ x * z 0 = z 0 * x ∧ x * (z 1 * z 2) = z 1 * z 2 * x

end CFSG.StandardType.GGFF

end
