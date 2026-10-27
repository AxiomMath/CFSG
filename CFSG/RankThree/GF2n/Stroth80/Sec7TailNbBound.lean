module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAbelianBound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

theorem abelian_card_le_of_semiextraspecial {X : Type*} [Group X] [Finite X]
    (V Nb : Subgroup X) (q : ℕ)
    (hV : V ≤ Nb) (hVc : ∀ v ∈ V, ∀ n ∈ Nb, v * n = n * v)
    (hcomm : ∀ a ∈ Nb, ∀ b ∈ Nb, ⁅a, b⁆ ∈ V) (hV2 : ∀ v ∈ V, v * v = 1)
    (hZ : ∀ z ∈ Nb, (∀ n ∈ Nb, z * n = n * z) → z ∈ V)
    (hsemi : ∀ z ∈ Nb, z ∉ V → ∀ w ∈ V, ∃ m ∈ Nb, m * z * m⁻¹ = w * z)
    (hVcard : Nat.card V = q) (hNbcard : Nat.card Nb = q ^ 9) :
    ∀ A : Subgroup X, A ≤ Nb → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 5 := by
  intro A hAN hA
  have hcoe : ∀ x y : Nb, ((⁅x, y⁆ : Nb) : X) = ⁅(x : X), (y : X)⁆ := fun x y => by
    simp [commutatorElement_def]
  have hVcen : ∀ v ∈ V.subgroupOf Nb, ∀ n : Nb, v * n = n * v := by
    intro v hv n
    exact Subtype.ext (hVc (v : X) (Subgroup.mem_subgroupOf.mp hv) (n : X) n.2)
  have hcomm' : ∀ x y : Nb, ⁅x, y⁆ ∈ V.subgroupOf Nb := by
    intro x y
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hcomm x.1 x.2 y.1 y.2
  have hV2' : ∀ v ∈ V.subgroupOf Nb, v ^ 2 = 1 := by
    intro v hv
    apply Subtype.ext
    rw [pow_two]
    exact hV2 (v : X) (Subgroup.mem_subgroupOf.mp hv)
  have hZ' : ∀ x : Nb, (∀ n : Nb, x * n = n * x) → x ∈ V.subgroupOf Nb := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hZ x.1 x.2
    intro n hn
    exact congrArg Subtype.val (hx ⟨n, hn⟩)
  have hsemi' : ∀ x : Nb, x ∉ V.subgroupOf Nb →
      ∀ v ∈ V.subgroupOf Nb, ∃ n : Nb, ⁅x, n⁆ = v := by
    intro x hx v hv
    obtain ⟨m, hm, hmeq⟩ := hsemi x.1 x.2 (fun h => hx (Subgroup.mem_subgroupOf.mpr h))
      (v : X) (Subgroup.mem_subgroupOf.mp hv)
    have h1 : ⁅m, (x : X)⁆ = (v : X) := by
      rw [commutatorElement_def, hmeq, mul_inv_cancel_right]
    have hvinv : (v : X)⁻¹ = (v : X) :=
      inv_eq_of_mul_eq_one_right (hV2 (v : X) (Subgroup.mem_subgroupOf.mp hv))
    have h2 : ⁅(x : X), m⁆ = (v : X) := by
      rw [← commutatorElement_inv, h1, hvinv]
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hcoe]
    exact h2
  have hA' : ∀ a ∈ A.subgroupOf Nb, ∀ b ∈ A.subgroupOf Nb, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hA (a : X) (Subgroup.mem_subgroupOf.mp ha) (b : X)
      (Subgroup.mem_subgroupOf.mp hb))
  have key := card_sq_le_of_abelian_in_semiextraspecial (V.subgroupOf Nb) hVcen hcomm' hV2'
    hZ' hsemi' (A.subgroupOf Nb) hA'
  have hAcard : Nat.card (A.subgroupOf Nb) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hVcard' : Nat.card (V.subgroupOf Nb) = q :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv).trans hVcard
  rw [hAcard, hVcard', hNbcard] at key
  have h10 : q ^ 9 * q = (q ^ 5) ^ 2 := by ring
  rw [h10] at key
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp key

end CFSG.RankThree.GF2n.Stroth80
