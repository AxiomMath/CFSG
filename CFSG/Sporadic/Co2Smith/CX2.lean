module

public import CFSG.Sporadic.Co2Smith.CCFacts

public section

namespace CFSG.Sporadic.Co2Smith

open Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev DC :
    Subgroup Cz := DCi 7

theorem natCard_DCi
    (hc : CCFacts) {i : ℕ} (hi : i < 9) : Nat.card (DCi i) = Native.ccCE[i]! := by
  have e : Nat.card (DCi i) = ceInv (cR i) := by
    unfold ceInv
    exact Nat.card_congr
      { toFun := fun d => ⟨⟨d.1, d.2.2⟩, (Subgroup.mem_centralizer_singleton_iff.mp d.2.1)⟩
        invFun := fun q => ⟨q.1.1, Subgroup.mem_centralizer_singleton_iff.mpr q.2, q.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e]
  exact hc.ce ⟨i, hi⟩

section

theorem DC_comm (hc : CCFacts) : ∀ a ∈ DC, ∀ b ∈ DC, a * b = b * a := hc.c2B_comm

theorem card_CXD (hc : CCFacts) :
    Nat.card (Subgroup.centralizer (DC : Set Cz) ⊓ XC 7 : Subgroup Cz) ≤ Nat.card DC ^ 2 :=
  hc.c2B_cxd

theorem card_ZD (hc : CCFacts) :
    Nat.card {d : Cz // d ∈ DC ∧ ∀ x ∈ XC 7, x * d = d * x} ≤ 2 := hc.c2B_zd

theorem card_ZA (hc : CCFacts) :
    8 ≤ Nat.card {a : Cz // a ∈ Subgroup.centralizer (DC : Set Cz) ⊓ XC 7 ∧
      ∀ x ∈ XC 7, x * a = a * x} := hc.c2B_za

theorem hmin_C (hc : CCFacts) :
    ∀ N : Subgroup Cz, N ≤ DC → (∀ x ∈ XC 7, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      N ≠ ⊥ → zCz ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : Cz, h * (cR 7 * d) * h⁻¹ = cR 7 :=
  hc.c2B_hmin

end

end CFSG.Sporadic.Co2Smith
