module

public import CFSG.Sporadic.Co2Smith.CX2

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

abbrev D1 :
    Subgroup Cz := DCi 1

section


theorem cz_invE (hc : CCFacts) (i : Fin 9) : invEInv (cR i) = Native.ccInvE[(i : ℕ)]! :=
  hc.invE i

theorem D1_comm (hc : CCFacts) : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a := hc.c1_comm

theorem c1_hmin (hc : CCFacts) :
    ∀ N : Subgroup Cz, N ≤ D1 → (∀ x ∈ XC 1, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N ≠ ⊥ → zCz ∈ N :=
  hc.c1_hmin

theorem c1_cxd_card (hc : CCFacts) :
    Nat.card (centralizer (D1 : Set Cz) ⊓ XC 1 : Subgroup Cz) ≤ 1024 := hc.c1_cxd_card

theorem c1_cxd_sq (hc : CCFacts) : ∀ y ∈ centralizer (D1 : Set Cz) ⊓ XC 1, y * y = 1 :=
  hc.c1_cxd_sq

theorem c1_j (hc : CCFacts) : ∃ j ∈ centralizer (D1 : Set Cz) ⊓ XC 1, invEInv j = 80 := hc.c1_j

theorem c1_two (hc : CCFacts) : ∃ h : Cz, h * (cR 2 * zCz) * h⁻¹ = cR 1 := hc.c1_two

theorem natCard_D1 (hc : CCFacts) : Nat.card D1 = 32 := natCard_DCi hc (i := 1) (by norm_num)

end

end CFSG.Sporadic.Co2Smith
