module

import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open CFSG.Assembly.LowTwoRank

theorem card_proj_statedSU {K : Type} [Field K] {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2) :
    Nat.card (StatedProj (StatedSU 3 r K)) =
      r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) / Nat.gcd 3 (r + 1) :=
  CFSG.Open.StatedAPI.card_statedProj_statedSU_three_of_prime hr hK

theorem card_dvd_of_model {X : Type} [Group X] {r : ℕ}
    (hX : StatedClassicalModel X .PSU 3 r 1) :
    Nat.card X ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := by
  obtain ⟨⟨hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK' : Nat.card K = r ^ 2 := by rw [hK, pow_one]
  rw [Nat.card_congr e.toEquiv]
  rw [show StatedSU 3 (r ^ 1) K = StatedSU 3 r K by rw [pow_one], card_proj_statedSU hr hK']
  have hg : Nat.gcd 3 (r + 1) ∣ r ^ 3 + 1 :=
    (Nat.gcd_dvd_right 3 (r + 1)).trans
      (by simpa using Odd.nat_add_dvd_pow_add_pow r 1 (by decide : Odd 3))
  exact Nat.div_dvd_of_dvd (Dvd.dvd.mul_left (Dvd.dvd.mul_left hg _) _)

end CFSG.Quasithin.H13.NQCore.U3O
