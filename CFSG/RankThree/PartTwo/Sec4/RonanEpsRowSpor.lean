module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem rowSEpsOf_of_card {X Y : Type} [Group X] [Group Y] {N B : ℕ}
    (hY : Nonempty (Y ≃* X)) (hX : Nat.card Y = N) (hN : 0 < N)
    (hB : N < B ^ 9 * ((B ^ 6 - 1) * (B ^ 9 - 1)))
    (hL : ∀ r < B, 2 ≤ r → r % 3 = 2 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1)) ∣ N)
    (hU : ∀ r < B, 2 ≤ r → r % 3 = 1 → ¬ r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1)) ∣ N) :
    RowSEpsOf X := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := hY
  exact noCfgSEps_of_card (dvd_of_eq ((Nat.card_congr (e.trans b.symm).toEquiv).trans hX))
    hN hB hL hU

theorem rowSEpsOf_j3 :
    RowSEpsOf (Spor .J3) :=
  rowSEpsOf_of_card (X := Spor .J3) (Y := Blueprint.NativeSporadic.J3) (N := 50232960)
    (B := 3) CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv CFSG.Sporadic.J3.card_J3
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_mcl :
    RowSEpsOf (Spor .McL) :=
  rowSEpsOf_of_card (X := Spor .McL) (Y := Blueprint.NativeSporadic.McL) (N := 898128000)
    (B := 3) CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv CFSG.Sporadic.McL.card_McL
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_on :
    RowSEpsOf (Spor .ONan) :=
  rowSEpsOf_of_card (X := Spor .ONan) (Y := Blueprint.NativeSporadic.ON) (N := 460815505920)
    (B := 4) CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv CFSG.Sporadic.ON.card_ON
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_hn :
    RowSEpsOf (Spor .HN) :=
  rowSEpsOf_of_card (X := Spor .HN) (Y := Blueprint.NativeSporadic.HN) (N := 273030912000000)
    (B := 4) CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv CFSG.Sporadic.HN.card_HN
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_th :
    RowSEpsOf (Spor .Th) :=
  rowSEpsOf_of_card (X := Spor .Th) (Y := Blueprint.NativeSporadic.Th) (N := 90745943887872000)
    (B := 6) CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    ((Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv).trans CFSG.Sporadic.Bridge.Th.card_J)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_co3 :
    RowSEpsOf (Spor .Co3) :=
  rowSEpsOf_of_card (X := Spor .Co3) (Y := Blueprint.NativeSporadic.Co3) (N := 495766656000)
    (B := 4) CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv CFSG.Sporadic.Co3.card_Co3
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_co2 :
    RowSEpsOf (Spor .Co2) :=
  rowSEpsOf_of_card (X := Spor .Co2) (Y := Blueprint.NativeSporadic.Co2) (N := 42305421312000)
    (B := 4) CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv CFSG.Sporadic.Co2.card_Co2
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_suz :
    RowSEpsOf (Spor .Suz) :=
  rowSEpsOf_of_card (X := Spor .Suz) (Y := Blueprint.NativeSporadic.Suz) (N := 448345497600)
    (B := 4) CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv CFSG.Sporadic.Suz.card_Suz
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_ly :
    RowSEpsOf (Spor .Ly) :=
  rowSEpsOf_of_card (X := Spor .Ly) (Y := Blueprint.NativeSporadic.Ly) (N := 51765179004000000)
    (B := 5) CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv CFSG.Sporadic.Ly.card_Ly
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
