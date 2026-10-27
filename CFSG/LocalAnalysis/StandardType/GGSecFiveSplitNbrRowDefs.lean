module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggRowP_SA (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 3 ≤ lab.rank ∨ lab.tag = .D ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_SD (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_SE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_SE7 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_SE8 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_ESU (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_EOmP (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_EOmM (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_ETwE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_EE7 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_EE8 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_NB (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)

@[expose] def ggRowP_NF4 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)

@[expose] def ggRowP_NAP (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 3 ≤ lab.rank ∨ lab.tag = .D ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_NTwAM (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_NDOdd (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggRowP_NTwD (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)

@[expose] def ggRowP_NE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1 ∨ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggRowP_Small (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank ≤ 2) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
    lab.tag = .B2der ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ (lab.tag = .twA ∧ lab.rank ≤ 2) ∨
    (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    lab.tag = .twF4der

@[expose] def ggRowP_ZA8 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7

@[expose] def ggRowP_ZE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7

@[expose] def GGNSRowLab (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_SA p lab ∨ ggRowP_SD p lab ∨ ggRowP_SE6 p lab ∨ ggRowP_SE7 p lab ∨ ggRowP_SE8 p lab ∨
    ggRowP_ESU p lab ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab ∨ ggRowP_ETwE6 p lab ∨
    ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
    ggRowP_NB p lab ∨ ggRowP_NF4 p lab ∨ ggRowP_NAP p lab ∨ ggRowP_NTwAM p lab ∨
    ggRowP_NDOdd p lab ∨ ggRowP_NTwD p lab ∨ ggRowP_NE6 p lab ∨
    ggRowP_Small p lab ∨ ggRowP_ZA8 p lab ∨ ggRowP_ZE6 p lab

end CFSG.StandardType

end
