module

public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.Background.E2TwoProofSporM23Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.GroupTheory.SolvableHallNodes
public import Certificates.Certificate7123

public section

namespace CFSG.Quasithin.ModH.M23Excl

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.H.MathieuLat

abbrev L16 : Array ℕ := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9]

theorem exists_hall_two_p' {K : Type} [Group K] [Finite K] (hK : Group.IsSolvable K)
    (U : Subgroup K) (hU : IsPGroup 2 ↥U) (p : ℕ) (hp : p.Prime) :
    ∃ H : Subgroup K, U ≤ H ∧ (∀ q : ℕ, q.Prime → q ∣ Nat.card ↥H → q = 2 ∨ q = p) ∧
      ¬ 2 ∣ H.index ∧ ¬ p ∣ H.index := by
  classical
  let π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  have hU' : CFSG.IsPiSubgroup π U := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU
    have h2 : q.val ∣ 2 ^ n := hn ▸ hq
    have : q.val = 2 :=
      (Nat.prime_dvd_prime_iff_eq q.prop Nat.prime_two).1 (q.prop.dvd_of_dvd_pow h2)
    left
    exact Subtype.ext this
  obtain ⟨H, hH, hUH⟩ := CFSG.SolvableHall.solvable_hall_containment hK π U hU'
  refine ⟨H, hUH, fun q hq hqd => ?_, ?_, ?_⟩
  · rcases hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqd with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h
  · intro h2
    exact hH.p_in_pi_of_p_dvd_index ⟨2, Nat.prime_two⟩ h2 (Or.inl rfl)
  · intro hpd
    exact hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpd (Or.inr rfl)

theorem exists_hall_overgroup {Q : Type} [Group Q] [Finite Q] {S Z : Subgroup Q}
    (hS : IsPGroup 2 ↥S) (hSZ : S ≤ Z) (hZs : Group.IsSolvable ↥Z) (p : ℕ) (hp : p.Prime) :
    ∃ H : Subgroup Q, S ≤ H ∧ H ≤ Z ∧ ∃ k : ℕ, Nat.card ↥H * k = Nat.card ↥Z ∧ ¬ 2 ∣ k ∧
      ¬ p ∣ k ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥H → q = 2 ∨ q = p := by
  have hU : IsPGroup 2 ↥(S.subgroupOf Z) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  obtain ⟨H, hUH, hHq, hk2, hkp⟩ := exists_hall_two_p' hZs (S.subgroupOf Z) hU p hp
  have hHZ : H.map Z.subtype ≤ Z := Subgroup.map_subtype_le H
  have hSH : S ≤ H.map Z.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSZ]
    exact Subgroup.map_mono hUH
  have hcard : Nat.card ↥(H.map Z.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Z.subtype Subtype.val_injective).toEquiv).symm
  refine ⟨H.map Z.subtype, hSH, hHZ, H.index, ?_, hk2, hkp, ?_⟩
  · rw [hcard]
    exact Subgroup.card_mul_index H
  · intro q hq hqd
    rw [hcard] at hqd
    exact hHq q hq hqd

theorem J_eq : m23Ctx.J = 16 := m23_J

theorem card_Y {j : ℕ} (hj : j < 16) : Nat.card (m23Ctx.Y j) = L16[j]! * 128 := by
  rw [m23Ctx.Y_card (by rw [J_eq]; exact hj), om_size_eq m23_lat_cert.2.2 (by simpa using hj)]
  rfl

end CFSG.Quasithin.ModH.M23Excl
