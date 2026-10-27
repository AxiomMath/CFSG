module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


theorem not_commute_psl2 {K : Type} [Group K] {g p r : ℕ}
    (hK : StatedClassicalModel K .PSL 2 2 g) (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2)
    (hpg : p ∣ 2 ^ g + 1) (hrg : r ∣ 2 ^ g - 1) {x y : K} (hx : orderOf x = p)
    (hy : orderOf y = r) : x * y ≠ y * x := by
  intro hxy
  obtain ⟨⟨-, hg, -⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ := hK
  let ε : PSL(2, F) ≃* K :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  have hq1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hodd : Nat.gcd (Nat.card F - 1) 2 = 1 := by
    rw [hcard]
    have : Odd (2 ^ g - 1) := Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact Nat.coprime_two_right.mpr this
  have hcop : Nat.Coprime p r := by
    rw [Nat.coprime_primes hp hr]
    rintro rfl
    have h1 : p ∣ (2 ^ g + 1) - (2 ^ g - 1) := Nat.dvd_sub hpg hrg
    have h2 : (2 ^ g + 1) - (2 ^ g - 1) = 2 := by omega
    rw [h2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hcomm : Commute x y := hxy
  have hord : orderOf (x * y) = p * r := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (hx ▸ hy ▸ hcop), hx, hy]
  have hord' : orderOf (ε.symm (x * y)) = p * r := by
    rw [MulEquiv.orderOf_eq]; exact hord
  have hfin := CFSG.Glauberman.Dickson.psl2_orderOf_dvd (p := 2) (f := g) (F := F) hcard
    (ε.symm (x * y))
  rw [hord', hodd, Nat.div_one, Nat.div_one, hcard] at hfin
  rcases hfin with h | h | h
  · have : p ∣ 2 := (Dvd.intro r rfl).trans h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  · have hpd : p ∣ 2 ^ g - 1 := (Dvd.intro r rfl).trans h
    have h1 : p ∣ (2 ^ g + 1) - (2 ^ g - 1) := Nat.dvd_sub hpg hpd
    have h2 : (2 ^ g + 1) - (2 ^ g - 1) = 2 := by omega
    rw [h2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  · have hrd : r ∣ 2 ^ g + 1 := (Dvd.intro_left p rfl).trans h
    have h1 : r ∣ (2 ^ g + 1) - (2 ^ g - 1) := Nat.dvd_sub hrd hrg
    have h2 : (2 ^ g + 1) - (2 ^ g - 1) = 2 := by omega
    rw [h2] at h1
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1
    subst this
    have hrodd : ¬ (2 ∣ 2 ^ g - 1) := by
      have : Odd (2 ^ g - 1) := Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
      exact fun h2 => (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 h2)
    exact hrodd hrg


end CFSG.RankThree.PartOne.K1320
