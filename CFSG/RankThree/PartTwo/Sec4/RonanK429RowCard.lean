module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem le_card_of_isoLThreePi {T : Type} [Group T] [Finite T] [Group.IsPerfect T] {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (h : IsoLThreePi T p e) : 2520 ≤ Nat.card T := by
  have hp : p.Prime := Fact.out
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hq4 : 4 ≤ p ^ e := by
      have h1 : p ^ e ≠ 1 := fun h1 => by
        rcases Nat.pow_eq_one.mp h1 with h' | h'
        · exact hp.one_lt.ne' h'
        · omega
      omega
    have hg : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have h64 : 64 ≤ (p ^ e) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq4 3
    have h15 : 15 ≤ (p ^ e) ^ 2 - 1 := by
      have : 16 ≤ (p ^ e) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (p ^ e) ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have h63 : 63 ≤ (p ^ e) ^ 3 - 1 := by omega
    have hprod : 64 * (15 * 63) ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) :=
      Nat.mul_le_mul h64 (Nat.mul_le_mul h15 h63)
    have hle : 64 * (15 * 63) ≤ Nat.card T * 3 :=
      hprod.trans (hc ▸ Nat.mul_le_mul_left _ hg)
    omega
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    by_cases hq2 : p ^ e = 2
    · exfalso
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq2
      have hs := Sec13.isSolvable_projSU_two
      have hsolv : IsSolvable T :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have h1 : Nat.card T = 1 := by
        by_contra hne
        have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by
          have := Nat.card_pos (α := T)
          omega)
        exact Group.IsPerfect.not_isSolvable T hsolv
      rw [h1] at hc
      norm_num at hc
    · have hq5 : 5 ≤ p ^ e := by
        have h1 : p ^ e ≠ 1 := fun h1 => by
          rcases Nat.pow_eq_one.mp h1 with h' | h'
          · exact hp.one_lt.ne' h'
          · omega
        have h2 : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      have hg : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
      have h125 : 125 ≤ (p ^ e) ^ 3 := by
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq5 3
      have h24 : 24 ≤ (p ^ e) ^ 2 - 1 := by
        have : 25 ≤ (p ^ e) ^ 2 := by
          calc 25 = 5 ^ 2 := by norm_num
            _ ≤ (p ^ e) ^ 2 := Nat.pow_le_pow_left hq5 2
        omega
      have h126 : 126 ≤ (p ^ e) ^ 3 + 1 := by omega
      have hprod : 125 * (24 * 126) ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
        Nat.mul_le_mul h125 (Nat.mul_le_mul h24 h126)
      have hle : 125 * (24 * 126) ≤ Nat.card T * 3 :=
        hprod.trans (hc ▸ Nat.mul_le_mul_left _ hg)
      omega

theorem le_card_of_isType429
    {T : Type} [Group T] [Finite T] [Group.IsPerfect T]
    (h : IsType429 T) : 2520 ≤ Nat.card T := by
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact le_card_of_isoLThreePi he h
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
    decide
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.J2.card_J2]
    norm_num

theorem noCfgS429_of_card_lt
    {S : Type} [Group S] [Finite S] (h : Nat.card S < 2520) :
    NoCfgS429 S := by
  intro A σ K hc
  haveI : Group.IsPerfect K := hc.isPerfect
  have h1 := le_card_of_isType429 hc.isType
  have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h3 : Nat.card K ≤ Nat.card S := Subgroup.card_le_card_group K
  omega

end CFSG.RankThree.PartTwo.Sec4.RonanK429
