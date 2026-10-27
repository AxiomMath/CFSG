module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKOdd
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Gen

public section

namespace CFSG.Quasithin.H13.Cor332

open scoped MatrixGroups

theorem isElemAbelian_map_hom {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {E : Subgroup X}
    (h : CFSG.Open.IsElemAbelian 2 E) : CFSG.Open.IsElemAbelian 2 (E.map f) :=
  CFSG.Open.IsElemAbelian.map h _

theorem card_le_four_psl2_zmod
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (E : Subgroup PSL(2, ZMod p))
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  let e := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p)
  have h := CFSG.QuasithinUnique.Lin2.card_le_four_psl2 hchar (Ab := E.map e.toMonoidHom)
    (isElemAbelian_map_hom e.toMonoidHom hE)
  have hinj : Function.Injective e.toMonoidHom := e.injective
  rwa [Subgroup.card_map_of_injective hinj] at h

theorem exists_sign_pow_two {p : ℕ} (hp7 : 7 < p)
    (hF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) :
    ∃ (ε : ℤ) (a : ℕ), (ε = 1 ∨ ε = -1) ∧ (p : ℤ) ≡ ε [ZMOD 4] ∧ (p : ℤ) - ε = 2 ^ a := by
  rcases hF with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have hk1 : 1 ≤ k := by
      by_contra h
      have : k = 0 := by omega
      subst this
      omega
    have h4 : 4 ∣ 2 ^ 2 ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ', pow_mul]
      exact dvd_pow_self (2 ^ 2) (pow_ne_zero j two_ne_zero)
    refine ⟨1, 2 ^ k, Or.inl rfl, ?_, ?_⟩
    · unfold Int.ModEq
      omega
    · rw [hk]
      push_cast
      ring
  · have h4 : 4 ∣ 2 ^ k := by
      have := pow_dvd_pow 2 hk2
      simpa using this
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨-1, k, Or.inr rfl, ?_, ?_⟩
    · unfold Int.ModEq
      omega
    · have : (p : ℤ) + 1 = 2 ^ k := by
        have h' : p + 1 = 2 ^ k := by omega
        exact_mod_cast h'
      linarith

theorem not_orderOf_commute_involution_psl2 {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1))
    (x t : PSL(2, ZMod p)) (ht : orderOf t = 2) (hxt : x * t = t * x) {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) : orderOf x ≠ r := by
  intro hxo
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hcard, pow_one]⟩
  obtain ⟨ε, a, hε1, hε, hpa⟩ := exists_sign_pow_two hp7 hF
  rw [← hcard] at hε hpa
  obtain ⟨m, hm2, ⟨e⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hodd hε hε1 ht
  have hma : 2 * m = 2 ^ a := by
    have : (2 * m : ℤ) = 2 ^ a := by rw [hm2, hpa]
    exact_mod_cast this
  have hm0 : NeZero m := ⟨by
    rintro rfl
    exact absurd hma.symm (pow_ne_zero a (by norm_num))⟩
  have hx : x ∈ Subgroup.centralizer ({t} : Set PSL(2, ZMod p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hxt.symm
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : Subgroup.centralizer ({t} : Set PSL(2, ZMod p)))
  rw [Subgroup.orderOf_mk, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hma, hxo] at h1
  have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1)
  omega

theorem twoLocalsSolvable_psl2
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hF : (∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) :
    TwoLocalsSolvable PSL(2, ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite PSL(2, ZMod p) := inferInstance
  refine twoLocalsSolvable_of 2 ?_ ?_ ?_
  · intro E hE
    simpa using card_le_four_psl2_zmod (by omega) E hE
  · intro r hr h5 hrG d hd1 hdk h
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h4 : 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdk
    omega
  · intro x z hz hxz r hr h5 hxo
    exact not_orderOf_commute_involution_psl2 hp hp7 hF x z hz hxz hr h5 hxo

end CFSG.Quasithin.H13.Cor332
