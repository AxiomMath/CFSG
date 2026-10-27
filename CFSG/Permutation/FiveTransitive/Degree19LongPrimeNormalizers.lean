module

public import CFSG.Permutation.FiveTransitive.FewFixedPrimeCycle

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

theorem sylow_long_prime_card_eq_prime
    (P : Type) [Group P] [Fintype P]
    (h : ℕ) (hPcard : Nat.card P = 1395360 * h)
    (hdiv : h ∣ 497664)
    {p : ℕ} (hpCases : p = 17 ∨ p = 19)
    (S : Sylow p P) :
    Nat.card S = p := by
  classical
  rcases hpCases with rfl | rfl
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    have hnot : ¬17 ∣ h := by
      intro hdvd
      have : 17 ∣ 497664 := hdvd.trans hdiv
      norm_num at this
    have hh : h ≠ 0 := by
      intro hz
      subst h
      exact hnot (dvd_zero 17)
    have hfactorization :
        (1395360 * h).factorization 17 = 1 := by
      rw [show 1395360 = 17 * 82080 by norm_num,
        Nat.mul_assoc,
        Nat.factorization_mul (by norm_num)
          (Nat.mul_ne_zero (by norm_num) hh),
        Finsupp.add_apply,
        (show Nat.Prime 17 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) hh,
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd hnot]
      norm_num
    rw [S.card_eq_multiplicity, hPcard,
      hfactorization]
    norm_num
  · letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have hnot : ¬19 ∣ h := by
      intro hdvd
      have : 19 ∣ 497664 := hdvd.trans hdiv
      norm_num at this
    have hh : h ≠ 0 := by
      intro hz
      subst h
      exact hnot (dvd_zero 19)
    have hfactorization :
        (1395360 * h).factorization 19 = 1 := by
      rw [show 1395360 = 19 * 73440 by norm_num,
        Nat.mul_assoc,
        Nat.factorization_mul (by norm_num)
          (Nat.mul_ne_zero (by norm_num) hh),
        Finsupp.add_apply,
        (show Nat.Prime 19 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) hh,
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd hnot]
      norm_num
    rw [S.card_eq_multiplicity, hPcard,
      hfactorization]
    norm_num

theorem long_prime_normalizer_constraints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {p f : ℕ} (hp : p.Prime) (hpSeven : 7 ≤ p)
    (hfFive : f ≤ 5) (hcard : Fintype.card X = p + f)
    (S : Sylow p P) (hScard : Nat.card S = p) :
    let C := Subgroup.centralizer (S : Set P)
    let N := Subgroup.normalizer (S : Set P)
    C.relIndex N ∣ p - 1 ∧
      0 < C.relIndex N ∧
      N.index % p = 1 ∧
      C.relIndex N * N.index * p = Nat.card P := by
  classical
  dsimp
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorderS : orderOf u = p :=
    huorder.trans hScard
  have huorderP : orderOf (u : P) = p := by
    calc
      orderOf (u : P) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = p := huorderS
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hSleC : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hCle :
      C ≤ Subgroup.centralizer
        ({(u : P)} : Set P) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hq (u : P) u.prop).symm
  have hsingletonCard :
      Nat.card
          (Subgroup.centralizer
            ({(u : P)} : Set P)) = p :=
    FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
      X P hp hpSeven (hfFive.trans (by norm_num)) hcard h5 hnotAlt
        (u : P) huorderP
  have hCdivP : Nat.card C ∣ p := by
    rw [← hsingletonCard]
    exact Subgroup.card_dvd_of_le hCle
  have hpDvdC : p ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSleC
  have hCcard : Nat.card C = p :=
    Nat.dvd_antisymm hCdivP hpDvdC
  have hAutCard : Nat.card (MulAut S) = p - 1 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime hp]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ p - 1 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : C.relIndex N ∣ p - 1 := by
    rwa [hrEq]
  have hsmod : N.index % p = 1 := by
    change
      (Subgroup.normalizer (S : Set P)).index % p = 1
    have hsylow :
        (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD p] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one p P
    change
      (Subgroup.normalizer (S : Set P)).index % p =
        1 % p at hsylow
    rw [Nat.mod_eq_of_lt hp.one_lt] at hsylow
    exact hsylow
  have hrel : C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S : Set P))
  have hCindex := C.index_mul_card
  rw [hCcard, ← hrel] at hCindex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact ⟨hrDvd,
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero,
    hsmod, hCindex⟩

end FiveTransitive.Degree19

end CFSG
