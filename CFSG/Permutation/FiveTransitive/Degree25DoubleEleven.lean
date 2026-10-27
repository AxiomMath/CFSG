module

public import CFSG.Permutation.FiveTransitive.Degree25Eleven

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem dvd_twenty_two_of_dvd_two_hundred_forty_two
    {k : ℕ} (hkdvd : k ∣ 242) (hnot : ¬121 ∣ k) :
    k ∣ 22 := by
  have hkne : k ≠ 0 := by
    intro hk
    subst k
    norm_num at hkdvd
  apply
    (Nat.factorization_le_iff_dvd hkne
      (by norm_num : (22 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hkne
      (by norm_num : (242 : ℕ) ≠ 0)).mpr hkdvd) p
  by_cases hp : p = 11
  · subst p
    have hlt : k.factorization 11 < 2 := by
      rw [← not_le]
      intro htwo
      exact hnot
        ((show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
          hkne |>.mpr htwo)
    have htarget : (22 : ℕ).factorization 11 = 1 := by
      rw [show 22 = 11 * 2 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 11 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (242 : ℕ).factorization p =
          (22 : ℕ).factorization p := by
      have hp' : 11 ≠ p := Ne.symm hp
      rw [show 242 = 11 * 22 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 11 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

theorem order_eleven_cycleType_eq_double
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 11) :
    (u : Equiv.Perm X).cycleType = {11, 11} := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 25 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ _
      _ = 25 := hcard
  have hmLe : m + 1 ≤ 2 := by
    nlinarith
  have hmPos : 0 < m + 1 := Nat.zero_lt_succ m
  rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
  · have hgcycle : g.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hm,
        Multiset.card_replicate, hmOne]
    have hgsupport : g.support.card = 11 := by
      rw [← hgcycle.orderOf, hgorder]
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_elevenCycle
          X P hcard h5 u.prop hgcycle hgsupport))
  · rw [hm, hgorder, hmTwo]
    norm_num

theorem sylow_eleven_normalizer_constraints_of_centralizer_card_dvd
    (K : Type) [Group K] [Fintype K]
    (m : ℕ)
    (S : Sylow 11 K) (hScard : Nat.card S = 11)
    (hcentralizer :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup K) : Set K)) ∣ 11 * m) :
    let C : Subgroup K :=
      Subgroup.centralizer ((S : Subgroup K) : Set K)
    let N : Subgroup K :=
      Subgroup.normalizer ((S : Subgroup K) : Set K)
    let c := (S : Subgroup K).relIndex C
    let r := C.relIndex N
    c ∣ m ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card K := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup K :=
    Subgroup.centralizer ((S : Subgroup K) : Set K)
  let N : Subgroup K :=
    Subgroup.normalizer ((S : Subgroup K) : Set K)
  let c := (S : Subgroup K).relIndex C
  let r := C.relIndex N
  change
    c ∣ m ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card K
  have hSleC : (S : Subgroup K) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSsubCard :
      Nat.card ((S : Subgroup K).subgroupOf C) = 11 := by
    calc
      Nat.card ((S : Subgroup K).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 11 := hScard
  have hcCardRaw :=
    ((S : Subgroup K).subgroupOf C).index_mul_card
  have hcCard : c * 11 = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup K).subgroupOf C).index * 11 =
        Nat.card C
    calc
      ((S : Subgroup K).subgroupOf C).index * 11 =
          ((S : Subgroup K).subgroupOf C).index *
            Nat.card ((S : Subgroup K).subgroupOf C) :=
        congrArg
          (((S : Subgroup K).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ m := by
    obtain ⟨t, ht⟩ := hcentralizer
    refine ⟨t, ?_⟩
    have hcancel : 11 * m = 11 * (c * t) := by
      calc
        11 * m = Nat.card C * t := ht
        _ = (c * 11) * t := by rw [hcCard]
        _ = 11 * (c * t) := by ring
    omega
  have hAutCard : Nat.card (MulAut S) = 10 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (show Nat.Prime 11 by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 10 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer
          ((S : Subgroup K) : Set K)).relIndex
          (Subgroup.normalizer
            ((S : Subgroup K) : Set K)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
  have hrDvd : r ∣ 10 := by
    change C.relIndex N ∣ 10
    rwa [hrEq]
  letI : (S : Subgroup K).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 11 = 1 := by
    change
      (Subgroup.normalizer
        ((S : Subgroup K) : Set K)).index % 11 = 1
    have hsylow :
        (Subgroup.normalizer (S : Set K)).index ≡
          1 [MOD 11] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 11 K
    change
      (Subgroup.normalizer
          ((S : Subgroup K) : Set K)).index % 11 =
        1 % 11 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          ((S : Subgroup K) : Set K))
  have hCindexCard := C.index_mul_card
  have hproduct :
      c * r * N.index * 11 = Nat.card K := by
    calc
      c * r * N.index * 11 =
          (r * N.index) * (c * 11) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card K := hCindexCard
  exact
    ⟨hcDvd, hrDvd, hcPos, hrPos, hNmod, hproduct⟩

end FiveTransitive.Degree25

end CFSG
