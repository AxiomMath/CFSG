module

public import Mathlib.GroupTheory.Sylow

public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.Degree28ThirteenArithmetic

theorem sylow_thirteen_normalizer_constraints_of_centralizer_card_dvd
    (K : Type) [Group K] [Fintype K]
    (m : ℕ)
    (S : Sylow 13 K) (hScard : Nat.card S = 13)
    (hcentralizer :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup K) : Set K)) ∣ 13 * m) :
    let C : Subgroup K :=
      Subgroup.centralizer ((S : Subgroup K) : Set K)
    let N : Subgroup K :=
      Subgroup.normalizer ((S : Subgroup K) : Set K)
    let c := (S : Subgroup K).relIndex C
    let r := C.relIndex N
    c ∣ m ∧ r ∣ 12 ∧ 0 < c ∧ 0 < r ∧
      N.index % 13 = 1 ∧
      c * r * N.index * 13 = Nat.card K := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let _ : IsCyclic S :=
    isCyclic_of_prime_card hScard
  let _ : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup K :=
    Subgroup.centralizer ((S : Subgroup K) : Set K)
  let N : Subgroup K :=
    Subgroup.normalizer ((S : Subgroup K) : Set K)
  let c := (S : Subgroup K).relIndex C
  let r := C.relIndex N
  change
    c ∣ m ∧ r ∣ 12 ∧ 0 < c ∧ 0 < r ∧
      N.index % 13 = 1 ∧
      c * r * N.index * 13 = Nat.card K
  have hSleC : (S : Subgroup K) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSsubCard :
      Nat.card ((S : Subgroup K).subgroupOf C) = 13 := by
    calc
      Nat.card ((S : Subgroup K).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 13 := hScard
  have hcCardRaw :=
    ((S : Subgroup K).subgroupOf C).index_mul_card
  have hcCard : c * 13 = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup K).subgroupOf C).index * 13 =
        Nat.card C
    calc
      ((S : Subgroup K).subgroupOf C).index * 13 =
          ((S : Subgroup K).subgroupOf C).index *
            Nat.card ((S : Subgroup K).subgroupOf C) :=
        congrArg
          (((S : Subgroup K).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ m := by
    obtain ⟨t, ht⟩ := hcentralizer
    refine ⟨t, ?_⟩
    have hcancel : 13 * m = 13 * (c * t) := by
      calc
        13 * m = Nat.card C * t := ht
        _ = (c * 13) * t := by rw [hcCard]
        _ = 13 * (c * t) := by ring
    omega
  have hAutCard : Nat.card (MulAut S) = 12 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (show Nat.Prime 13 by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 12 := by
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
  have hrDvd : r ∣ 12 := by
    change C.relIndex N ∣ 12
    rwa [hrEq]
  let _ : (S : Subgroup K).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  let _ : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 13 = 1 := by
    change
      (Subgroup.normalizer
        ((S : Subgroup K) : Set K)).index % 13 = 1
    have hsylow :
        (Subgroup.normalizer (S : Set K)).index ≡
          1 [MOD 13] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 13 K
    change
      (Subgroup.normalizer
          ((S : Subgroup K) : Set K)).index % 13 =
        1 % 13 at hsylow
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
      c * r * N.index * 13 = Nat.card K := by
    calc
      c * r * N.index * 13 =
          (r * N.index) * (c * 13) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card K := hCindexCard
  exact
    ⟨hcDvd, hrDvd, hcPos, hrPos, hNmod, hproduct⟩

theorem exponent_cases {a c r j : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ 9) (hc : c ∣ 2) (hr : r ∣ 12)
    (hcpos : 0 < c) (hrpos : 0 < r)
    (heven : 2 ∣ c * r) (hj : j % 13 = 1) (heq : c * r * j * 13 = 11793600 * 2 ^ a) :
    a = 2 ∨ a = 3 ∨ a = 4 := by
  have hcle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hc
  have hrle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hr
  interval_cases c <;> interval_cases r <;> norm_num at hr <;> norm_num at heven
  all_goals interval_cases a <;> norm_num at heq ⊢ <;> omega

end FiveTransitive.Degree28ThirteenArithmetic

end CFSG
