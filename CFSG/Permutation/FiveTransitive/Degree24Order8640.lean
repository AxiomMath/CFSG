module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence
public import CFSG.Permutation.FiveTransitive.Degree24FiveFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem no_five_normalizer_parameters_for_eight_thousand_six_hundred_forty
    (n c r m : ℕ)
    (hnm : n * m = 8640)
    (hnMod : n % 5 = 1)
    (hmLower : 60 ≤ m)
    (hFiveDvdC : 5 ∣ c)
    (hCdvd : c ∣ 750)
    (hrDvd : r ∣ 4)
    (hrPos : 0 < r)
    (hmEq : m = r * c) :
    False := by
  have hcLe : c ≤ 750 :=
    Nat.le_of_dvd (by norm_num) hCdvd
  have hcCases :
      c = 5 ∨ c = 10 ∨ c = 15 ∨ c = 25 ∨
      c = 30 ∨ c = 50 ∨ c = 75 ∨ c = 125 ∨
      c = 150 ∨ c = 250 ∨ c = 375 ∨ c = 750 := by
    interval_cases c <;> norm_num at hCdvd
    all_goals norm_num at hFiveDvdC
    all_goals omega
  have hrLe : r ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hrDvd
  have hrCases : r = 1 ∨ r = 2 ∨ r = 4 := by
    interval_cases r <;> norm_num at hrDvd
    all_goals omega
  rcases hcCases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hrCases with rfl | rfl | rfl
  all_goals norm_num at hmEq
  all_goals subst m
  all_goals omega

theorem five_point_stabilizer_card_ne_eight_thousand_six_hundred_forty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard :
      Nat.card (fixingSubgroup P s) = 8640) :
    False := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let S : Sylow 5 H := Sylow.nonempty.some
  have hScard : Nat.card S = 5 := by
    exact
      sylow_card_eq_prime_of_card_eq_prime_mul
        H 5 1728 (by norm_num) (by norm_num)
          (by simpa only [H] using hHcard) S
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let N : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  let n := Nat.card (Sylow 5 H)
  let c := Nat.card C
  let r := C.relIndex N
  let m := Nat.card N
  have hLower :=
    sylow_five_local_normalizer_lower_cases
      X P hcard h5 hnotAlt s hs S hScard
  have hfixed : Nat.card (sylowFixedPoints X P s S) = 9 := by
    rcases hLower with hnine | hfourteen
    · exact hnine.1
    · have hNdvdH : Nat.card N ∣ Nat.card H :=
        Subgroup.card_subgroup_dvd_card N
      have hNleH : Nat.card N ≤ Nat.card H :=
        Nat.le_of_dvd Nat.card_pos hNdvdH
      have hNlower : 907200 ≤ Nat.card N := by
        simpa only [H, S, N] using hfourteen.2
      have hHcard' : Nat.card H = 8640 := by
        simpa only [H] using hHcard
      omega
  have hmLower : 60 ≤ m := by
    rcases hLower with hnine | hfourteen
    · simpa only [H, S, N, m] using hnine.2
    · omega
  have hCdvd : c ∣ 750 := by
    simpa only [H, S, C, c] using
      sylow_five_centralizer_card_dvd_seven_hundred_fifty
        X P hcard h5 hnotAlt s hs S hScard hfixed
  have hSleC : (S : Subgroup H) ≤ C := by
    intro a ha b hb
    exact
      congrArg Subtype.val
        (mul_comm'
          (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hFiveDvdC : 5 ∣ c := by
    change 5 ∣ Nat.card C
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSleC
  have hAutCard : Nat.card (MulAut S) = 4 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 4 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      r = Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set H)).relIndex
          (Subgroup.normalizer (S : Set H)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : r ∣ 4 := by
    rw [hrEq]
    exact hrangeDvd
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrel :
      r * N.index = C.index := by
    exact
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          (S : Set H))
  have hmEq : m = r * c := by
    have hproduct :
        N.index * (r * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (r * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card H := C.index_mul_card
        _ = N.index * Nat.card N :=
          N.index_mul_card.symm
    change Nat.card N = r * Nat.card C
    exact
      (Nat.mul_left_cancel
        (Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite)
        hproduct).symm
  have hNindex : N.index = n := by
    calc
      N.index = Nat.card (Sylow 5 H) :=
        S.card_eq_index_normalizer.symm
      _ = n := rfl
  have hnm : n * m = 8640 := by
    have hproduct := N.index_mul_card
    rw [hNindex] at hproduct
    change n * Nat.card N = 8640
    calc
      n * Nat.card N = Nat.card H := hproduct
      _ = 8640 := by
        simpa only [H] using hHcard
  have hnMod : n % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 H
    change n % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  exact
    no_five_normalizer_parameters_for_eight_thousand_six_hundred_forty
      n c r m hnm hnMod hmLower hFiveDvdC hCdvd
        hrDvd hrPos hmEq

end FiveTransitive.Degree24

end CFSG
