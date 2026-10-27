module

public import CFSG.RankThree.PartOne.S11d.FieldFFTwo
public import CFSG.RankThree.PartOne.Mult.Exceptional

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank Subgroup
open CFSG.RankThree.PartOne

theorem exceptionalOrders_eq_one (t : StatedLieTag) (n m : ℕ) (hm : 5 ≤ m) :
    exceptionalOrders t n 2 m = (1, 1) := by
  unfold exceptionalOrders
  split
  all_goals first | rfl | (exfalso; omega)

theorem genericOrders_odd (t : StatedLieTag) (n m : ℕ) (hm : 1 ≤ m)
    (hn : t = .POmegaMinus → 1 ≤ n) (hne : t ≠ .POmegaOdd) :
    ¬ 2 ∣ (genericOrders t n 2 m).1 * (genericOrders t n 2 m).2 := by
  have hq : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd1 : Odd (2 ^ m - 1) := by
    obtain ⟨r, hr⟩ := hq
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨r - 1, by omega⟩
  have hodd2 : Odd (2 ^ m + 1) := hq.add_one
  have key : ∀ {a b : ℕ}, Odd b → a ∣ b → a % 2 = 1 := fun hb hab =>
    Nat.odd_iff.mp (Odd.of_dvd_nat hb hab)
  cases t <;> simp [genericOrders]
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact key hodd2 (Nat.gcd_dvd_right _ _)
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact hne rfl
  · simp [hq]
  · have hn1 := hn rfl
    have hev : Even ((2 ^ m) ^ n) := (Nat.even_pow.mpr ⟨hq, by omega⟩)
    exact key hev.add_one (Nat.gcd_dvd_right _ _)
  · exact key (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  · exact key hodd1 (Nat.gcd_dvd_right _ _)
  · exact key (by decide : Odd 3) (Nat.gcd_dvd_left _ _)

theorem table_odd {t : StatedLieTag} {n m : ℕ} (hm : 5 ≤ m) (hn : t = .POmegaMinus → 1 ≤ n)
    (hne : t ≠ .POmegaOdd) :
    ¬ 2 ∣ ((genericOrders t n 2 m).1 * (genericOrders t n 2 m).2) *
      ((exceptionalOrders t n 2 m).1 * (exceptionalOrders t n 2 m).2) := by
  rw [exceptionalOrders_eq_one t n m hm]
  simpa using genericOrders_odd t n m (by omega) hn hne

@[expose] def OddCenterSuzukiRee : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → ∀ (t : StatedLieTag) (m : ℕ),
    5 ≤ m → (t = .twistedB2 ∨ t = .twistedF4) → LieModel (J ⧸ Subgroup.center J) t 0 2 m →
      ¬ 2 ∣ Nat.card (Subgroup.center J)


theorem oddCenterLie_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSR : OddCenterSuzukiRee) : OddCenterLie := by
  intro J _ _ hq t n m hm5 hmodel
  have : Group.IsPerfect J := hq.1
  have hadm : StatedLieAdmissible t n 2 m := statedLieAdmissible_of_lieModel hmodel
  have hne : t ≠ .POmegaOdd := fun h => by
    subst h
    exact absurd rfl hadm.2.2.2
  have hn : t = .POmegaMinus → 1 ≤ n := fun h => by
    subst h
    have := hadm.2.2
    omega
  rcases hmodel with ⟨-, hmod⟩ | ⟨hn0, ht, hM⟩ | ⟨hn0, ht, hM⟩ | ⟨hn0, ht, hM⟩
  · exact fun h2 => table_odd hm5 hn hne (h2.trans (card_center_dvd_of_model hGA hq hmod))
  · subst hn0
    obtain ⟨dd, hdd, he⟩ := Mult.exists_index_of_chevalley
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll Nat.prime_two ht hM
    have hm : Models.LieModel (J ⧸ Subgroup.center J) t 0 2 m :=
      ⟨hM.1, Or.inr ⟨rfl, dd, hdd, he⟩⟩
    exact fun h2 => table_odd hm5 hn hne (h2.trans (Mult.card_center_dvd_of_lieModel hGA hq hm))
  · subst hn0
    have hmod : LieModel (J ⧸ Subgroup.center J) t 0 2 m := Or.inr (Or.inr (Or.inl ⟨rfl, ht, hM⟩))
    have hF4 : t = .twistedF4 := by
      have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by simpa [reeTitsTags] using ht
      rcases ht' with h | h | h
      · subst h
        exact absurd hadm.2.2.2.1 (by norm_num)
      · exact h
      · subst h
        have := hadm.2.2.2.2
        omega
    exact hSR J hq t m hm5 (Or.inr hF4) hmod
  · subst hn0 ht
    exact hSR J hq .twistedB2 m hm5 (Or.inl rfl) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hM⟩)))

end CFSG.RankThree.PartOne.FieldFix
