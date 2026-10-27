module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

theorem ncard_colSet {j n : ℕ} (S : Set (Fin n → ZMod 2)) :
    {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i ∈ S}.ncard = S.ncard ^ j := by
  have e : {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i ∈ S} ≃ (Fin j → S) :=
    Equiv.subtypePiEquivPi (β := fun _ => Fin n → ZMod 2) (p := fun _ b => b ∈ S)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun]
  simp

theorem range_actM_eq {j n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Set.range (fun Y' : Fin j → Fin n → ZMod 2 => actM B Y') =
      {Y | ∀ i, Y i ∈ Set.range (fun v : Fin n → ZMod 2 => B.mulVec v)} := by
  ext Y
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Y', rfl⟩ i
    exact ⟨Y' i, rfl⟩
  · intro h
    choose v hv using h
    exact ⟨v, funext fun i => hv i⟩

theorem ncard_ker_le {n : ℕ} (hn : n ≤ 5) {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : B ≠ 0) :
    {v : Fin n → ZMod 2 | B.mulVec v = 0}.ncard ≤ 16 := by
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ZMod 2, B.mulVec w ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    apply hB
    ext i k
    have h := congrFun (hcon (Pi.single k 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hTK : ((fun v => w + v) '' {v : Fin n → ZMod 2 | B.mulVec v = 0}).ncard
      = {v : Fin n → ZMod 2 | B.mulVec v = 0}.ncard :=
    Set.ncard_image_of_injective _ (fun x y h => add_left_cancel h)
  have hdisj : Disjoint {v : Fin n → ZMod 2 | B.mulVec v = 0}
      ((fun v => w + v) '' {v : Fin n → ZMod 2 | B.mulVec v = 0}) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨u, hu, rfl⟩
    apply hw
    have h1 : B.mulVec u = 0 := hu
    have h2 : B.mulVec (w + u) = 0 := ha
    rw [Matrix.mulVec_add, h1, add_zero] at h2
    exact h2
  have hcard : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_fun]
    simp
  have hle : ({v : Fin n → ZMod 2 | B.mulVec v = 0} ∪
      ((fun v => w + v) '' {v : Fin n → ZMod 2 | B.mulVec v = 0})).ncard ≤ 2 ^ n := by
    rw [← hcard, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [Set.ncard_union_eq hdisj, hTK] at hle
  have h32 : 2 ^ n ≤ 32 := by
    calc 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 32 := by norm_num
  omega

theorem exists_ne_zero_of_ncard_two {n : ℕ} {S : Set (Fin n → ZMod 2)}
    (h0 : (0 : Fin n → ZMod 2) ∈ S) (h2 : S.ncard = 2) :
    ∃ a : Fin n → ZMod 2, a ≠ 0 ∧ ∀ v, v ∈ S ↔ v = 0 ∨ v = a := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
  rcases h0 with rfl | rfl
  · refine ⟨y, fun h => hxy h.symm, fun v => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  · refine ⟨x, hxy, fun v => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem colSet_two_eq_range_tens {j n : ℕ} {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i = 0 ∨ Y i = a} =
      Set.range (fun t : Fin j → ZMod 2 => tens a t) := by
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    refine ⟨fun i => if Y i = a then 1 else 0, ?_⟩
    funext i
    rcases h i with h1 | h1
    · have hne : Y i ≠ a := by
        rw [h1]
        exact Ne.symm ha
      simp only [tens_apply]
      rw [if_neg hne, h1, zero_smul]
    · simp only [tens_apply]
      rw [if_pos h1, one_smul, h1]
  · rintro ⟨t, rfl⟩ i
    rw [tens_apply]
    rcases key (t i) with h | h <;> simp [h]

theorem ncard_range_tens {j n : ℕ} {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    (Set.range (fun t : Fin j → ZMod 2 => tens a t)).ncard = 2 ^ j := by
  obtain ⟨b, hb⟩ : ∃ b, a b ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    exact ha (funext fun c => hcon c)
  have hb1 : a b = 1 := by
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact key _ hb
  have hinj : Function.Injective (fun t : Fin j → ZMod 2 => tens a t) := by
    intro t t' h
    funext i
    have h2 : tens a t i b = tens a t' i b := congrFun (congrFun h i) b
    rw [tens_apply_apply, tens_apply_apply, hb1, mul_one, mul_one] at h2
    exact h2
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_fun]
  simp

end CFSG.Quasithin.H13.Ch4.NSB
