module

public import CFSG.RankThree.PartOne.S13K.KFLift
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KRowDeg (r f g : ℕ) : Prop :=
  match r with
  | 1 | 2 | 7 | 9 | 10 | 11 | 12 => g = f
  | 3 => g = f ∨ g = 3 * f
  | 5 | 6 | 8 => g = f ∨ g = 2 * f
  | _ => False

@[expose] def KF132At (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → r ≠ 4 → RowModel p L r → (r ≤ 8 → E = A) →
    (9 ≤ r → Nat.card E = p ^ 4) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      ∃ f g : ℕ, RowModelF p L r f ∧ KRowDeg r f g ∧ KFAt p E g t

@[expose] def KF132Short8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → RowModel p L 8 → E = A →
    ∃ f : ℕ, RowModelF p L 8 f ∧
      ∃ t ∈ reflectionSet p E, t ∈ torusImage E L ∧ KFAt p E (2 * f) t

theorem two_pow_sub_one_dvd_mul (f k : ℕ) : 2 ^ f - 1 ∣ 2 ^ (k * f) - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 k
  rwa [one_pow, ← pow_mul'] at this

theorem kf132Types_of_at {r : ℕ} (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hr4 : r ≠ 4) (h : KF132At r) :
    KF132Types r := by
  intro G _ _ p A c L E hH hF hF13 hT hrow hrA hr9 t ht htL K hK
  obtain ⟨f, g, hRM, hdeg, hKF⟩ := h G p A c L E hH hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hKeq : K = kZero p E t := hK.2 hKF.1
  have hmod : StatedClassicalModel ↥K .PSL 2 2 g := by
    rw [hKeq]
    exact hKF.2.1
  refine ⟨f, hRM, ?_, fun _ => by rw [hKeq]; exact hKF.2.2.2.1⟩
  interval_cases r
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  · exact absurd rfl hr4
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hmod

theorem kf132At_split {r : ℕ} (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 7) (h : KF132At r)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (hH : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hrow : RowModel p L r) (hrA : E = A)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) :
    ∃ g : ℕ, p ∣ 2 ^ g - 1 ∧ KFAt p E g t := by
  have hr4 : r ≠ 4 := by omega
  have hrA' : r ≤ 8 → E = A := fun _ => hrA
  have hr9' : 9 ≤ r → Nat.card E = p ^ 4 := fun h9 => by omega
  obtain ⟨f, g, hRM, hdeg, hKF⟩ := h G p A c L E hH hF hF13 hT hr4 hrow hrA' hr9' t ht htL
  have hpf : p ∣ 2 ^ f - 1 := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hRM.2.1
  refine ⟨g, ?_, hKF⟩
  have h2 : p ∣ 2 ^ (2 * f) - 1 := hpf.trans (two_pow_sub_one_dvd_mul f 2)
  have h3 : p ∣ 2 ^ (3 * f) - 1 := hpf.trans (two_pow_sub_one_dvd_mul f 3)
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hpf
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hpf
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h3
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h2
  · simp only [KRowDeg] at hdeg
    rcases hdeg with rfl | rfl
    · exact hpf
    · exact h2
  · simp only [KRowDeg] at hdeg
    subst hdeg
    exact hpf

theorem kf132Short8_split (h : KF132Short8) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (hH : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hrow : RowModel p L 8) (hrA : E = A) :
    ∃ t ∈ reflectionSet p E, t ∈ torusImage E L ∧ ∃ g : ℕ, p ∣ 2 ^ g - 1 ∧ KFAt p E g t := by
  obtain ⟨f, hRM, t, ht, htL, hKF⟩ := h G p A c L E hH hF hF13 hT hrow hrA
  refine ⟨t, ht, htL, 2 * f, ?_, hKF⟩
  have hpf : p ∣ 2 ^ f + 1 := hRM.2.1
  have h1 : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsq : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [two_mul, pow_add]
    have hpos2 : 1 ≤ 2 ^ f * 2 ^ f := Nat.mul_pos hpos hpos
    rw [hsq]
    zify [hpos, hpos2]
    ring
  rw [h1]
  exact Dvd.dvd.mul_left hpf _

end CFSG.RankThree.PartOne.S13K
