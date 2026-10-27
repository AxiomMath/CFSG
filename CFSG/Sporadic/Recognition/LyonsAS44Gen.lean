module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

theorem comm_of_inverted {G : Type*} [Group G] {A : Subgroup G} {s : G}
    (hsA : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h1 : s * (a * b) * s⁻¹ = (a * b)⁻¹ := hsA _ (A.mul_mem ha hb)
  have h2 : s * (a * b) * s⁻¹ = a⁻¹ * b⁻¹ :=
    calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hsA a ha, hsA b hb]
  have h3 : (a * b)⁻¹ = (b * a)⁻¹ := by rw [← h1, h2, mul_inv_rev]
  exact inv_injective h3

theorem nonempty_mulEquiv_prod_of_hom_neg_one {C : Type*} [Group C] {s : C}
    (hs : s ∈ Subgroup.center C) (hs2 : s * s = 1) (hs1 : s ≠ 1) (χ : C →* ℤˣ)
    (hχ : χ s = -1) : Nonempty (C ≃* Multiplicative (ZMod 2) × χ.ker) := by
  have _ : s ≠ 1 := hs1
  have hcomm : ∀ c : C, s * c = c * s := fun c => ((Subgroup.mem_center_iff.mp hs) c).symm
  have hss : ∀ x : C, s * (s * x) = x := fun x => by rw [← mul_assoc, hs2, one_mul]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hε : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hεε : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
  have hdich : ∀ c : C, χ c = 1 ∨ χ c = -1 := fun c => Int.units_eq_one_or (χ c)
  have hnc : ∀ c : C, χ c = -1 → ¬ χ c = 1 := fun c h h' => hne (h.symm.trans h')
  have hker : ∀ c : C, (if χ c = 1 then c else s * c) ∈ χ.ker := by
    intro c
    rw [MonoidHom.mem_ker]
    rcases hdich c with h | h
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right (hnc c h), map_mul, hχ, h, neg_mul_neg, mul_one]
  have hεmul : ∀ a b : C,
      (if χ (a * b) = 1 then (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) =
        (if χ a = 1 then 1 else Multiplicative.ofAdd 1) *
          (if χ b = 1 then 1 else Multiplicative.ofAdd 1) := by
    intro a b
    rcases hdich a with ha | ha <;> rcases hdich b with hb | hb
    · have hab : χ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb, mul_one]
    · have hab : χ (a * b) = -1 := by rw [map_mul, ha, hb, one_mul]
      rw [ite_eq_right (hnc _ hab), ite_eq_left ha, ite_eq_right (hnc b hb), one_mul]
    · have hab : χ (a * b) = -1 := by rw [map_mul, ha, hb, mul_one]
      rw [ite_eq_right (hnc _ hab), ite_eq_right (hnc a ha), ite_eq_left hb, mul_one]
    · have hab : χ (a * b) = 1 := by rw [map_mul, ha, hb, neg_mul_neg, mul_one]
      rw [ite_eq_left hab, ite_eq_right (hnc a ha), ite_eq_right (hnc b hb), hεε]
  have hκmul : ∀ a b : C,
      (if χ (a * b) = 1 then a * b else s * (a * b)) =
        (if χ a = 1 then a else s * a) * (if χ b = 1 then b else s * b) := by
    intro a b
    rcases hdich a with ha | ha <;> rcases hdich b with hb | hb
    · have hab : χ (a * b) = 1 := by rw [map_mul, ha, hb, mul_one]
      rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb]
    · have hab : χ (a * b) = -1 := by rw [map_mul, ha, hb, one_mul]
      rw [ite_eq_right (hnc _ hab), ite_eq_left ha, ite_eq_right (hnc b hb), ← mul_assoc,
        hcomm a, mul_assoc]
    · have hab : χ (a * b) = -1 := by rw [map_mul, ha, hb, mul_one]
      rw [ite_eq_right (hnc _ hab), ite_eq_right (hnc a ha), ite_eq_left hb, mul_assoc]
    · have hab : χ (a * b) = 1 := by rw [map_mul, ha, hb, neg_mul_neg, mul_one]
      rw [ite_eq_left hab, ite_eq_right (hnc a ha), ite_eq_right (hnc b hb), hcomm a,
        mul_assoc a s, hss]
  let f : C → Multiplicative (ZMod 2) × χ.ker := fun c =>
    (if χ c = 1 then 1 else Multiplicative.ofAdd 1, ⟨if χ c = 1 then c else s * c, hker c⟩)
  have hf : ∀ a b : C, f (a * b) = f a * f b := fun a b =>
    Prod.ext (hεmul a b) (Subtype.ext (hκmul a b))
  refine ⟨MulEquiv.ofBijective (MonoidHom.mk' f hf) ⟨?_, ?_⟩⟩
  · change Function.Injective f
    intro a b hab
    have h1 : (if χ a = 1 then (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) =
        (if χ b = 1 then 1 else Multiplicative.ofAdd 1) := congrArg Prod.fst hab
    have h2 : (if χ a = 1 then a else s * a) = (if χ b = 1 then b else s * b) :=
      congrArg (fun p => (p.2 : C)) hab
    rcases hdich a with ha | ha <;> rcases hdich b with hb | hb
    · rw [ite_eq_left ha, ite_eq_left hb] at h2
      exact h2
    · rw [ite_eq_left ha, ite_eq_right (hnc b hb)] at h1
      exact absurd h1 hε.symm
    · rw [ite_eq_right (hnc a ha), ite_eq_left hb] at h1
      exact absurd h1 hε
    · rw [ite_eq_right (hnc a ha), ite_eq_right (hnc b hb)] at h2
      exact mul_left_cancel h2
  · change Function.Surjective f
    rintro ⟨e, k, hk⟩
    have hk' : χ k = 1 := hk
    have he : e = 1 ∨ e = Multiplicative.ofAdd 1 := by
      obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective e
      have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases hx x with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases he with rfl | rfl
    · exact ⟨k, Prod.ext (ite_eq_left hk') (Subtype.ext (ite_eq_left hk'))⟩
    · have hsk : χ (s * k) = -1 := by rw [map_mul, hχ, hk', mul_one]
      exact ⟨s * k, Prod.ext (ite_eq_right (hnc _ hsk))
        (Subtype.ext ((ite_eq_right (hnc _ hsk)).trans (hss k)))⟩

end CFSG.Sporadic.Recognition.LyonsSims
