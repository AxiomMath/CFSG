module

public import CFSG.Permutation.FiveTransitive.HallOrbitTransitivity

public section

namespace CFSG

namespace FiveTransitive.Research.HallReflectionTransitivity

open MulAction
open Research.HallOrbitTransitivity

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_hallCentralizer_maps_into_fourSet_of_reflections
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (E : Set X) (hE : E = exceptionalSet (X := X) a b)
    (sigma : X → X) (hsigmaE : Set.MapsTo sigma E E)
    (hsigmaSq : ∀ z ∈ E, sigma (sigma z) = z)
    (hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)))
    (hreflect : ∀ x : X, x ∉ E →
      ∃ x₀ : X, ∃ v : G,
        (x₀ = x ∨ x₀ = b • x) ∧ x₀ ∉ E ∧
          HallReflectionAt E sigma a b x₀ v)
    (y : X) (hy : y ∉ E) :
    ∀ x : X, x ∉ E →
      ∃ k : hallCentralizer (X := X) a b,
        (k : G) • x ∈
          ({y, a • y, b • y, (a * b) • y} : Set X) := by
  intro x hx
  obtain ⟨x₀, vx, hxChoice, hx₀E, hvx⟩ := hreflect x hx
  obtain ⟨y₀, vy, hyChoice, hy₀E, hvy⟩ := hreflect y hy
  obtain ⟨k, hk⟩ := exists_hallCentralizer_maps_regular_orbit
    a b haTwo E hE sigma hsigmaE hsigmaSq hoddC
      x₀ y₀ hx₀E hy₀E vx vy hvx hvy
  refine ⟨k, ?_⟩
  have hkb : Commute (k : G) b :=
    (mem_hallCentralizer_iff a b (k : G)).mp k.prop |>.2.2
  have hremoveB (z : X)
      (hz : (k : G) • (b • x) = z) :
      (k : G) • x = b • z := by
    calc
      (k : G) • x = b • (b • ((k : G) • x)) := by
        symm
        rw [← mul_smul, ← pow_two, hbTwo, one_smul]
      _ = b • ((k : G) • (b • x)) := by
        congr 1
        rw [← mul_smul, ← mul_smul, hkb.eq.symm]
      _ = b • z := congrArg (fun w : X ↦ b • w) hz
  rcases hxChoice with hxChoice | hxChoice
  · rw [hxChoice] at hk
    rcases hyChoice with hyChoice | hyChoice
    · rw [hyChoice] at hk
      rcases hk with hk | hk
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl hk
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inl hk)
    · rw [hyChoice] at hk
      rcases hk with hk | hk
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr (Or.inl hk))
      · have hk' : (k : G) • x = (a * b) • y := by
          calc
            (k : G) • x = a • (b • y) := hk
            _ = (a * b) • y := by rw [mul_smul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr (Or.inr hk'))
  · rw [hxChoice] at hk
    rcases hyChoice with hyChoice | hyChoice
    · rw [hyChoice] at hk
      rcases hk with hk | hk
      · have hk' := hremoveB y hk
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr (Or.inl hk'))
      · have hk' : (k : G) • x = (a * b) • y := by
          calc
            (k : G) • x = b • (a • y) := hremoveB (a • y) hk
            _ = (a * b) • y := by
              rw [← mul_smul, hab.eq, mul_smul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr (Or.inr hk'))
    · rw [hyChoice] at hk
      rcases hk with hk | hk
      · have hk' : (k : G) • x = y := by
          calc
            (k : G) • x = b • (b • y) := hremoveB (b • y) hk
            _ = y := by rw [← mul_smul, ← pow_two, hbTwo, one_smul]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl hk'
      · have hk' : (k : G) • x = a • y := by
          calc
            (k : G) • x = b • (a • (b • y)) :=
              hremoveB (a • (b • y)) hk
            _ = a • y := by
              rw [← mul_smul, ← mul_smul]
              congr 1
              calc
                (b * a) * b = (a * b) * b := by rw [← hab.eq]
                _ = a * (b * b) := by rw [mul_assoc]
                _ = a := by rw [← pow_two, hbTwo, mul_one]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inl hk')

end FiveTransitive.Research.HallReflectionTransitivity

end CFSG
