module

public import CFSG.OddTranspositions.O4PairTenGraph

public section

namespace CFSG.OddTranspositions

open CFSG.OddTranspositions.QZ

variable {G : Type*} [Group G]

@[expose] def WidthLe (D : Set G) (n : ℕ) : Prop :=
  ∀ S : Finset G, (↑S : Set G) ⊆ D →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Commute x y) → S.card ≤ n

theorem widthLe_two_iff {D : Set G} :
    WidthLe D 2 ↔ ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x ≠ y → x ≠ z → y ≠ z →
      ¬ (Commute x y ∧ Commute x z ∧ Commute y z) := by
  classical
  constructor
  · rintro h x hx y hy z hz hxy hxz hyz ⟨hxy', hxz', hyz'⟩
    have hsub : (↑({x, y, z} : Finset G) : Set G) ⊆ D := by
      intro w hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    have hcomm : ∀ a ∈ ({x, y, z} : Finset G), ∀ b ∈ ({x, y, z} : Finset G),
        a ≠ b → Commute a b := by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | exact hxy'
          | exact hxz'
          | exact hyz'
          | exact hxy'.symm
          | exact hxz'.symm
          | exact hyz'.symm
    have hle := h _ hsub hcomm
    have h2 : 2 < ({x, y, z} : Finset G).card :=
      Finset.two_lt_card.mpr ⟨x, by simp, y, by simp, z, by simp, hxy, hxz, hyz⟩
    omega
  · intro h S hS hcomm
    by_contra hle
    have h3 : 2 < S.card := by omega
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp h3
    exact h x (hS hx) y (hS hy) z (hS hz) hxy hxz hyz
      ⟨hcomm x hx y hy hxy, hcomm x hx z hz hxz, hcomm y hy z hz hyz⟩

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

private instance (priority := 2000) f25tDecEqInst : DecidableEq F25t := f25tDecEq

private def commuteXDecidable (i j : Fin 10) : Decidable (Commute (x i) (x j)) :=
  decidable_of_iff (X i * X j = X j * X i ∨ X i * X j = -(X j * X i))
    (commute_x_iff i j).symm

private instance instDecidableRelCommuteX :
    DecidableRel (fun a b : Fin 10 => Commute (x a) (x b)) :=
  fun a b => commuteXDecidable a b

end CFSG.OddTranspositions
