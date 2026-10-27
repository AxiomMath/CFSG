module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG

namespace FiveTransitive.PairFixedExceptionTransport

open MulAction

private theorem image_exception_eq
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (B : Subgroup G) (F O : Set X) (a x c : G)
    (hsemifree : ∀ b : B, ∀ y : X, y ∉ F → y ∉ O → b.val • y = y → b = 1)
    (hO : ∀ y ∈ O, y ∉ F ∧ (x • y = y ∨ (a * x) • y = y))
    (hx : x ≠ 1) (hax : a * x ≠ 1)
    (hcF : ∀ y : X, y ∈ F ↔ c • y ∈ F)
    (haB : c * a * c⁻¹ ∈ B) (hxB : c * x * c⁻¹ ∈ B) :
    (fun y : X => c • y) '' O = O := by
  have haxB : c * (a * x) * c⁻¹ ∈ B := by
    have hm := B.mul_mem haB hxB
    convert hm using 1
    group
  have hmaps : (fun y : X => c • y) '' O ⊆ O := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hout
    have hnotF : c • y ∉ F := fun h => (hO y hy).1 ((hcF y).mpr h)
    have hfix (g : G) (hg : g • y = y) : (c * g * c⁻¹) • (c • y) = c • y := by
      simp only [mul_smul, inv_smul_smul, hg]
    have hne (g : G) (hg : g ≠ 1) : c * g * c⁻¹ ≠ 1 := by
      intro he
      have hh : MulAut.conj c g = MulAut.conj c 1 := by simpa using he
      exact hg ((MulAut.conj c).injective hh)
    rcases (hO y hy).2 with h | h
    · exact hne x hx (congrArg Subtype.val (hsemifree ⟨_, hxB⟩ _ hnotF hout (hfix x h)))
    · exact hne (a * x) hax (congrArg Subtype.val (hsemifree ⟨_, haxB⟩ _ hnotF hout (hfix (a * x) h)))
  apply Set.eq_of_subset_of_ncard_le hmaps
  rw [Set.ncard_image_of_injective O (MulAction.injective c)]

theorem contradiction
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (B : Subgroup G) (F O : Set X) (a x u c : G) (z : X)
    (hsemifree : ∀ b : B, ∀ y : X, y ∉ F → y ∉ O → b.val • y = y → b = 1)
    (hO : ∀ y ∈ O, y ∉ F ∧ (x • y = y ∨ (a * x) • y = y))
    (hx : x ≠ 1) (hax : a * x ≠ 1) (hu : u ≠ 1)
    (hzF : z ∉ F) (hzO : z ∉ O) (huz : u • z = z)
    (hcF : ∀ y : X, y ∈ F ↔ c • y ∈ F)
    (haB : c * a * c⁻¹ ∈ B) (hxB : c * x * c⁻¹ ∈ B) (huB : c * u * c⁻¹ ∈ B) :
    False := by
  have he := image_exception_eq B F O a x c hsemifree hO hx hax hcF haB hxB
  have hcO : c • z ∉ O := by
    intro hz
    rw [← he] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    exact hzO ((MulAction.injective c hyz) ▸ hy)
  have hcnotF : c • z ∉ F := fun h => hzF ((hcF z).mpr h)
  have hfix : (c * u * c⁻¹) • (c • z) = c • z := by
    simp only [mul_smul, inv_smul_smul, huz]
  have hh := congrArg Subtype.val (hsemifree ⟨_, huB⟩ _ hcnotF hcO hfix)
  have hconj : MulAut.conj c u = MulAut.conj c 1 := by simpa using hh
  exact hu ((MulAut.conj c).injective hconj)

end FiveTransitive.PairFixedExceptionTransport

end CFSG
