module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.SEITZ12

abbrev conjSub {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

structure SuzukiTwo {G : Type*} [Group G] (q : ℕ) (S Z : Subgroup G) : Prop where
  Z_le : Z ≤ S
  card_S : Nat.card S = q ^ 2
  card_Z : Nat.card Z = q
  sq_mem : ∀ s ∈ S, s * s ∈ Z
  exists_sq : ∀ z ∈ Z, z ≠ 1 → ∃ s ∈ S, s * s = z
  eq_one_of_sq : ∀ s ∈ S, s * s = 1 → s ∈ Z
  sq_Z : ∀ z ∈ Z, z * z = 1
  central : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z

theorem mem_conjSub {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ conjSub H g ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.RankThree.PartOne.SEITZ12
