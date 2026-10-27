module

public import CFSG.Assembly.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace MulAut

theorem eq_one_of_isPGroup_of_not_dvd_card
    {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (MulAut A)) {φ : MulAut A}
    (hφ : IsPGroup p (Subgroup.zpowers φ)) : φ = 1 := by
  by_contra hφne
  haveI : Fact p.Prime := ⟨hp⟩
  have hx : (⟨φ, Subgroup.mem_zpowers φ⟩ : Subgroup.zpowers φ) ≠ 1 := by
    intro hx1
    exact hφne (by simpa using congrArg Subtype.val hx1)
  have hpdvd : p ∣ orderOf (⟨φ, Subgroup.mem_zpowers φ⟩ : Subgroup.zpowers φ) :=
    hφ.dvd_orderOf hx
  rw [Subgroup.orderOf_mk] at hpdvd
  exact h (hpdvd.trans (orderOf_dvd_natCard φ))

end MulAut

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
