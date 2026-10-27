module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

theorem card_quotCenter_dvd_of_le {G : Type*} [Group G] [Finite G] {J X : Subgroup G}
    (h : J ≤ X) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  let f : ↥J →* ↥X ⧸ Subgroup.center ↥X :=
    (QuotientGroup.mk' (Subgroup.center ↥X)).comp (Subgroup.inclusion h)
  have hker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hx1 : QuotientGroup.mk' (Subgroup.center ↥X) (Subgroup.inclusion h x) = 1 :=
      MonoidHom.mem_ker.mp hx
    have hxZ : Subgroup.inclusion h x ∈ Subgroup.center ↥X := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      exact hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * (x : G) = (x : G) * (y : G)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, h y.2⟩)
  have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥J ⧸ f.ker) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le hker
  have h2 : Nat.card (↥J ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    Subgroup.card_subgroup_dvd_card f.range
  rw [h2] at h1
  exact h1.trans h3

end CFSG.GroupTheory

end
