module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Lemma2

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section Common

variable {K : Type*} [Group K] [Finite K]

theorem row6_exists_E9 {e x : K} (he3 : orderOf e = 3) (hx3 : orderOf x = 3)
    (hex : e * x = x * e) (hxe : x ∉ Subgroup.zpowers e) :
    IsElemAbelian 3 (Subgroup.zpowers e ⊔ Subgroup.zpowers x) ∧
      Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers x) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE1, hc⟩ := isElemAbelian_zpowers_order_three he3
  obtain ⟨hE2, hE2c⟩ := exists_elemAbelian_sup_zpowers hE1 hx3 (fun u hu => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (show Commute e x from hex).zpow_left k) hxe
  exact ⟨hE2, by rw [hE2c, hc]⟩

omit [Finite K] in
theorem row6_not_mem_zpowers_of_central {N Lb : Subgroup K} (hLb : Lb ≤ N)
    (hLbZ : ∀ z ∈ Lb, (∀ a ∈ Lb, z * a = a * z) → z = 1) {e w : K} (he : e ∈ Lb) (he1 : e ≠ 1)
    (hw : ∀ a ∈ N, w * a = a * w) : e ∉ Subgroup.zpowers w := by
  intro h
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  refine he1 (hLbZ _ he fun a ha => ?_)
  exact ((show Commute w a from hw a (hLb ha)).zpow_left k).eq

end Common

end Stellmacher.L3YC

end CFSG.Quasithin
