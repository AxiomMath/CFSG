module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.J4L4

variable {G : Type*} [Group G]

theorem centralizer_singleton_eq_of_mem_zpowers {p : ℕ} [hp : Fact p.Prime] {x y : G}
    (hx : orderOf x = p) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  have hord : orderOf y = p := by
    have h1 : orderOf y ∣ p := hx ▸ orderOf_dvd_of_mem_zpowers hy
    rcases (Nat.dvd_prime hp.out).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have : Finite (Subgroup.zpowers x) := by
    have : 0 < Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hx]
      exact hp.out.pos
    exact Nat.finite_of_card_ne_zero this.ne'
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord])
  have hxy : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  have key : ∀ a b : G, b ∈ Subgroup.zpowers a →
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a b hb z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact ((Commute.zpow_right (show Commute z a from hz) k).eq)
  exact le_antisymm (key y x hxy) (key x y hy)

theorem card_centralizer_conj (c y : G) :
    Nat.card (Subgroup.centralizer ({c * y * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨c⁻¹ * z * c, ?_⟩
      invFun := fun w => ⟨c * w * c⁻¹, ?_⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }
  · have := z.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    calc c⁻¹ * ↑z * c * y = c⁻¹ * (↑z * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * ↑z) * c := by rw [this]
      _ = y * (c⁻¹ * ↑z * c) := by group
  · have := w.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    calc c * ↑w * c⁻¹ * (c * y * c⁻¹) = c * (↑w * y) * c⁻¹ := by group
      _ = c * (y * ↑w) * c⁻¹ := by rw [this]
      _ = c * y * c⁻¹ * (c * ↑w * c⁻¹) := by group

theorem card_centralizer_eq_of_order_prime [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (h : (Nat.card G).factorization p = 1) {x g : G} (hx : orderOf x = p) (hg : orderOf g = p) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  let Sx : Sylow p G := Sylow.ofCard (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx, h, pow_one])
  let Sg : Sylow p G := Sylow.ofCard (Subgroup.zpowers g) (by rw [Nat.card_zpowers, hg, h, pow_one])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Sx Sg
  have hgS : g ∈ (Sg : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers g
  rw [← hc, Sylow.coe_subgroup_smul, Sylow.coe_ofCard,
    Subgroup.mem_smul_pointwise_iff_exists] at hgS
  obtain ⟨y, hy, hyg⟩ := hgS
  have hyg' : c * y * c⁻¹ = g := by
    rw [← hyg]
    simp only [MulAut.smul_def, MulAut.conj_apply]
  have hy1 : y ≠ 1 := by
    rintro rfl
    have : g = 1 := by rw [← hyg']; group
    rw [this, orderOf_one] at hg
    exact hp.out.ne_one hg.symm
  rw [← hyg', card_centralizer_conj, centralizer_singleton_eq_of_mem_zpowers hx hy hy1]

theorem card_centralizer_subgroup_dvd [Finite G] (C : Subgroup G) (g : ↥C) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set ↥C)) ∣
      Nat.card ↥(Subgroup.centralizer ({(g : G)} : Set G)) := by
  have hle : (Subgroup.centralizer ({g} : Set ↥C)).map C.subtype ≤
      Subgroup.centralizer ({(g : G)} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * g = g * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective C.subtype_injective] at h1

end CFSG.Quasithin.J4L4
