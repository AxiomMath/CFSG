module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Cube
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2Plane
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3_elem3 {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime) {Y J₀ J₁ : Subgroup N}
    (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N) (h₀ : CFSG.IsComponent J₀)
    (h₁ : CFSG.IsComponent J₁) (hne : J₀ ≠ J₁) (hm₀ : ¬ p ∣ Nat.card (Subgroup.center J₀))
    (hm₁ : ¬ p ∣ Nat.card (Subgroup.center J₁)) {w₀ w₁ : N} (hw₀ : w₀ ∈ J₀) (hw₁ : w₁ ∈ J₁)
    (ho₀ : orderOf w₀ = p) (ho₁ : orderOf w₁ = p) :
    ∃ F : Subgroup N, CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ 3 ∧
      F = Y ⊔ Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ J₀, ∀ y ∈ J₁, x * y = y * x := by
    intro x hx y hy
    rcases CFSG.LocalCores.distinct_components_commute h₀ h₁ with he | hb
    · exact absurd he hne
    · have hxy : ⁅x, y⁆ ∈ ⁅J₀, J₁⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [hb, Subgroup.mem_bot] at hxy
      exact commutatorElement_eq_one_iff_mul_comm.1 hxy
  have hcen : ∀ J : Subgroup N, ¬ p ∣ Nat.card (Subgroup.center J) →
      ∀ x ∈ J, (∀ j ∈ J, x * j = j * x) → x ^ p = 1 → x = 1 := by
    intro J hJ x hxJ hxc hxp
    by_contra hx1
    have hord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hmem : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g.1 g.2).symm
    have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hmem
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact hJ hdvd
  have hzp : ∀ w : N, orderOf w = p → ∀ x ∈ Subgroup.zpowers w, x ^ p = 1 := by
    intro w hw x hx
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers w) hx
    rw [Nat.card_zpowers, hw] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hW0 : Subgroup.zpowers w₀ ≤ J₀ := Subgroup.zpowers_le.2 hw₀
  have hW1 : Subgroup.zpowers w₁ ≤ J₁ := Subgroup.zpowers_le.2 hw₁
  have hzinf : Subgroup.zpowers w₀ ⊓ Subgroup.zpowers w₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.1 hx
    exact hcen J₀ hm₀ x (hW0 hx0) (fun j hj => (hcomm j hj x (hW1 hx1)).symm) (hzp w₁ ho₁ x hx1)
  have hc01 : ∀ h ∈ Subgroup.zpowers w₀, ∀ k ∈ Subgroup.zpowers w₁, h * k = k * h :=
    fun h hh k hk => hcomm h (hW0 hh) k (hW1 hk)
  have hcardW : Nat.card (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁ : Subgroup N) = p ^ 2 := by
    rw [r4d_card_sup hc01 hzinf, Nat.card_zpowers, Nat.card_zpowers, ho₀, ho₁, pow_two]
  have hE0 : CFSG.Open.IsElemAbelian p (Subgroup.zpowers w₀) := ⟨inferInstance, hzp w₀ ho₀⟩
  have hE1 : CFSG.Open.IsElemAbelian p (Subgroup.zpowers w₁) := ⟨inferInstance, hzp w₁ ho₁⟩
  have hWel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE0 hE1 hc01
  have hYcomm : ∀ y ∈ Y, ∀ g ∈ Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁, y * g = g * y :=
    fun y hy g _ => ((Subgroup.mem_center_iff.1 (hYc hy)) g).symm
  have hYel : CFSG.Open.IsElemAbelian p Y := by
    refine ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hYc a.2)) b.1).symm⟩⟩, ?_⟩
    intro x hx
    have h1 := Subgroup.orderOf_dvd_natCard Y hx
    rw [hY] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hYW : Y ⊓ (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgY, hgW⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨h, hh, k, hk, hhk⟩ := r2a_mem_sup hc01 hgW
    have hgc : ∀ j : N, j * g = g * j := Subgroup.mem_center_iff.1 (hYc hgY)
    have hjh : ∀ j ∈ J₀, j * h = h * j := by
      intro j hj
      have hjk : j * k = k * j := hcomm j hj k (hW1 hk)
      have key : j * h * k = h * j * k := by
        calc j * h * k = j * (h * k) := mul_assoc _ _ _
          _ = j * g := by rw [hhk]
          _ = g * j := hgc j
          _ = h * k * j := by rw [hhk]
          _ = h * (k * j) := mul_assoc _ _ _
          _ = h * (j * k) := by rw [hjk]
          _ = h * j * k := (mul_assoc _ _ _).symm
      exact mul_right_cancel key
    have hhJ : h = 1 := hcen J₀ hm₀ h (hW0 hh) (fun j hj => (hjh j hj).symm) (hzp w₀ ho₀ h hh)
    have hgk : g = k := by rw [← hhk, hhJ, one_mul]
    have hgz : g ∈ Subgroup.zpowers w₁ := by rw [hgk]; exact hk
    exact hcen J₁ hm₁ g (hW1 hgz) (fun j _ => (hgc j).symm) (hzp w₁ ho₁ g hgz)
  have hcardF : Nat.card (Y ⊔ (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁) : Subgroup N) =
      p * p ^ 2 := by
    rw [r4d_card_sup hYcomm hYW, hY, hcardW]
  have hFel : CFSG.Open.IsElemAbelian p (Y ⊔ (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hYel hWel hYcomm
  refine ⟨Y ⊔ (Subgroup.zpowers w₀ ⊔ Subgroup.zpowers w₁), hFel, ?_, (sup_assoc _ _ _).symm⟩
  rw [hcardF]
  ring

end CFSG.RankThree.PartTwo.Sec13.F135Last
