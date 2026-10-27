module

public import CFSG.RankThree.GF2n.Tim79aSec25

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem isPGroup_sup_wOf_of_commutator_mem {h : G} (hh : h ∈ H)
    (hW : ∀ y ∈ V, ∀ u ∈ conjSubgroup h V, ⁅y, u⁆ ∈ wOf V H) :
    IsPGroup 2 ↥(V ⊔ conjSubgroup h V ⊔ wOf V H) := by
  have hVH : V ≤ H := hc.V_le_H
  have hUH : conjSubgroup h V ≤ H := conjSubgroup_le_of_le_of_mem hVH hh
  have hW2 : IsPGroup 2 ↥(wOf V H) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  have hU2 : IsPGroup 2 ↥(conjSubgroup h V) := hc.isPGroup_V.of_equiv
    (V.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective)
  have hK2 : IsPGroup 2 ↥(V ⊔ wOf V H) := IsPGroup.to_sup_of_normal_right' hc.isPGroup_V hW2
    (fun y hy => H_le_normalizer_wOf V H (hVH hy))
  have hconj : ∀ u ∈ conjSubgroup h V, conjSubgroup u (V ⊔ wOf V H) ≤ V ⊔ wOf V H := by
    intro u hu
    unfold conjSubgroup
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 : ⁅u, y⁆ ∈ wOf V H := by
        rw [← commutatorElement_inv]
        exact (wOf V H).inv_mem (hW y hy u hu)
      have e : (MulAut.conj u).toMonoidHom y = ⁅u, y⁆ * y := by
        show u * y * u⁻¹ = ⁅u, y⁆ * y
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
    · rintro _ ⟨w, hw, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hUH hu)) w).mp hw
      exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using this)
  have hnorm : conjSubgroup h V ≤ Subgroup.normalizer ((V ⊔ wOf V H : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨fun hn => mem_of_conjSubgroup_le (hconj u hu) hn, fun hn => by
      simpa [mul_assoc] using mem_of_conjSubgroup_le (hconj u⁻¹ ((conjSubgroup h V).inv_mem hu)) hn⟩
  rw [sup_right_comm]
  exact IsPGroup.to_sup_of_normal_left' hK2 hU2 hnorm

theorem commute_conj_of_commutator_mem_wOf {g₁ g₂ : G} (hg₁ : g₁ ∈ H) (hg₂ : g₂ ∈ H)
    (hW : ∀ y ∈ conjSubgroup g₁ V, ∀ u ∈ conjSubgroup g₂ V, ⁅y, u⁆ ∈ wOf V H) :
    ∀ y ∈ conjSubgroup g₁ V, ∀ u ∈ conjSubgroup g₂ V, y * u = u * y := by
  intro y hy u hu
  have hkH : g₁⁻¹ * g₂ ∈ H := H.mul_mem (H.inv_mem hg₁) hg₂
  have hy' : g₁⁻¹ * y * g₁ ∈ V := mem_conjSubgroup.mp hy
  have hu' : g₁⁻¹ * u * g₁ ∈ conjSubgroup (g₁⁻¹ * g₂) V := by
    rw [mem_conjSubgroup]
    have := mem_conjSubgroup.mp hu
    rwa [show (g₁⁻¹ * g₂)⁻¹ * (g₁⁻¹ * u * g₁) * (g₁⁻¹ * g₂) = g₂⁻¹ * u * g₂ by group]
  have hW' : ∀ y ∈ V, ∀ u ∈ conjSubgroup (g₁⁻¹ * g₂) V, ⁅y, u⁆ ∈ wOf V H := by
    intro y₀ hy₀ u₀ hu₀
    have h1 : g₁ * y₀ * g₁⁻¹ ∈ conjSubgroup g₁ V := by
      rw [mem_conjSubgroup]
      rwa [show g₁⁻¹ * (g₁ * y₀ * g₁⁻¹) * g₁ = y₀ by group]
    have h2 : g₁ * u₀ * g₁⁻¹ ∈ conjSubgroup g₂ V := by
      rw [mem_conjSubgroup]
      have := mem_conjSubgroup.mp hu₀
      rwa [show g₂⁻¹ * (g₁ * u₀ * g₁⁻¹) * g₂ = (g₁⁻¹ * g₂)⁻¹ * u₀ * (g₁⁻¹ * g₂) by group]
    have h4 := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem hg₁)) _).mp
      (hW _ h1 _ h2)
    have e : g₁⁻¹ * ⁅g₁ * y₀ * g₁⁻¹, g₁ * u₀ * g₁⁻¹⁆ * g₁⁻¹⁻¹ = ⁅y₀, u₀⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h4
  have hcomm := hc.commute_of_isPGroup_sup_wOf hkH
    (hc.isPGroup_sup_wOf_of_commutator_mem hkH hW') _ hy' _ hu'
  calc y * u = g₁ * ((g₁⁻¹ * y * g₁) * (g₁⁻¹ * u * g₁)) * g₁⁻¹ := by group
    _ = g₁ * ((g₁⁻¹ * u * g₁) * (g₁⁻¹ * y * g₁)) * g₁⁻¹ := by rw [hcomm]
    _ = u * y := by group

theorem card_le_of_centralizes {U F : Subgroup G} (hFW : F ≤ wOf V H)
    (hFU : ∀ x ∈ F, ∀ y ∈ U, x * y = y * x) {r : G} (hr : r ∈ xOf V H) {a : G}
    (ha : a ∈ conjSubgroup r V) (hgen : xOf V H ≤ U ⊔ Subgroup.zpowers a) :
    Nat.card F ≤ Nat.card (V ⊓ wOf V H : Subgroup G) := by
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  have hrH : r ∈ H := hXH hr
  have haH : a ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hrH ha
  have hCF : ∀ x ∈ F, a * x = x * a → x = 1 := by
    intro x hx hax
    have hle : U ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun y hy => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hFU x hx y hy).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hax
    have hxX : x ∈ Subgroup.centralizer (xOf V H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen hy))
    have : x ∈ wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) := ⟨hFW hx, hxX⟩
    rw [hc.wOf_inf_centralizer_xOf_eq_bot, Subgroup.mem_bot] at this
    exact this
  have hψ : ∀ x ∈ F, ⁅x, a⁆ ∈ conjSubgroup r V ⊓ wOf V H := by
    intro x hx
    have hxW := hFW hx
    have hxN : x ∈ Subgroup.normalizer (conjSubgroup r V : Set G) :=
      hc.pCoreH_le_normalizer_conj hrH (wOf_le_pCore V H hxW)
    refine ⟨?_, ?_⟩
    · have h1 : x * a * x⁻¹ ∈ conjSubgroup r V := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
      have e : ⁅x, a⁆ = x * a * x⁻¹ * a⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact (conjSubgroup r V).mul_mem h1 ((conjSubgroup r V).inv_mem ha)
    · have h2 : a * x⁻¹ * a⁻¹ ∈ wOf V H := (Subgroup.mem_normalizer_iff.mp
        (H_le_normalizer_wOf V H haH) x⁻¹).mp ((wOf V H).inv_mem hxW)
      have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (wOf V H).mul_mem hxW h2
  have hcardle : Nat.card F ≤ Nat.card (conjSubgroup r V ⊓ wOf V H : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun x : F => (⟨⁅(x : G), a⁆, hψ x x.2⟩ : ↥(conjSubgroup r V ⊓ wOf V H))) ?_
    intro x x' hxx
    have h1 : ⁅(x : G), a⁆ = ⁅(x' : G), a⁆ := congrArg Subtype.val hxx
    have h2 : (x : G) * a * (x : G)⁻¹ = (x' : G) * a * (x' : G)⁻¹ := by
      simp only [commutatorElement_def] at h1
      exact mul_right_cancel h1
    have h3 : a * ((x' : G)⁻¹ * x) = ((x' : G)⁻¹ * x) * a := by
      calc a * ((x' : G)⁻¹ * x) = (x' : G)⁻¹ * ((x' : G) * a * (x' : G)⁻¹) * x := by group
        _ = (x' : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * x := by rw [h2]
        _ = ((x' : G)⁻¹ * x) * a := by group
    have h4 := hCF _ (F.mul_mem (F.inv_mem x'.2) x.2) h3
    exact Subtype.ext (inv_mul_eq_one.mp h4).symm
  have hcardA : Nat.card (conjSubgroup r V ⊓ wOf V H : Subgroup G) =
      Nat.card (V ⊓ wOf V H : Subgroup G) := by
    have e : conjSubgroup r V ⊓ wOf V H = conjSubgroup r (V ⊓ wOf V H) := by
      rw [conjSubgroup_inf, mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hrH)]
    rw [e, card_conjSubgroup]
  exact hcardle.trans hcardA.le

theorem eq_inf_wOf_of_centralizes {U F : Subgroup G} (hFW : F ≤ wOf V H)
    (hFU : ∀ x ∈ F, ∀ y ∈ U, x * y = y * x) (hVF : V ⊓ wOf V H ≤ F) {r : G}
    (hr : r ∈ xOf V H) {a : G} (ha : a ∈ conjSubgroup r V)
    (hgen : xOf V H ≤ U ⊔ Subgroup.zpowers a) : V ⊓ wOf V H = F :=
  Subgroup.eq_of_le_of_card_ge hVF (hc.card_le_of_centralizes hFW hFU hr ha hgen)

end MinCex

end CFSG.RankThree.GF2n.Tim79a
