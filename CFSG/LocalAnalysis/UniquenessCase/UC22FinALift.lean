module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open Subgroup

variable {Γ : Type} [Group Γ]

theorem map_sup_zpowers (N : Subgroup Γ) [N.Normal] (y₁ : Γ) :
    (N ⊔ zpowers y₁).map (QuotientGroup.mk' N) = zpowers (QuotientGroup.mk' N y₁) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    (Subgroup.map_eq_bot_iff _).2 (le_of_eq (QuotientGroup.ker_mk' N).symm), bot_sup_eq]

theorem commute_mk_of_mem {N : Subgroup Γ} [N.Normal] {x y : Γ} (h : x * y * x⁻¹ * y⁻¹ ∈ N) :
    Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker] at h
  simp only [map_mul, map_inv] at h
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := QuotientGroup.mk' N x)
    (g₂ := QuotientGroup.mk' N y)).1 (by simpa [commutatorElement_def] using h)

theorem mem_of_commute_mk {N : Subgroup Γ} [N.Normal] {x y : Γ}
    (h : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [h.eq]
  simp

theorem mk_mem_zpowers {N : Subgroup Γ} [N.Normal] {y₁ x : Γ} (hx : x ∈ N ⊔ zpowers y₁) :
    QuotientGroup.mk' N x ∈ zpowers (QuotientGroup.mk' N y₁) := by
  rw [← map_sup_zpowers]
  exact Subgroup.mem_map_of_mem _ hx

theorem commutator_mem_of_mem_sup {N : Subgroup Γ} [N.Normal] {y₁ x y : Γ}
    (hx : x ∈ N ⊔ zpowers y₁) (hy : y ∈ N ⊔ zpowers y₁) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (mk_mem_zpowers hx)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (mk_mem_zpowers hy)
  apply mem_of_commute_mk
  rw [← hi, ← hj]
  exact Commute.zpow_zpow_self _ _ _

theorem commutator_mem_of_mem_sup_of_commute {N : Subgroup Γ} [N.Normal] {y₁ x b : Γ}
    (hx : x ∈ N ⊔ zpowers y₁) (hb : y₁ * b * y₁⁻¹ * b⁻¹ ∈ N) : x * b * x⁻¹ * b⁻¹ ∈ N := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (mk_mem_zpowers hx)
  apply mem_of_commute_mk
  rw [← hi]
  exact (commute_mk_of_mem hb).zpow_left i

theorem le_normalizer_sup_zpowers {N : Subgroup Γ} [N.Normal] {y₁ : Γ} {B : Subgroup Γ}
    (hB : ∀ b ∈ B, y₁ * b * y₁⁻¹ * b⁻¹ ∈ N) :
    B ≤ normalizer (↑(N ⊔ zpowers y₁) : Set Γ) := by
  have key : ∀ b ∈ B, ∀ x ∈ N ⊔ zpowers y₁, b * x * b⁻¹ ∈ N ⊔ zpowers y₁ := by
    intro b hb x hx
    have h := commutator_mem_of_mem_sup_of_commute hx (hB b hb)
    have h' : b * x * b⁻¹ = (x * b * x⁻¹ * b⁻¹)⁻¹ * x := by group
    rw [h']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left h)) hx
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key b hb x hx, fun hx => ?_⟩
  have := key b⁻¹ (B.inv_mem hb) _ hx
  simpa [mul_assoc] using this

theorem relIndex_sup_zpowers (N : Subgroup Γ) [N.Normal] (y₁ : Γ) :
    N.relIndex (N ⊔ zpowers y₁) = orderOf (QuotientGroup.mk' N y₁) := by
  let f : ↥(N ⊔ zpowers y₁) →* Γ ⧸ N := (QuotientGroup.mk' N).comp (N ⊔ zpowers y₁).subtype
  have hker : f.ker = N.subgroupOf (N ⊔ zpowers y₁) := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = zpowers (QuotientGroup.mk' N y₁) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_sup_zpowers]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Nat.card_zpowers]

theorem isCyclic_card_of_complement {N : Subgroup Γ} [N.Normal] {y₁ : Γ} {C : Subgroup Γ}
    (hNC : N ⊓ C = ⊥) (hsup : N ⊔ C = N ⊔ zpowers y₁) :
    IsCyclic C ∧ Nat.card C = orderOf (QuotientGroup.mk' N y₁) := by
  let g : ↥C →* Γ ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : Γ) ∈ N := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : Γ) ∈ N ⊓ C := ⟨hxN, x.2⟩
    rw [hNC, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : g.range = zpowers (QuotientGroup.mk' N y₁) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (le_of_eq (QuotientGroup.ker_mk' N).symm),
      bot_sup_eq, map_sup_zpowers] at h
    exact h
  have : IsCyclic g.range := by rw [hrange]; infer_instance
  let e : ↥C ≃* ↥g.range := MonoidHom.ofInjective hinj
  refine ⟨isCyclic_of_injective e.toMonoidHom e.injective, ?_⟩
  rw [Nat.card_congr e.toEquiv, hrange, Nat.card_zpowers]

variable {Q : Type} [Group Q]

theorem orderOf_mk_eq_orderOf_image (φ : Γ →* Q) {N Y : Subgroup Γ} [N.Normal]
    (hN2 : IsPGroup 2 N) (hker : ∀ y ∈ Y, φ y = 1 → y ∈ N) {y₁ : Γ} (hy₁ : y₁ ∈ Y)
    (hodd : Odd (orderOf (φ y₁))) :
    orderOf (QuotientGroup.mk' N y₁) = orderOf (φ y₁) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hker _ (Y.pow_mem hy₁ _) (by rw [map_pow, pow_orderOf_eq_one])
  · set u := orderOf (QuotientGroup.mk' N y₁) with hu
    have h1 : y₁ ^ u ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_pow, hu, pow_orderOf_eq_one]
    have h2 : IsPGroup 2 (N.map φ) := hN2.map φ
    let z : ↥(N.map φ) := ⟨φ (y₁ ^ u), Subgroup.mem_map_of_mem φ h1⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 h2 z
    have hk' : orderOf (φ y₁ ^ u) = 2 ^ k := by
      rw [← map_pow]
      exact (Subgroup.orderOf_coe z).trans hk
    have hdvd : orderOf (φ y₁ ^ u) ∣ orderOf (φ y₁) := orderOf_pow_dvd u
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk'] at hdvd
      have : Even (orderOf (φ y₁)) :=
        even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 (Nat.even_pow.2 ⟨even_two, hk0⟩)) hdvd)
      exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    exact orderOf_dvd_of_pow_eq_one hk'

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
