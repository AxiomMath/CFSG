module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC
public import CFSG.Quasithin.Vol2.Ch10SecEE3Setup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise

section General

variable {W : Type*} [CommGroup W] [Finite W] {W₁ W₂ : Subgroup W} {P₁ P₂ : Subgroup (MulAut W)}

theorem ProdSetting.exists_mem_of_good (h : ProdSetting W₁ W₂ P₁ P₂)
    (hb₁ : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) ≤ Nat.card W₁)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {𝒜 : Set (Subgroup (MulAut W))}
    (h𝒜 : ∀ X ∈ 𝒜, X ≤ P₁ ⊔ P₂ ∧
      Nat.card X * Nat.card ↥(fixV X ⊓ (W₁ ⊔ W₂)) = Nat.card ↥(W₁ ⊔ W₂))
    (hP₁ : P₁ ≤ ⨆ X ∈ 𝒜, X) {p r : MulAut W} (hp : p ∈ P₁) (hr : r ∈ P₁)
    (hgood : ∀ Y ≤ P₁, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₁) = Nat.card W₁ → p * r ∈ Y → p ∈ Y)
    (hall : ∀ g ∈ P₁, g = 1 ∨ g = p ∨ g = r ∨ g = p * r) (hp1 : p ≠ 1) (hpr : p ≠ r)
    (hrr : r * r = 1) : ∃ X ∈ 𝒜, p ∈ X := by
  by_contra hcon
  push Not at hcon
  have hX : ∀ X ∈ 𝒜, X ≤ Subgroup.zpowers r ⊔ P₂ := by
    intro X hX𝒜
    obtain ⟨hXP, heq⟩ := h𝒜 X hX𝒜
    obtain ⟨hle, hg⟩ := h.projOne_le_of_eq hb₁ hb₂ hXP heq
    have hle1 : h.projOne X ≤ P₁ := h.symm.projTwo_le X
    have hsub : ∀ a ∈ h.projOne X, a = 1 ∨ a = r := by
      intro a ha
      have hpa : p ∉ h.projOne X := fun hp' => hcon X hX𝒜 (hle hp')
      rcases hall a (hle1 ha) with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd ha hpa
      · exact Or.inr rfl
      · exact absurd (hgood _ hle1 hg ha) hpa
    intro x hx
    have hX' : X ≤ P₂ ⊔ P₁ := sup_comm P₁ P₂ ▸ hXP
    obtain ⟨b, hb, hxb⟩ := h.symm.exists_eq_mul ⟨x, hX' hx⟩
    have hxb' : x = b * (h.symm.projHom ⟨x, hX' hx⟩ : MulAut W) := hxb
    have ha : (h.symm.projHom ⟨x, hX' hx⟩ : MulAut W) ∈ h.projOne X :=
      (h.symm.mem_projTwo_iff hX').mpr ⟨(h.symm.projHom ⟨x, hX' hx⟩).2, b, hb, hxb' ▸ hx⟩
    rw [hxb']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left ?_)
    rcases hsub _ ha with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers r
  have hpS : p ∈ Subgroup.zpowers r ⊔ P₂ := iSup₂_le hX (hP₁ hp)
  have hc : ∀ a ∈ Subgroup.zpowers r, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    h.comm a ((Subgroup.zpowers_le.mpr hr) ha) b hb
  obtain ⟨c, hc', d, hd, hcd⟩ := exists_mul_of_mem_sup hc hpS
  have hcP : c ∈ P₁ := (Subgroup.zpowers_le.mpr hr) hc'
  have h1 := eq_of_mul_eq_mul h.inf_P hp hcP P₂.one_mem hd (by rw [mul_one]; exact hcd)
  rcases eq_one_or_eq_of_mem_zpowers hrr hc' with h2 | h2
  · exact hp1 (h1.1.trans h2)
  · exact hpr (h1.1.trans h2)

end General

theorem isElemAbelian_sup_of_commute' {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

theorem sA_mul_sB_comm : sB * sA = sA * sB := by decide

theorem sA_ne_one : sA ≠ 1 := by decide

theorem sB_ne_one : sB ≠ 1 := by decide

theorem sA_ne_sB : sA ≠ sB := by decide

theorem sA_mul_self : sA * sA = 1 := by decide

theorem sB_mul_self : sB * sB = 1 := by decide

section Side

variable {W : Type*} [CommGroup W] [Finite W] {W₂ : Subgroup W} {K P₂ : Subgroup (MulAut W)}
  {θ : ↥K ≃* Equiv.Perm (Fin 5)} {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem exists_mem_of_side {P : Subgroup (MulAut W)} (h : ProdSetting (commV K) W₂ P P₂)
    (hβ : A5Equivariant θ β) (hPK : P ≤ K) (hmem : ∀ g (hg : g ∈ K), g ∈ P ↔ θ ⟨g, hg⟩ ∈ eFour)
    (hb₂ : ∀ Y ≤ P₂, Nat.card Y * Nat.card ↥(fixV Y ⊓ W₂) ≤ Nat.card W₂)
    {𝒜 : Set (Subgroup (MulAut W))}
    (h𝒜 : ∀ X ∈ 𝒜, X ≤ P ⊔ P₂ ∧
      Nat.card X * Nat.card ↥(fixV X ⊓ (commV K ⊔ W₂)) = Nat.card ↥(commV K ⊔ W₂))
    (hP : P ≤ ⨆ X ∈ 𝒜, X) {σ : Equiv.Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB) :
    ∃ X ∈ 𝒜, ((θ.symm σ : ↥K) : MulAut W) ∈ X := by
  have hc16 : Nat.card ↥(commV K) = 16 := card_commV_of_isA5Module β
  have hb₁ : ∀ Y ≤ P, Nat.card Y * Nat.card ↥(fixV Y ⊓ commV K) ≤ Nat.card ↥(commV K) :=
    fun Y hY => hc16 ▸ (factor_bound hβ hPK hmem hY).1
  have hgood' : ∀ Y ≤ P, Nat.card Y * Nat.card ↥(fixV Y ⊓ commV K) = Nat.card ↥(commV K) →
      ((θ.symm (sA * sB) : ↥K) : MulAut W) ∈ Y → ((θ.symm sA : ↥K) : MulAut W) ∈ Y ∧
        ((θ.symm sB : ↥K) : MulAut W) ∈ Y := by
    intro Y hY heq hq
    have hA := ((factor_bound hβ hPK hmem hY).2.mp (hc16 ▸ heq)) hq
    refine ⟨hA, ?_⟩
    have e : ((θ.symm sB : ↥K) : MulAut W) =
        ((θ.symm sA : ↥K) : MulAut W)⁻¹ * ((θ.symm (sA * sB) : ↥K) : MulAut W) := by
      rw [map_mul, Subgroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact Y.mul_mem (Y.inv_mem hA) hq
  have hmemP : ∀ τ ∈ eFour, ((θ.symm τ : ↥K) : MulAut W) ∈ P := fun τ hτ =>
    (hmem _ (θ.symm τ).2).mpr (by rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]; exact hτ)
  have hinj : ∀ τ τ' : Equiv.Perm (Fin 5), ((θ.symm τ : ↥K) : MulAut W) =
      ((θ.symm τ' : ↥K) : MulAut W) → τ = τ' := fun τ τ' e =>
    θ.symm.injective (Subtype.ext e)
  have hall : ∀ g ∈ P, g = 1 ∨ g = ((θ.symm sA : ↥K) : MulAut W) ∨
      g = ((θ.symm sB : ↥K) : MulAut W) ∨ g = ((θ.symm (sA * sB) : ↥K) : MulAut W) := by
    intro g hg
    have hgK := hPK hg
    have hθ := (hmem g hgK).mp hg
    have e : g = ((θ.symm (θ ⟨g, hgK⟩) : ↥K) : MulAut W) := by rw [MulEquiv.symm_apply_apply]
    rcases (eFour_mem_iff _).mp hθ with h1 | h1 | h1 | h1 <;> rw [e, h1]
    · left; rw [map_one]; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  have hprod : ∀ τ τ' : Equiv.Perm (Fin 5), ((θ.symm τ : ↥K) : MulAut W) *
      ((θ.symm τ' : ↥K) : MulAut W) = ((θ.symm (τ * τ') : ↥K) : MulAut W) := by
    intro τ τ'; rw [map_mul]; rfl
  rcases hσ with rfl | rfl
  · refine h.exists_mem_of_good hb₁ hb₂ h𝒜 hP (r := ((θ.symm sB : ↥K) : MulAut W))
      (hmemP _ (by decide)) (hmemP _ (by decide)) (fun Y hY heq hq => (hgood' Y hY heq
        (by rwa [hprod] at hq)).1) (fun g hg => ?_) (fun e => sA_ne_one (hinj _ 1 (by
          rw [e, map_one]; rfl))) (fun e => sA_ne_sB (hinj _ _ e)) (by
          rw [hprod, sB_mul_self, map_one]; rfl)
    rw [hprod]
    exact hall g hg
  · refine h.exists_mem_of_good hb₁ hb₂ h𝒜 hP (r := ((θ.symm sA : ↥K) : MulAut W))
      (hmemP _ (by decide)) (hmemP _ (by decide)) (fun Y hY heq hq => (hgood' Y hY heq
        (by rwa [hprod, sA_mul_sB_comm] at hq)).2) (fun g hg => ?_) (fun e => sB_ne_one
          (hinj _ 1 (by rw [e, map_one]; rfl))) (fun e => sA_ne_sB (hinj _ _ e).symm) (by
          rw [hprod, sA_mul_self, map_one]; rfl)
    rw [hprod, sA_mul_sB_comm]
    rcases hall g hg with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr h1))

end Side

end CFSG.Quasithin.Vol2.Ch10.SecE
