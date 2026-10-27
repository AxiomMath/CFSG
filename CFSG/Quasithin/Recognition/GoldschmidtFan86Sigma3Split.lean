module

public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Dih

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup

theorem aux_eq {G : Type*} [Group G] {a a' b b' : G} (h : a * b = a' * b') :
    a'⁻¹ * a = b' * b⁻¹ := by
  calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
    _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
    _ = b' * b⁻¹ := by group

theorem commute_subtype {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (a : ↥A) (b : ↥B) :
    Commute (A.subtype a) (B.subtype b) := by
  show (a : G) * b = b * a
  exact hc a a.2 b b.2

noncomputable def mulProdHom {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : (↥A × ↥B) →* G :=
  MonoidHom.noncommCoprod A.subtype B.subtype (commute_subtype A B hc)

theorem mulProdHom_apply {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (a : A) (b : B) :
    mulProdHom A B hc (a, b) = (a : G) * b := by
  simp [mulProdHom]

theorem mulProdHom_bijective {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) (hs : A ⊔ B = ⊤) :
    Function.Bijective (mulProdHom A B hc) := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    rw [mulProdHom_apply, mulProdHom_apply] at h
    have h1 : (a'⁻¹ * a : G) = b' * b⁻¹ := aux_eq h
    have h2 : (a'⁻¹ * a : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h1 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hd, Subgroup.mem_bot] at h2
    have ha : a = a' := Subtype.ext (inv_mul_eq_one.1 h2).symm
    subst ha
    have hb : (b : G) = b' := by simpa using h
    exact Prod.ext rfl (Subtype.ext hb)
  · intro g
    have hAle : A ≤ (mulProdHom A B hc).range := fun a ha =>
      ⟨(⟨a, ha⟩, 1), by simp [mulProdHom_apply]⟩
    have hBle : B ≤ (mulProdHom A B hc).range := fun b hb =>
      ⟨(1, ⟨b, hb⟩), by simp [mulProdHom_apply]⟩
    have : g ∈ A ⊔ B := hs ▸ Subgroup.mem_top g
    exact (sup_le hAle hBle) this

noncomputable def prodEquivOfSplit {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) (hs : A ⊔ B = ⊤) :
    (↥A × ↥B) ≃* G :=
  MulEquiv.ofBijective (mulProdHom A B hc) (mulProdHom_bijective A B hc hd hs)

theorem prodEquivOfSplit_apply {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) (hs : A ⊔ B = ⊤) (a : A) (b : B) :
    prodEquivOfSplit A B hc hd hs (a, b) = (a : G) * b :=
  mulProdHom_apply A B hc a b

theorem finset_cases : ∀ F : Finset (DihedralGroup 4), F.card = 4 → (∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) →
    (∀ x ∈ F, x * x = 1) →
    F = {r 0, r 2, sr 0, sr 2} ∨ F = {r 0, r 2, sr 1, sr 3} := by
  decide +kernel

theorem kleinFour_cases (K : Subgroup (DihedralGroup 4)) (hK : IsKleinFour ↥K) :
    K = kleinA ∨ K = kleinB := by
  classical
  let F : Finset (DihedralGroup 4) := Finset.univ.filter (· ∈ K)
  have hF : F.card = 4 := by
    have h1 : Nat.card K = F.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← h1]; exact hK.card_four
  have hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F := by
    intro x hx y hy
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
    exact K.mul_mem hx hy
  have hsq : ∀ x ∈ F, x * x = 1 := by
    intro x hx
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := hK.mul_self (⟨x, hx⟩ : K)
    exact congrArg Subtype.val this
  rcases finset_cases F hF hmul hsq with h | h
  · left
    ext x
    have hx : x ∈ F ↔ x ∈ ({r 0, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)) := by rw [h]
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hx, mem_kleinA]
    simp [inA]
  · right
    ext x
    have hx : x ∈ F ↔ x ∈ ({r 0, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)) := by rw [h]
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hx, mem_kleinB]
    simp [inB]

end CFSG.Quasithin.Fan86.Sigma3
