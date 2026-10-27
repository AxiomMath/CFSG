module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin

namespace S1421QA27

open Subgroup

variable {G Y : Type*} [Group G] [Group Y]

@[expose] def img (K : Subgroup G) (ψ : ↥K →* Y) (A : Subgroup G) : Subgroup Y :=
  (A.subgroupOf K).map ψ

variable {K : Subgroup G} {ψ : ↥K →* Y} {A B : Subgroup G}

theorem mem_img {y : Y} : y ∈ img K ψ A ↔ ∃ a : ↥K, (a : G) ∈ A ∧ ψ a = y := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_img (hψ : Function.Injective ψ) (hAK : A ≤ K) :
    Nat.card ↥(img K ψ A) = Nat.card ↥A := by
  rw [img, Subgroup.card_map_of_injective hψ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv

theorem img_mono (hAB : A ≤ B) : img K ψ A ≤ img K ψ B :=
  Subgroup.map_mono (fun _ ha => hAB ha)

theorem img_injective (hψ : Function.Injective ψ) (hAK : A ≤ K) (hBK : B ≤ K)
    (h : img K ψ A = img K ψ B) : A = B := by
  have h1 : A.subgroupOf K = B.subgroupOf K := Subgroup.map_injective hψ h
  have h2 := (Subgroup.subgroupOf_inj).mp h1
  rwa [inf_eq_left.mpr hAK, inf_eq_left.mpr hBK] at h2

theorem img_zpowers {z : G} (hz : z ∈ K) :
    img K ψ (zpowers z) = zpowers (ψ ⟨z, hz⟩) := by
  have h : (zpowers z).subgroupOf K = zpowers (⟨z, hz⟩ : ↥K) := by
    ext a
    simp only [Subgroup.mem_subgroupOf, mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  rw [img, h, MonoidHom.map_zpowers]

@[expose] def IrredModel (Y : Type*) [Group Y] (nK nQ : ℕ) : Prop :=
  ∀ (K Q W : Subgroup Y) (z : Y), orderOf z = 2 → Nat.card ↥K = nK → (∀ k ∈ K, k * z = z * k) →
    Q ≤ K → (∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) → Nat.card ↥Q = nQ → z ∈ W → W ≤ Q →
      (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) → W = zpowers z ∨ W = Q

theorem irred_of_embedding {nK nQ : ℕ} (hY : IrredModel Y nK nQ) (hψ : Function.Injective ψ)
    {Q W : Subgroup G} {z : G} (hz2 : orderOf z = 2) (hK : Nat.card ↥K = nK)
    (hKz : ∀ k ∈ K, k * z = z * k) (hQK : Q ≤ K) (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hQ : Nat.card ↥Q = nQ) (hzW : z ∈ W) (hWQ : W ≤ Q)
    (hW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) : W = zpowers z ∨ W = Q := by
  have hzK : z ∈ K := hQK (hWQ hzW)
  have hWK : W ≤ K := hWQ.trans hQK
  have hz' : orderOf (ψ ⟨z, hzK⟩) = 2 := by
    rw [orderOf_injective ψ hψ]
    exact (Subgroup.orderOf_coe (⟨z, hzK⟩ : ↥K)).symm.trans hz2
  have h := hY (img K ψ K) (img K ψ Q) (img K ψ W) (ψ ⟨z, hzK⟩) hz'
    (by rw [card_img hψ le_rfl]; exact hK)
    (by
      rintro _ hk
      obtain ⟨k, hk1, rfl⟩ := mem_img.mp hk
      show ψ k * ψ ⟨z, hzK⟩ = ψ ⟨z, hzK⟩ * ψ k
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hKz k hk1)))
    (img_mono hQK)
    (by
      intro k' hk' q' hq'
      obtain ⟨k, hk1, rfl⟩ := mem_img.mp hk'
      obtain ⟨q, hq1, rfl⟩ := mem_img.mp hq'
      refine mem_img.mpr ⟨k * q * k⁻¹, hQn k k.2 q hq1, by simp⟩)
    (by rw [card_img hψ hQK]; exact hQ)
    (mem_img.mpr ⟨⟨z, hzK⟩, hzW, rfl⟩)
    (img_mono hWQ)
    (by
      intro k' hk' w' hw'
      obtain ⟨k, hk1, rfl⟩ := mem_img.mp hk'
      obtain ⟨w, hw1, rfl⟩ := mem_img.mp hw'
      exact mem_img.mpr ⟨k * w * k⁻¹, hW k k.2 w hw1, by simp⟩)
  rcases h with h | h
  · left
    rw [← img_zpowers hzK] at h
    exact img_injective hψ hWK ((zpowers_le.mpr (hWQ hzW)).trans hQK) h
  · right
    exact img_injective hψ hWK hQK h

end S1421QA27

end CFSG.Quasithin
