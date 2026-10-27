module

public import CFSG.Quasithin.H13.L32ASk4
public import CFSG.Quasithin.H13.L32AC50d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace Alt7

theorem a_sub_s : (∀ a ∈ raAList, a ∈ raSList) ∧ (∀ a ∈ rbAList, a ∈ rbSList) ∧
    ∀ a ∈ rcAList, a ∈ rcSList := by
  have h : raAList.all (fun a => decide (a ∈ raSList)) = true ∧
      rbAList.all (fun a => decide (a ∈ rbSList)) = true ∧
      rcAList.all (fun a => decide (a ∈ rcSList)) = true := by
    decide +kernel
  exact ⟨of_all h.1, of_all h.2.1, of_all h.2.2⟩

end Alt7

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem relIndex_eq_three_of_card {A B : Subgroup (Equiv.Perm (Fin 7))} (hAB : A ≤ B)
    (h : Nat.card B = 3 * Nat.card A) : A.relIndex B = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr hAB, h] at h1
  have hA : 0 < Nat.card A := Nat.card_pos
  have : A.relIndex B * Nat.card A = 3 * Nat.card A := h1
  exact Nat.eq_of_mul_eq_mul_right hA this

theorem not_le_normalizer_of {A B : Subgroup (Equiv.Perm (Fin 7))}
    (h : ∃ r ∈ B, ∃ t ∈ A, r * t * r⁻¹ ∉ A) :
    ¬ B ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 7))) := by
  intro hle
  obtain ⟨r, hr, t, ht, hrt⟩ := h
  exact hrt ((Subgroup.mem_normalizer_iff.mp (hle hr) t).mp ht)

section Six

variable (S : Setting147 G T L V H) {π : ↥H →* Equiv.Perm (Fin 7)}
  (hker : π.ker = CFSG.Open.pCore 2 ↥H)
  {I : Subgroup G} (hV1I : fsuV1 T V ≤ I) (hIU : I < conjClosure V H)
  (hIn : H ≤ Subgroup.normalizer (I : Set G))
  {β : ↥(conjClosure V H) →* ↥(G6.coreMod 7)} (hβker : β.ker = I.subgroupOf (conjClosure V H))
  (hβ : ∀ (h : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = h * x * (h : G)⁻¹ →
    β x' = G6.coreAct 7 (π h) (β x))
include hβ

include S hV1I hIU hIn hβker

theorem false_of_three (h2 : Lemma14_7_2) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    {Y : Subgroup G} (hYH : Y ≤ H) (hYo : oTwoUpper Y = Y)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hYT : quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)))
    {v : G} (hv : v ∈ V₂) {u₁ u₂ : G} (hu₁ : u₁ ∈ Y) (hu₂ : u₂ ∈ Y)
    (hind : ∀ a b c : ZMod 2,
      (fun i => a * Alt7.coords (β ⟨v, le_conjClosure V H (hV2.2.1 hv)⟩) i +
        b * Alt7.coords (β ⟨v, le_conjClosure V H (hV2.2.1 hv)⟩) ((π ⟨u₁, hYH hu₁⟩)⁻¹ i) +
        c * Alt7.coords (β ⟨v, le_conjClosure V H (hV2.2.1 hv)⟩) ((π ⟨u₂, hYH hu₂⟩)⁻¹ i)) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) : False := by
  have hsl := (h2 _ T L V H S I hV1I hIU hIn Y V₂ hV2 hYH hYo hTY hYT).2.1
  have hvU : v ∈ conjClosure V H := le_conjClosure V H (hV2.2.1 hv)
  set Z := conjClosure V₂ Y ⊔ I with hZ
  have hZU : Z ≤ conjClosure V H := sup_le (conjClosure_le fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H (hYH hy)) x).mp
      (le_conjClosure V H (hV2.2.1 hx))) hIU.le
  have hrel := relIndex_eq_card_map β hβker hZU
  have hx₁ : u₁ * v * u₁⁻¹ ∈ conjClosure V H :=
    hZU (Subgroup.mem_sup_left (mem_conjClosure hu₁ hv))
  have hx₂ : u₂ * v * u₂⁻¹ ∈ conjClosure V H :=
    hZU (Subgroup.mem_sup_left (mem_conjClosure hu₂ hv))
  have e₁ : β ⟨u₁ * v * u₁⁻¹, hx₁⟩ = G6.coreAct 7 (π ⟨u₁, hYH hu₁⟩) (β ⟨v, hvU⟩) :=
    hβ _ _ _ rfl
  have e₂ : β ⟨u₂ * v * u₂⁻¹, hx₂⟩ = G6.coreAct 7 (π ⟨u₂, hYH hu₂⟩) (β ⟨v, hvU⟩) :=
    hβ _ _ _ rfl
  have m₀ : β ⟨v, hvU⟩ ∈ (Z.subgroupOf (conjClosure V H)).map β :=
    ⟨⟨v, hvU⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (le_conjClosure V₂ Y hv)),
      rfl⟩
  have m₁ : β ⟨u₁ * v * u₁⁻¹, hx₁⟩ ∈ (Z.subgroupOf (conjClosure V H)).map β :=
    ⟨⟨u₁ * v * u₁⁻¹, hx₁⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (mem_conjClosure hu₁ hv)), rfl⟩
  have m₂ : β ⟨u₂ * v * u₂⁻¹, hx₂⟩ ∈ (Z.subgroupOf (conjClosure V H)).map β :=
    ⟨⟨u₂ * v * u₂⁻¹, hx₂⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (mem_conjClosure hu₂ hv)), rfl⟩
  have h8 := Alt7.eight_le_card m₀ m₁ m₂ (by
    intro a b c h
    apply hind a b c
    rw [e₁, e₂] at h
    simpa only [Alt7.coords_coreAct] using h)
  rcases hsl with h | h <;> omega

end Six

end CFSG.Quasithin.H13.L32A.C
