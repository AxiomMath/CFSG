module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable (S : Setting V V₁ L T) {g : G}
  (hg : Good V₁ L g)

include S hg

theorem sup_le_normalizer_inf_rconj_wA :
    L ⊔ uA V V₁ ≤ Subgroup.normalizer ((wA V V₁ ⊓ rconj (wA V V₁) g : Subgroup G) : Set G) := by
  rw [S.wA_inf_rconj_eq hg]
  exact S.sup_le_normalizer_inf_rconj hg

theorem exists_mul_of_mem_pCoreOf_sup {s : G} (hs : s ∈ pCoreOf 2 (L ⊔ uA V V₁)) :
    ∃ w ∈ wA V V₁, ∃ x ∈ rconj (wA V V₁) g, s = w * x := by
  have : s ∈ (wA V V₁ : Set G) * (rconj (wA V V₁) g : Set G) := by
    rw [← (S.pCoreOf_sup_eq_wA_sup hg).2]
    exact hs
  obtain ⟨w, hw, x, hx, hwx⟩ := this
  exact ⟨w, hw, x, hx, hwx.symm⟩

theorem nine_three {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) :
    (∀ s ∈ pCoreOf 2 (L ⊔ uA V V₁),
        (s * u * s⁻¹ * u⁻¹ ∈ wA V V₁ ⊓ rconj (wA V V₁) g ↔ s ∈ wA V V₁)) ∧
      (∀ s ∈ pCoreOf 2 (L ⊔ uA V V₁), s * u * s⁻¹ * u⁻¹ ∈ wA V V₁) ∧
      (∀ s ∈ pCoreOf 2 (L ⊔ uA V V₁), ∃ x ∈ rconj (wA V V₁) g,
        (s * u * s⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ ∈ wA V V₁ ⊓ rconj (wA V V₁) g) ∧
      (∀ w ∈ wA V V₁, ∃ x ∈ rconj (wA V V₁) g,
        x * u * x⁻¹ * u⁻¹ * w⁻¹ ∈ wA V V₁ ⊓ rconj (wA V V₁) g) := by
  set U := uA V V₁ with hUdef
  set W := wA V V₁ with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set I := L ⊔ U with hIdef
  set Sg := pCoreOf 2 I with hSdef
  have hEN : I ≤ Subgroup.normalizer (E : Set G) := S.sup_le_normalizer_inf_rconj_wA hg
  have hZE : V₁ ≤ E := S.V₁_le_inf_rconj hg
  have hWU : W ≤ U := wA_le_uA V V₁
  have hEW : E ≤ W := inf_le_left
  have hWI : W ≤ I := hWU.trans le_sup_right
  have hSI : Sg ≤ I := pCoreOf_le 2 I
  have huI : u ∈ I := Subgroup.mem_sup_right hu
  have hsuW : ∀ s ∈ Sg, s * u * s⁻¹ * u⁻¹ ∈ W := by
    intro s hs
    have h1 : u * s * u⁻¹ * s⁻¹ ∈ W := by
      rw [hWdef, S.wA_eq_inf_pCoreOf hg]
      refine ⟨?_, ?_⟩
      · have hau : s * u⁻¹ * s⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp
            (S.pCoreOf_sup_le_normalizer_uA hg hs) _).mp (U.inv_mem hu)
        have e3 : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
        rw [e3]
        exact U.mul_mem hu hau
      · have hua : u * s * u⁻¹ ∈ Sg :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I huI) _).mp hs
        exact Sg.mul_mem hua (Sg.inv_mem hs)
    have e : s * u * s⁻¹ * u⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1
  have hwuE : ∀ w ∈ W, w * u * w⁻¹ * u⁻¹ ∈ E := fun w hw =>
    hZE (S.commutator_mem (hWU hw) hu)
  refine ⟨fun s hs => ⟨fun hsE => ?_, fun hsW => hwuE s hsW⟩, hsuW, fun s hs => ?_, fun w hw => ?_⟩
  ·
    obtain ⟨w, hw, x, hx, rfl⟩ := S.exists_mul_of_mem_pCoreOf_sup hg hs
    have e : (w * x) * u * (w * x)⁻¹ * u⁻¹ =
        (w * (x * u * x⁻¹ * u⁻¹) * w⁻¹) * (w * u * w⁻¹ * u⁻¹) := by group
    rw [e] at hsE
    have h1 : w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ ∈ E := by
      have := E.mul_mem hsE (E.inv_mem (hwuE w hw))
      rwa [mul_inv_cancel_right] at this
    have h2 : x * u * x⁻¹ * u⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hEN (hWI hw)) _).mpr h1
    have h3 : x ∈ E := S.mem_inf_of_commutator_mem hg hu huW hx h2
    exact W.mul_mem hw (hEW h3)
  ·
    obtain ⟨w, hw, x, hx, rfl⟩ := S.exists_mul_of_mem_pCoreOf_sup hg hs
    refine ⟨x, hx, ?_⟩
    have hc : x * u * x⁻¹ * u⁻¹ ∈ W := hsuW x (S.rconj_wA_le_pCoreOf hg hx)
    have e : (w * x) * u * (w * x)⁻¹ * u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ =
        (w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹) *
          ((x * u * x⁻¹ * u⁻¹) * (w * u * w⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹) := by group
    rw [e]
    refine E.mul_mem ?_ ?_
    · have := S.commutator_mem (x := w) (y := x * u * x⁻¹ * u⁻¹)
        (hWU hw) (hWU hc)
      have e2 : w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ =
          w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ := rfl
      exact hZE this
    · have hcI : x * u * x⁻¹ * u⁻¹ ∈ I := hWI hc
      have := (Subgroup.mem_normalizer_iff.mp (hEN hcI) _).mp (hwuE w hw)
      exact this
  ·
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · rw [hXdef, mem_rconj]
      have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rw [e]
      exact hw
    · exact (S.module_relations hg hu huW).2.1 w hw

theorem nine_six {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) {x : G}
    (hx : x ∈ rconj (wA V V₁) g)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ centerOf (uA V V₁)) :
    x ∈ rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g) := by
  set ζ := u * x * u⁻¹ * x⁻¹ with hζ
  have hζZ : ζ ∈ centerOf (uA V V₁) := by
    have e : ζ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [hζ]; group
    rw [e]
    exact (centerOf (uA V V₁)).inv_mem hxu
  have hζW : ζ ∈ wA V V₁ := centerOf_uA_le_wA V V₁ hζZ
  have h1 := (S.module_relations hg hu huW).2.2.1 x hx ζ hζW (by
    have : (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ = 1 := by rw [← hζ]; group
    rw [this]
    exact Subgroup.one_mem _)
  have hyZg : g⁻¹ * ζ * g ∈ rconj (centerOf (uA V V₁)) g := inv_mul_mul_mem_rconj hζZ
  have e : x = (g⁻¹ * ζ * g) * (x⁻¹ * (g⁻¹ * ζ * g))⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyZg ((wA V V₁ ⊓ rconj (wA V V₁) g).inv_mem h1)

end Setting

end L128A

end CFSG.Quasithin.H13
