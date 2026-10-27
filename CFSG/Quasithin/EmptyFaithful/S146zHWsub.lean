module

public import CFSG.Quasithin.EmptyFaithful.S146zHCls

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Wsub

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] def Wsub (h : HypF91 T V L V₁ Vp H) (X : Subgroup G) : Subgroup (UMod h) :=
  (tildeOf V₁ X).comap (valW h)

theorem mem_Wsub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} {w : UMod h} :
    w ∈ Wsub h X ↔ w.val ∈ tildeOf V₁ X := Iff.rfl

theorem clsU_mem_Wsub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} {u : G}
    (hu : u ∈ conjClosure Vp H) (hX : u ∈ X) : clsU h hu ∈ Wsub h X :=
  secMk_mem_secImg (x := ⟨u, U_le_normalizer h hu⟩) hX

theorem exists_clsU_of_mem_Wsub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G}
    (hXU : X ≤ conjClosure Vp H) {w : UMod h} (hw : w ∈ Wsub h X) :
    ∃ u : G, ∃ hu : u ∈ conjClosure Vp H, u ∈ X ∧ clsU h hu = w := by
  obtain ⟨x, hx, hxw⟩ := mem_secImg.mp hw
  exact ⟨x, hXU hx, hx, IntMod.val_injective (by rw [clsU_val]; exact hxw)⟩

theorem rhoH_mem_Wsub (h : HypF91 T V L V₁ Vp H) (y : ↥H) {X Y : Subgroup G}
    (hXU : X ≤ conjClosure Vp H) (hXY : conjSub (y : G) X = Y) {w : UMod h}
    (hw : w ∈ Wsub h X) : rhoH h y w ∈ Wsub h Y := by
  obtain ⟨u, hu, huX, rfl⟩ := exists_clsU_of_mem_Wsub h hXU hw
  rw [rhoH_clsU]
  refine clsU_mem_Wsub h _ ?_
  rw [← hXY]
  exact mul_mem_conjSub huX

theorem card_Wsub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} (hXU : X ≤ conjClosure Vp H) :
    Nat.card (Wsub h X) = Nat.card (tildeOf V₁ X) := by
  have hK : tildeOf V₁ X ≤ (valW h).range := by
    intro x hx
    have hx' : x ∈ tildeOf V₁ (conjClosure Vp H) := secImg_mono hXU hx
    exact ⟨⟨x, hx'⟩, rfl⟩
  have h1 : (Wsub h X).map (valW h) = tildeOf V₁ X := by
    unfold Wsub
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hK]
  calc Nat.card (Wsub h X) = Nat.card ((Wsub h X).map (valW h)) :=
        (Subgroup.card_map_of_injective (valW_injective h)).symm
    _ = Nat.card (tildeOf V₁ X) := by rw [h1]

theorem Wsub_inf_eq_bot (h : HypF91 T V L V₁ Vp H) {X Y : Subgroup G}
    (hXU : X ≤ conjClosure Vp H) (hYU : Y ≤ conjClosure Vp H) (hVX : V₁ ≤ X)
    (hXY : X ⊓ Y ≤ V₁) : Wsub h X ⊓ Wsub h Y = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨u₁, hu₁, hu₁X, rfl⟩ := exists_clsU_of_mem_Wsub h hXU hw.1
  obtain ⟨u₂, hu₂, hu₂Y, hu₂w⟩ := exists_clsU_of_mem_Wsub h hYU hw.2
  have h12 : u₁⁻¹ * u₂ ∈ V₁ := (clsU_eq_iff h hu₁ hu₂).mp hu₂w.symm
  have hu₂X : u₂ ∈ X := by
    have e : u₂ = u₁ * (u₁⁻¹ * u₂) := by group
    rw [e]
    exact X.mul_mem hu₁X (hVX h12)
  have hu₂V : u₂ ∈ V₁ := hXY ⟨hu₂X, hu₂Y⟩
  rw [Subgroup.mem_bot, ← hu₂w]
  exact (clsU_eq_one_iff h hu₂).mpr hu₂V

end Wsub

end CFSG.Quasithin
