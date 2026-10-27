module

public import CFSG.Sporadic.Co1Patterson.RigidCore
public import CFSG.Sporadic.Co1Patterson.Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

section Swap

variable {X : Type*} [Group X] {t u g : X}

theorem mem_cent_inf_left (htu : t * u = u * t) :
    t ∈ centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X) :=
  mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_singleton_iff.2 htu⟩

theorem mem_cent_inf_right (htu : t * u = u * t) :
    u ∈ centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X) :=
  mem_inf.2 ⟨mem_centralizer_singleton_iff.2 htu.symm, mem_centralizer_singleton_iff.2 rfl⟩

theorem conj_mem_cent_inf (hg1 : g * t * g⁻¹ = u) (hg2 : g * u * g⁻¹ = t) {x : X}
    (hx : x ∈ centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X)) :
    g * x * g⁻¹ ∈ centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X) := by
  obtain ⟨h1, h2⟩ := mem_inf.1 hx
  rw [mem_centralizer_singleton_iff] at h1 h2
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
  · rw [← hg2]
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [h2]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  · rw [← hg1]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group

@[expose] def swapAut (hg1 : g * t * g⁻¹ = u) (hg2 : g * u * g⁻¹ = t) :
    ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X)) ≃*
      ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X)) where
  toFun x := ⟨g * x * g⁻¹, conj_mem_cent_inf hg1 hg2 x.2⟩
  invFun x := ⟨g⁻¹ * x * g⁻¹⁻¹, conj_mem_cent_inf (g := g⁻¹)
    (by rw [← hg2]; group) (by rw [← hg1]; group) x.2⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem card_sq_pCore_eq_of_swap (htu : t * u = u * t) (hg1 : g * t * g⁻¹ = u)
    (hg2 : g * u * g⁻¹ = t) :
    Nat.card {x : CFSG.pCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X)) //
        (x : ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X))) ^ 2 =
          ⟨t, mem_cent_inf_left htu⟩} =
      Nat.card {x : CFSG.pCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X)) //
        (x : ↥(centralizer ({t} : Set X) ⊓ centralizer ({u} : Set X))) ^ 2 =
          ⟨u, mem_cent_inf_right htu⟩} := by
  have h := card_sq_pCore_eq_of_aut (swapAut hg1 hg2) ⟨t, mem_cent_inf_left htu⟩
  have e : swapAut hg1 hg2 ⟨t, mem_cent_inf_left htu⟩ = ⟨u, mem_cent_inf_right htu⟩ :=
    Subtype.ext hg1
  rwa [e] at h

end Swap

theorem mem_centralizer_singleton_self {G : Type*} [Group G] (x : G) :
    x ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

section Transport

variable {X : Type*} [Group X] {t : X} {T : Type*} [Group T]

@[expose] def centInfEquiv (u : centralizer ({t} : Set X)) :
    ↥(centralizer ({t} : Set X) ⊓ centralizer ({(u : X)} : Set X)) ≃*
      ↥(centralizer ({u} : Set (centralizer ({t} : Set X)))) where
  toFun x := ⟨⟨x.1, (mem_inf.1 x.2).1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
    (mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2))⟩
  invFun y := ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def centMapEquiv {H : Type*} [Group H] (σ : H ≃* T) (u : H) :
    ↥(centralizer ({u} : Set H)) ≃* ↥(centralizer ({σ u} : Set T)) where
  toFun y := ⟨σ y.1, mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 y.2])⟩
  invFun v := ⟨σ.symm v.1, mem_centralizer_singleton_iff.2 (by
    have h := congrArg σ.symm (mem_centralizer_singleton_iff.1 v.2)
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h)⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv v := Subtype.ext (σ.apply_symm_apply _)
  map_mul' y y' := Subtype.ext (map_mul σ _ _)

theorem card_sq_pCore_cent_eq_of_swap (σ : centralizer ({t} : Set X) ≃* T)
    (u : centralizer ({t} : Set X)) {g : X} (hg1 : g * t * g⁻¹ = u) (hg2 : g * u * g⁻¹ = t) :
    Nat.card {x : CFSG.pCore 2 ↥(centralizer ({σ u} : Set T)) //
        ((x : ↥(centralizer ({σ u} : Set T))) : T) ^ 2 = σ ⟨t, mem_centralizer_singleton_self t⟩} =
      Nat.card {x : CFSG.pCore 2 ↥(centralizer ({σ u} : Set T)) //
        ((x : ↥(centralizer ({σ u} : Set T))) : T) ^ 2 = σ u} := by
  have htu : t * (u : X) = u * t := (mem_centralizer_singleton_iff.1 u.2).symm
  let β := (centInfEquiv u).trans (centMapEquiv σ u)
  have h0 := card_sq_pCore_eq_of_swap htu hg1 hg2
  rw [card_sq_pCore_eq β, card_sq_pCore_eq β] at h0
  have et : ((β ⟨t, mem_cent_inf_left htu⟩ : ↥(centralizer ({σ u} : Set T))) : T) =
      σ ⟨t, mem_centralizer_singleton_self t⟩ := rfl
  have eu : ((β ⟨u, mem_cent_inf_right htu⟩ : ↥(centralizer ({σ u} : Set T))) : T) = σ u := rfl
  have key : ∀ (c : ↥(centralizer ({σ u} : Set T))) (x : ↥(centralizer ({σ u} : Set T))),
      (x ^ 2 = c ↔ (x : T) ^ 2 = (c : T)) := fun c x => by
    rw [← Subtype.coe_inj, Subgroup.coe_pow]
  calc _ = Nat.card {x : CFSG.pCore 2 ↥(centralizer ({σ u} : Set T)) //
        (x : ↥(centralizer ({σ u} : Set T))) ^ 2 = β ⟨t, mem_cent_inf_left htu⟩} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [key, et])
    _ = Nat.card {x : CFSG.pCore 2 ↥(centralizer ({σ u} : Set T)) //
        (x : ↥(centralizer ({σ u} : Set T))) ^ 2 = β ⟨u, mem_cent_inf_right htu⟩} := h0
    _ = _ := Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [key, eu])

end Transport

theorem card_sq_pCore_centralizer_eq {X : Type} [Group X] [Finite X] {t : X}
    (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) {T : Type*} [Group T]
    (σ : centralizer ({t} : Set X) ≃* T) {w : T}
    (hwQ : ((σ.symm w : centralizer ({t} : Set X)) : X) ∈ (setting h).QG)
    (hw2 : orderOf w = 2) (hwt : w ≠ σ ⟨t, mem_centralizer_singleton_self t⟩) :
    Nat.card {x : CFSG.pCore 2 ↥(centralizer ({w} : Set T)) //
        ((x : ↥(centralizer ({w} : Set T))) : T) ^ 2 = σ ⟨t, mem_centralizer_singleton_self t⟩} =
      Nat.card {x : CFSG.pCore 2 ↥(centralizer ({w} : Set T)) //
        ((x : ↥(centralizer ({w} : Set T))) : T) ^ 2 = w} := by
  set u : centralizer ({t} : Set X) := σ.symm w with hu
  have hu2 : orderOf (u : X) = 2 := by
    rw [Subgroup.orderOf_coe, hu, MulEquiv.orderOf_eq, hw2]
  have hut : (u : X) ≠ t := fun he => hwt (by
    rw [← σ.apply_symm_apply w, ← hu]
    exact congrArg σ (Subtype.ext he))
  obtain ⟨g, hg1, hg2⟩ := exists_swap h hw hwQ hu2 hut
  have hσu : σ u = w := σ.apply_symm_apply w
  have key := card_sq_pCore_cent_eq_of_swap σ u hg1 hg2
  rw [hσu] at key
  exact key

end CFSG.Sporadic.Co1Patterson
