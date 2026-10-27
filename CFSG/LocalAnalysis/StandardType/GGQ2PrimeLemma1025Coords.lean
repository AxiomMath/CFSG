module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Coords

public section

namespace CFSG.GGQ2Prime

open Subgroup

theorem lem1025_coord_conj {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m a : Fin 7}
    (hW : WeylCoords Bs A x κ m) {g : G} (hl : IsCoordLift Bs κ g (Equiv.swap m a))
    (hz : g * x * g⁻¹ ∈ Bs) (j : Fin 7) :
    κ j ⟨g * x * g⁻¹, hz⟩ = if j = a then 1 else ω3 := by
  refine (hl j ⟨x, hW.x_mem⟩ hz).trans ?_
  rw [hW.x_coord, Equiv.symm_swap]
  have : (Equiv.swap m a) j = m ↔ j = a := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  simp only [this]

theorem lem1025_lift_fix {G : Type} [Group G] {Bs : Subgroup G}
    {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {y u : G} {σ : Equiv.Perm (Fin 7)} {a : Fin 7}
    (hl : IsCoordLift Bs κ y σ) (hu : u ∈ Bs) (hyu : y * u * y⁻¹ = u)
    (hcu : ∀ j, κ j ⟨u, hu⟩ = if j = a then 1 else ω3) : σ a = a := by
  have hgb : y * u * y⁻¹ ∈ Bs := by rw [hyu]; exact hu
  have h : κ a ⟨u, hu⟩ = κ (σ.symm a) ⟨u, hu⟩ := by
    have := hl a ⟨u, hu⟩ hgb
    rwa [show (⟨y * u * y⁻¹, hgb⟩ : Bs) = ⟨u, hu⟩ from Subtype.ext hyu] at this
  rw [hcu, hcu] at h
  have hσ : σ.symm a = a := by
    by_contra hne
    rw [if_pos rfl, if_neg hne] at h
    exact one_ne_ω3 h
  exact ((Equiv.symm_apply_eq σ).1 hσ).symm

theorem lem1025_lift_cent {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m k : Fin 7}
    (hW : WeylCoords Bs A x κ m) {y zk : G} {σ : Equiv.Perm (Fin 7)}
    (hl : IsCoordLift Bs κ y σ) (hy : y ∈ normalizer (Bs : Set G)) (hzk : zk ∈ Bs)
    (hck : ∀ j, κ j ⟨zk, hzk⟩ = if j = k then 1 else ω3) (hσ : σ k = k) :
    y * zk * y⁻¹ = zk := by
  have hyz : y * zk * y⁻¹ ∈ Bs := (mem_normalizer_iff.1 hy zk).1 hzk
  have hext : (⟨y * zk * y⁻¹, hyz⟩ : Bs) = ⟨zk, hzk⟩ := weylCoords_ext hW fun j => by
    refine (hl j ⟨zk, hzk⟩ hyz).trans ?_
    rw [hck, hck]
    have : σ.symm j = k ↔ j = k := by rw [Equiv.symm_apply_eq, hσ]
    simp only [this]
  exact congrArg Subtype.val hext

theorem lem1025_perm_unique {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut Bs)}
    {x : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m : Fin 7}
    (hW : WeylCoords Bs A x κ m) {σ σ' : Equiv.Perm (Fin 7)}
    (h : ∀ (b : Bs) (j : Fin 7), κ (σ.symm j) b = κ (σ'.symm j) b) : σ = σ' := by
  have hs : ∀ j, σ.symm j = σ'.symm j := fun j => by
    obtain ⟨u, hu⟩ := exists_point hW (σ.symm j)
    have := h u j
    rw [hu, hu] at this
    by_contra hne
    rw [if_pos rfl, if_neg (Ne.symm hne)] at this
    exact one_ne_ω3 this
  calc σ = σ.symm.symm := (Equiv.symm_symm σ).symm
    _ = σ'.symm.symm := by rw [Equiv.ext hs]
    _ = σ' := Equiv.symm_symm σ'

theorem lem1025_ncard_perm_fixing (S : Finset (Fin 7)) :
    {σ : Equiv.Perm (Fin 7) | ∀ a ∈ S, σ a = a}.ncard = (7 - S.card).factorial := by
  classical
  have hrange : {σ : Equiv.Perm (Fin 7) | ∀ a ∈ S, σ a = a} =
      Set.range (Equiv.Perm.ofSubtype : Equiv.Perm {a : Fin 7 // a ∉ S} →* Equiv.Perm (Fin 7)) := by
    ext σ
    rw [← MonoidHom.coe_range, SetLike.mem_coe, Equiv.Perm.mem_range_ofSubtype_iff]
    simp only [Set.mem_setOf_eq, Set.subset_def, Finset.mem_coe, Equiv.Perm.mem_support,
      Set.mem_ofPred_eq]
    exact ⟨fun h a ha hS => ha (h a hS), fun h a hS => by_contra fun ha => h a ha hS⟩
  rw [hrange, ← Set.image_univ, Set.ncard_image_of_injective _ Equiv.Perm.ofSubtype_injective,
    Set.ncard_univ, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

end CFSG.GGQ2Prime
