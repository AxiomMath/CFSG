module

public import CFSG.Monster.B.TwoA.Fischer.AffineCayleyLayers

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Conj

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

theorem labProd_map (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) {k : S}
    (hk : k ∈ setStab act lab Y C) (T : Finset C) :
    labProd lab (T.map (setStabPerm act lab Y C ⟨k, hk⟩).toEmbedding) =
      k * labProd lab T * k⁻¹ := by
  have hkC : ∀ x ∈ C, act k x ∈ C := fun x hx => (hk.2 x).2 hx
  have h1 : ∀ z : C, cliqueGen (lab := lab) ((setStabPerm act lab Y C ⟨k, hk⟩).toEmbedding z) =
      conjGen k (conj_mem_closure hlab hkC) (cliqueGen z) := fun z =>
    Subtype.ext (hlab k z)
  rw [labProd, Finset.prod_map, Finset.prod_congr rfl fun z _ => h1 z, ← map_prod]
  rfl

theorem conj_mem_labelLayer (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹)
    {k : S} (hk : k ∈ setStab act lab Y C) {r : S} {i : ℕ} (hr : r ∈ labelLayer lab C i) :
    k * r * k⁻¹ ∈ labelLayer lab C i := by
  obtain ⟨T, rfl, hTi, hmin⟩ := (mem_labelLayer_iff _ _).1 hr
  refine (mem_labelLayer_iff _ _).2 ⟨_, labProd_map hlab hk T, by rw [Finset.card_map, hTi],
    fun T' hT' => ?_⟩
  have h := labProd_map hlab ((setStab act lab Y C).inv_mem hk) T'
  rw [hT', inv_inv] at h
  have h2 : labProd lab (T'.map (setStabPerm act lab Y C
      ⟨k⁻¹, (setStab act lab Y C).inv_mem hk⟩).toEmbedding) = labProd lab T := by
    rw [h]
    group
  have := hmin _ h2
  rwa [Finset.card_map] at this

end Conj

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exists_mem_fix_of_mem_setStab {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {f : S} (hf : f ∈ setStab act lab Y C) :
    ∃ k ∈ setStab act lab Y C ⊓ actStab act x, ∀ z ∈ C, act k z = act f z := by
  obtain ⟨r, ⟨hr, hrx⟩, -⟩ :=
    hS.existsUnique_act_eq hC hx (hS.act_mem_hexadFiber_empty hf hx)
  refine ⟨r⁻¹ * f, ⟨(setStab act lab Y C).mul_mem
    ((setStab act lab Y C).inv_mem (ptStab_le_setStab C hr)) hf, ?_⟩, fun z hz => ?_⟩
  · change act (r⁻¹ * f) x = x
    rw [map_mul, Equiv.Perm.mul_apply, ← hrx, act_inv_act]
  · rw [map_mul, Equiv.Perm.mul_apply]
    exact ((ptStab act lab Y C).inv_mem hr).2 _ ((hf.2 z).2 hz)

theorem exists_mem_ne_ne {C : Set V} (hC : IsSliceMaxClique lab Y C) (p q : V) :
    ∃ d ∈ C, d ≠ p ∧ d ≠ q := by
  have hle : ({p, q} : Set V).ncard ≤ 2 := by
    have := Set.ncard_insert_le p ({q} : Set V)
    rw [Set.ncard_singleton] at this
    exact this
  obtain ⟨d, hd, hdpq⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {p, q}) (t := C)
    (by rw [hS.ncard_eq_of_isSliceMaxClique hC]; omega)
  exact ⟨d, hd, fun h => hdpq (by simp [h]), fun h => hdpq (by simp [h])⟩

theorem exists_setStab_image_eq {C : Set V} (hC : IsSliceMaxClique lab Y C) {T T' : Set V}
    (hT : T ⊆ C) (hT' : T' ⊆ C) (hTT' : T.ncard = T'.ncard) (h3 : T.ncard ≤ 3) :
    ∃ f ∈ setStab act lab Y C, act f '' T = T' := by
  have hCfin : C.Finite := hS.finite.subset hC.1.1
  have hTfin : T.Finite := hCfin.subset hT
  have hT'fin : T'.Finite := hCfin.subset hT'
  rcases (by omega : T.ncard = 0 ∨ T.ncard = 1 ∨ T.ncard = 2 ∨ T.ncard = 3) with h | h | h | h
  · have hT0 : T = ∅ := (Set.ncard_eq_zero hTfin).1 h
    have hT'0 : T' = ∅ := (Set.ncard_eq_zero hT'fin).1 (hTT' ▸ h)
    exact ⟨1, (setStab act lab Y C).one_mem, by rw [hT0, hT'0, Set.image_empty]⟩
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h
    obtain ⟨b, rfl⟩ := Set.ncard_eq_one.1 (hTT' ▸ h)
    obtain ⟨f, hf, hfa⟩ := hS.exists_setStab hC (hT rfl) (hT' rfl)
    exact ⟨f, hf, by rw [Set.image_singleton, hfa]⟩
  · obtain ⟨a₁, a₂, ha, rfl⟩ := Set.ncard_eq_two.1 h
    obtain ⟨b₁, b₂, hb, rfl⟩ := Set.ncard_eq_two.1 (hTT' ▸ h)
    have ha₁ : a₁ ∈ C := hT (by simp)
    have ha₂ : a₂ ∈ C := hT (by simp)
    have hb₁ : b₁ ∈ C := hT' (by simp)
    have hb₂ : b₂ ∈ C := hT' (by simp)
    obtain ⟨f₁, hf₁, hf₁a⟩ := hS.exists_setStab hC ha₁ hb₁
    have hc : act f₁ a₂ ∈ C := (hf₁.2 a₂).2 ha₂
    have hcb : act f₁ a₂ ≠ b₁ := fun e => ha ((act f₁).injective (hf₁a.trans e.symm))
    obtain ⟨d, hd, hdb, hdc⟩ := hS.exists_mem_ne_ne hC b₁ (act f₁ a₂)
    obtain ⟨d', hd', hd'b, hd'b₂⟩ := hS.exists_mem_ne_ne hC b₁ b₂
    obtain ⟨f₂, hf₂, hf₂u, hf₂c, -⟩ := hS.exists_setStab_pair hC hb₁ hc hd hb₂ hd' hcb hdb
      (Ne.symm hb) hd'b (Ne.symm hdc) (Ne.symm hd'b₂)
    refine ⟨f₂ * f₁, (setStab act lab Y C).mul_mem hf₂ hf₁, ?_⟩
    rw [Set.image_pair, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf₁a, hf₂u, hf₂c]
  · obtain ⟨a₁, a₂, a₃, h12, h13, h23, rfl⟩ := Set.ncard_eq_three.1 h
    obtain ⟨b₁, b₂, b₃, g12, g13, g23, rfl⟩ := Set.ncard_eq_three.1 (hTT' ▸ h)
    have ha₁ : a₁ ∈ C := hT (by simp)
    have ha₂ : a₂ ∈ C := hT (by simp)
    have ha₃ : a₃ ∈ C := hT (by simp)
    have hb₁ : b₁ ∈ C := hT' (by simp)
    have hb₂ : b₂ ∈ C := hT' (by simp)
    have hb₃ : b₃ ∈ C := hT' (by simp)
    obtain ⟨f₁, hf₁, hf₁a⟩ := hS.exists_setStab hC ha₁ hb₁
    have hc₂ : act f₁ a₂ ∈ C := (hf₁.2 a₂).2 ha₂
    have hc₃ : act f₁ a₃ ∈ C := (hf₁.2 a₃).2 ha₃
    have hc₂b : act f₁ a₂ ≠ b₁ := fun e => h12 ((act f₁).injective (hf₁a.trans e.symm))
    have hc₃b : act f₁ a₃ ≠ b₁ := fun e => h13 ((act f₁).injective (hf₁a.trans e.symm))
    have hc₂₃ : act f₁ a₂ ≠ act f₁ a₃ := fun e => h23 ((act f₁).injective e)
    obtain ⟨f₂, hf₂, hf₂u, hf₂c₂, hf₂c₃⟩ := hS.exists_setStab_pair hC hb₁ hc₂ hc₃ hb₂ hb₃ hc₂b
      hc₃b (Ne.symm g12) (Ne.symm g13) hc₂₃ g23
    refine ⟨f₂ * f₁, (setStab act lab Y C).mul_mem hf₂ hf₁, ?_⟩
    rw [Set.image_insert_eq, Set.image_pair, map_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf₁a, hf₂u, hf₂c₂, hf₂c₃]

theorem exists_fix_image_eq {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {T T' : Set V} (hT : T ⊆ C) (hT' : T' ⊆ C)
    (hTT' : T.ncard = T'.ncard) (h3 : T.ncard ≤ 3) :
    ∃ k ∈ setStab act lab Y C ⊓ actStab act x, act k '' T = T' := by
  obtain ⟨f, hf, hfT⟩ := hS.exists_setStab_image_eq hC hT hT' hTT' h3
  obtain ⟨k, hk, hkf⟩ := hS.exists_mem_fix_of_mem_setStab hC hx hf
  refine ⟨k, hk, ?_⟩
  rw [← hfT]
  exact Set.image_congr fun z hz => hkf z (hT hz)

theorem exists_conj_eq_of_mem_labelLayer {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {r r' : S} {i : ℕ} (hi : i ≤ 3)
    (hr : r ∈ labelLayer lab C i) (hr' : r' ∈ labelLayer lab C i) :
    ∃ k ∈ setStab act lab Y C ⊓ actStab act x, k * r * k⁻¹ = r' := by
  obtain ⟨T, rfl, hTi, -⟩ := (mem_labelLayer_iff _ _).1 hr
  obtain ⟨T', rfl, hT'i, -⟩ := (mem_labelLayer_iff _ _).1 hr'
  have hsub : ∀ T₀ : Finset C, Subtype.val '' (T₀ : Set C) ⊆ C := by
    rintro T₀ _ ⟨z, -, rfl⟩
    exact z.2
  have hcard : ∀ T₀ : Finset C, (Subtype.val '' (T₀ : Set C)).ncard = T₀.card := fun T₀ => by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
  obtain ⟨k, hk, hkT⟩ := hS.exists_fix_image_eq hC hx (hsub T) (hsub T')
    (by rw [hcard, hcard, hTi, hT'i]) (by rw [hcard, hTi]; exact hi)
  refine ⟨k, hk, ?_⟩
  rw [← labProd_map hS.lab_act hk.1 T]
  congr 1
  apply Finset.coe_injective
  apply Set.image_injective.2 Subtype.val_injective
  rw [← hkT, Finset.coe_map, Set.image_image, Set.image_image]
  rfl

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
