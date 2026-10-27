module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Quasithin.L34Bin

variable {R E G : Type} [Ring R] [AddCommGroup E] [Module R E] [Group G]
  (ρ : G →* Module.End R E)

@[expose] def IsInvSub (N : Submodule R E) : Prop := ∀ g, ∀ v ∈ N, ρ g v ∈ N

theorem inf_sup_eq_bot {N C W : Submodule R E} (h₁ : N ⊓ C = ⊥) (h₂ : (N ⊔ C) ⊓ W = ⊥) :
    N ⊓ (C ⊔ W) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxCW⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxCW
  have hz0 : z = 0 := by
    have hzNC : z ∈ N ⊔ C := by
      have : z = (y + z) - y := (add_sub_cancel_left y z).symm
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxN) (Submodule.mem_sup_right hy)
    have hm : z ∈ (N ⊔ C) ⊓ W := Submodule.mem_inf.mpr ⟨hzNC, hz⟩
    rw [h₂] at hm
    exact (Submodule.mem_bot R).mp hm
  subst hz0
  rw [add_zero] at hxN ⊢
  have hm : y ∈ N ⊓ C := Submodule.mem_inf.mpr ⟨hxN, hy⟩
  rwa [h₁] at hm

theorem exists_isCompl_of_sSup [Finite E] (𝒲 : Set (Submodule R E))
    (hirr : ∀ W ∈ 𝒲, IsInvSub ρ W ∧
      ∀ M : Submodule R E, IsInvSub ρ M → M ≤ W → M = ⊥ ∨ M = W)
    (htop : sSup 𝒲 = ⊤) {N : Submodule R E} (hN : IsInvSub ρ N) :
    ∃ C : Submodule R E, IsInvSub ρ C ∧ IsCompl N C := by
  classical
  have : Finite (Submodule R E) :=
    Finite.of_injective (fun S : Submodule R E => (S : Set E)) SetLike.coe_injective
  let P : Set (Submodule R E) := {C | IsInvSub ρ C ∧ N ⊓ C = ⊥}
  have hPfin : P.Finite := Set.toFinite P
  have hPne : hPfin.toFinset.Nonempty :=
    ⟨⊥, hPfin.mem_toFinset.mpr ⟨fun g v hv => by
      rw [(Submodule.mem_bot R).mp hv, map_zero]
      exact Submodule.zero_mem _, inf_bot_eq N⟩⟩
  obtain ⟨C, hCP, hCmax⟩ := hPfin.toFinset.exists_max_image (fun C => Nat.card C) hPne
  obtain ⟨hCinv, hNC⟩ := hPfin.mem_toFinset.mp hCP
  refine ⟨C, hCinv, ⟨disjoint_iff.mpr hNC, codisjoint_iff.mpr ?_⟩⟩
  rw [eq_top_iff, ← htop, sSup_le_iff]
  intro W hW
  obtain ⟨hWinv, hWirr⟩ := hirr W hW
  by_cases hW0 : W = ⊥
  · rw [hW0]
    exact bot_le
  have hinv : IsInvSub ρ ((N ⊔ C) ⊓ W) := by
    intro g v ⟨hv₁, hv₂⟩
    refine ⟨?_, hWinv g v hv₂⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv₁
    rw [map_add]
    exact Submodule.add_mem_sup (hN g a ha) (hCinv g b hb)
  rcases hWirr _ hinv inf_le_right with h | h
  ·
    exfalso
    have hCW : C ⊔ W ∈ P := by
      refine ⟨fun g v hv => ?_, inf_sup_eq_bot hNC h⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.add_mem_sup (hCinv g a ha) (hWinv g b hb)
    have hlt : C < C ⊔ W := by
      refine lt_of_le_of_ne le_sup_left fun heq => hW0 ?_
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ C := heq ▸ Submodule.mem_sup_right hw
      have hwNC : w ∈ (N ⊔ C) ⊓ W := ⟨Submodule.mem_sup_right hwC, hw⟩
      rw [h] at hwNC
      exact hwNC
    have hcard : Nat.card C < Nat.card (C ⊔ W : Submodule R E) := by
      have hss : (C : Set E) ⊂ ((C ⊔ W : Submodule R E) : Set E) := hlt
      have h1 := Set.ncard_lt_ncard hss (Set.toFinite _)
      rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
    exact absurd (hCmax _ (hPfin.mem_toFinset.mpr hCW)) (not_le.mpr hcard)
  · rw [← h]
    exact inf_le_left

variable {ρ}

theorem projection_comm {p q : Submodule R E} (hp : IsInvSub ρ p) (hq : IsInvSub ρ q)
    (h : IsCompl p q) (g : G) (v : E) :
    p.projection q h (ρ g v) = ρ g (p.projection q h v) := by
  have hv := Submodule.projection_add_projection_eq_self h v
  conv_lhs => rw [← hv, map_add]
  rw [map_add, Submodule.projection_apply_of_mem_left h
      (hp g _ (Submodule.projection_apply_mem h v)),
    Submodule.projection_apply_of_mem_right h (hq g _ (Submodule.projection_apply_mem h.symm v)),
    add_zero]

theorem projectionOnto_comm {p q : Submodule R E} (hp : IsInvSub ρ p) (hq : IsInvSub ρ q)
    (h : IsCompl p q) (g : G) (v : E) :
    (p.projectionOnto q h (ρ g v) : E) = ρ g (p.projectionOnto q h v) :=
  projection_comm hp hq h g v

theorem false_of_two_copies {U : Set G} {c : E} (hc : ∀ u ∈ U, ρ u c = c)
    (hgen : ∀ N : Submodule R E, IsInvSub ρ N → c ∈ N → N = ⊤)
    {W₁ W₂ C : Submodule R E} (hW₁ : IsInvSub ρ W₁) (hW₂ : IsInvSub ρ W₂) (hC : IsInvSub ρ C)
    (h₁₂ : W₁ ⊓ W₂ = ⊥) (hcompl : IsCompl (W₁ ⊔ W₂) C) (hW₂0 : W₂ ≠ ⊥)
    (θ : W₁ ≃ₗ[R] W₂) (hθ : ∀ g (w : W₁), (θ ⟨ρ g w, hW₁ g w w.2⟩ : E) = ρ g (θ w))
    (htrans : ∀ w w' : W₂, w ≠ 0 → w' ≠ 0 → (∀ u ∈ U, ρ u w = w) → (∀ u ∈ U, ρ u w' = w') →
      ∃ δ : W₂ →ₗ[R] W₂, (∀ g (w : W₂), (δ ⟨ρ g w, hW₂ g w w.2⟩ : E) = ρ g (δ w)) ∧ δ w = w') :
    False := by
  have hc₁ : IsCompl W₁ (W₂ ⊔ C) := by
    refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
    · exact inf_sup_eq_bot h₁₂ (disjoint_iff.mp hcompl.disjoint)
    · rw [← sup_assoc]
      exact codisjoint_iff.mp hcompl.codisjoint
  have hc₂ : IsCompl W₂ (W₁ ⊔ C) := by
    refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
    · exact inf_sup_eq_bot (inf_comm W₁ W₂ ▸ h₁₂) (by
        rw [sup_comm]
        exact disjoint_iff.mp hcompl.disjoint)
    · rw [← sup_assoc, sup_comm W₂ W₁]
      exact codisjoint_iff.mp hcompl.codisjoint
  have hinvsup : ∀ {A B : Submodule R E}, IsInvSub ρ A → IsInvSub ρ B → IsInvSub ρ (A ⊔ B) := by
    intro A B hA hB g v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hA g a ha) (hB g b hb)
  set p₁ := W₁.projectionOnto (W₂ ⊔ C) hc₁
  set p₂ := W₂.projectionOnto (W₁ ⊔ C) hc₂
  have hp₁ := projectionOnto_comm hW₁ (hinvsup hW₂ hC) hc₁
  have hp₂ := projectionOnto_comm hW₂ (hinvsup hW₁ hC) hc₂
  have hzero : ∀ ψ : E →ₗ[R] W₂, (∀ g v, (ψ (ρ g v) : E) = ρ g (ψ v)) → ψ c = 0 → ψ = 0 := by
    intro ψ hψ hψc
    have hker : LinearMap.ker ψ = ⊤ := hgen _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      apply Subtype.ext
      rw [hψ, hv, Submodule.coe_zero, map_zero]) hψc
    exact LinearMap.ker_eq_top.mp hker
  have hzero₁ : ∀ ψ : E →ₗ[R] W₁, (∀ g v, (ψ (ρ g v) : E) = ρ g (ψ v)) → ψ c = 0 → ψ = 0 := by
    intro ψ hψ hψc
    have hker : LinearMap.ker ψ = ⊤ := hgen _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      apply Subtype.ext
      rw [hψ, hv, Submodule.coe_zero, map_zero]) hψc
    exact LinearMap.ker_eq_top.mp hker
  have hW₁0 : W₁ ≠ ⊥ := by
    intro h
    apply hW₂0
    have hW := (Submodule.eq_bot_iff W₁).mp h
    rw [eq_bot_iff]
    intro w hw
    have h2 : θ.symm ⟨w, hw⟩ = 0 := Subtype.ext (hW _ (θ.symm ⟨w, hw⟩).2)
    have h3 := congrArg θ h2
    rw [LinearEquiv.apply_symm_apply, map_zero] at h3
    exact (Submodule.mem_bot R).mpr (congrArg Subtype.val h3)
  have hc₁0 : p₁ c ≠ 0 := by
    intro h0
    have hz := hzero₁ p₁ hp₁ h0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₁0
    have := LinearMap.congr_fun hz w
    rw [Submodule.projectionOnto_apply_of_mem_left hc₁ hw, LinearMap.zero_apply] at this
    exact hw0 (congrArg Subtype.val this)
  have hc₂0 : p₂ c ≠ 0 := by
    intro h0
    have hz := hzero p₂ hp₂ h0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₂0
    have := LinearMap.congr_fun hz w
    rw [Submodule.projectionOnto_apply_of_mem_left hc₂ hw, LinearMap.zero_apply] at this
    exact hw0 (congrArg Subtype.val this)
  have hθc0 : θ (p₁ c) ≠ 0 := fun h => hc₁0 (by
    have := congrArg θ.symm h
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this)
  have hθfix : ∀ u ∈ U, ρ u (θ (p₁ c)) = θ (p₁ c) := fun u hu => by
    rw [← hθ]
    congr 2
    apply Subtype.ext
    show ρ u (p₁ c) = p₁ c
    rw [← hp₁, hc u hu]
  have hc₂fix : ∀ u ∈ U, ρ u (p₂ c) = p₂ c := fun u hu => by
    rw [← hp₂, hc u hu]
  obtain ⟨δ, hδ, hδc⟩ := htrans _ _ hθc0 hc₂0 hθfix hc₂fix
  have hψ := hzero (δ ∘ₗ θ.toLinearMap ∘ₗ p₁ - p₂) (fun g v => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.coe_sub, map_sub]
    have e1 : p₁ (ρ g v) = ⟨ρ g (p₁ v), hW₁ g _ (p₁ v).2⟩ := Subtype.ext (hp₁ g v)
    have e2 : θ ⟨ρ g (p₁ v), hW₁ g _ (p₁ v).2⟩ = ⟨ρ g (θ (p₁ v)), hW₂ g _ (θ (p₁ v)).2⟩ :=
      Subtype.ext (hθ g (p₁ v))
    rw [e1, e2, hδ, hp₂]) (by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hδc, sub_self])
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₂0
  have h1 := LinearMap.congr_fun hψ w
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.zero_apply] at h1
  rw [Submodule.projectionOnto_apply_of_mem_right hc₁ (Submodule.mem_sup_left hw), map_zero,
    map_zero, Submodule.projectionOnto_apply_of_mem_left hc₂ hw, zero_sub, neg_eq_zero] at h1
  exact hw0 (congrArg Subtype.val h1)

end CFSG.Quasithin.L34Bin
