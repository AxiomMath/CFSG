module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolModel

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ} (M : Model n)

@[expose] def fixQ (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) : Subgroup M.W where
  carrier := {w | ∀ b ∈ B, delHom (M.act b) w ∈ U}
  one_mem' := fun b _ => by rw [map_one]; exact U.one_mem
  mul_mem' := fun {x y} hx hy b hb => by rw [map_mul]; exact U.mul_mem (hx b hb) (hy b hb)
  inv_mem' := fun {x} hx b hb => by rw [map_inv]; exact U.inv_mem (hx b hb)

variable {M}

theorem mem_fixQ {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W} {w : M.W} :
    w ∈ fixQ M B U ↔ ∀ b ∈ B, M.act b w * w⁻¹ ∈ U := Iff.rfl

theorem fixW_le_fixQ (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) :
    fixW M B ≤ fixQ M B U := fun w hw b hb => by
  show M.act b w * w⁻¹ ∈ U
  rw [hw b hb, mul_inv_cancel]
  exact U.one_mem

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := fun h => by
  have h1 : H.relIndex K ∣ Nat.card K := Subgroup.relIndex_dvd_card H K
  rw [h, zero_dvd_iff] at h1
  exact (Nat.card_pos (α := K)).ne' h1

theorem le_fixQ {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W} (hU : IsInvSub M B U) :
    U ≤ fixQ M B U := fun u hu b hb => U.mul_mem (hU b hb u hu) (U.inv_mem hu)

theorem ml0_fixQ_fixW {B : Subgroup (Perm (Fin n))}
    (hgen : B ≤ Subgroup.closure {x | x ∈ B ∧ Odd (orderOf x)}) :
    fixQ M B (fixW M B) = fixW M B :=
  le_antisymm (fun _ hv => ml0_fixW M hgen hv) (fixW_le_fixQ _ _)

theorem bf4_relIndex (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) :
    U.relIndex (fixW M B) ≤ U.relIndex (fixQ M B U) := by
  have h1 : U.relIndex (fixQ M B U) ≠ 0 := relIndex_ne_zero_of_finite _ _
  exact Subgroup.relIndex_le_of_le_right (fixW_le_fixQ B U) h1

theorem bf4_card {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W} (hU : IsInvSub M B U) :
    Nat.card (fixW M B) * Nat.card U ≤ Nat.card ↥(U ⊓ fixW M B) * Nat.card (fixQ M B U) := by
  have h1 := bf4_relIndex (M := M) B U
  have h2 := Subgroup.relIndex_mul_card (H := U) (K := fixW M B)
  have h4 := Subgroup.relIndex_mul_card (H := U) (K := fixQ M B U)
  rw [inf_eq_left.mpr (le_fixQ hU)] at h4
  calc Nat.card (fixW M B) * Nat.card U
      = (U.relIndex (fixW M B) * Nat.card ↥(U ⊓ fixW M B)) * Nat.card U := by rw [h2]
    _ ≤ (U.relIndex (fixQ M B U) * Nat.card ↥(U ⊓ fixW M B)) * Nat.card U := by gcongr
    _ = Nat.card ↥(U ⊓ fixW M B) * (U.relIndex (fixQ M B U) * Nat.card U) := by ring
    _ = _ := by rw [h4]

theorem bf4_index {B : Subgroup (Perm (Fin n))} {U : Subgroup M.W} (hU : IsInvSub M B U) :
    (fixW M B).relIndex U * (fixQ M B U).index ≤ (fixW M B).index := by
  have h1 : (fixW M B).relIndex (fixQ M B U) ≠ 0 := relIndex_ne_zero_of_finite _ _
  have h2 : (fixW M B).relIndex U ≤ (fixW M B).relIndex (fixQ M B U) :=
    Subgroup.relIndex_le_of_le_right (le_fixQ hU) h1
  rw [← Subgroup.relIndex_mul_index (fixW_le_fixQ B U)]
  exact Nat.mul_le_mul_right _ h2

theorem card_commW_zpowers_eq_relIndex {b : Perm (Fin n)} {U : Subgroup M.W}
    (hU : IsInvSub M (Subgroup.zpowers b) U) :
    Nat.card (commW M (Subgroup.zpowers b) U) = (fixW M (Subgroup.zpowers b)).relIndex U := by
  rw [commW_zpowers_eq_map M b hU, fixW_zpowers_eq_ker, Subgroup.relIndex_ker]

theorem bf5 (Γ : Set (Perm (Fin n))) {U : Subgroup M.W} (hU : IsInvSub M (Subgroup.closure Γ) U) :
    commW M (Subgroup.closure Γ) U = ⨆ γ ∈ Γ, commW M (Subgroup.zpowers γ) U := by
  apply le_antisymm
  · set K : Subgroup M.W := ⨆ γ ∈ Γ, commW M (Subgroup.zpowers γ) U with hK
    have key : ∀ g ∈ Subgroup.closure Γ, ∀ u ∈ U, M.act g u * u⁻¹ ∈ K := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        intro u hu
        refine Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem hx ?_)
        exact Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, u, hu, rfl⟩
      | one => intro u _; simp
      | mul a b ha hb hxa hxb =>
        intro u hu
        have hbu : M.act b u ∈ U := hU b hb u hu
        have e : M.act (a * b) u * u⁻¹ =
            (M.act a (M.act b u) * (M.act b u)⁻¹) * (M.act b u * u⁻¹) := by
          rw [act_mul_apply]
          simp only [mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact K.mul_mem (hxa _ hbu) (hxb u hu)
      | inv a ha hxa =>
        intro u hu
        have hau : M.act a⁻¹ u ∈ U := hU a⁻¹ (Subgroup.inv_mem _ ha) u hu
        have h1 := hxa _ hau
        rw [act_act_inv] at h1
        have := K.inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this
    unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, u, hu, rfl⟩
    exact key b hb u hu
  · refine iSup₂_le fun γ hγ => ?_
    unfold commW
    refine Subgroup.closure_mono ?_
    rintro _ ⟨b, hb, u, hu, rfl⟩
    exact ⟨b, (Subgroup.zpowers_le.mpr (Subgroup.subset_closure hγ)) hb, u, hu, rfl⟩

theorem bf7 {B : Subgroup (Perm (Fin n))} (hB : ⁅B, B⁆ = B) {U : Subgroup M.W}
    (hU1 : U ≤ fixW M B) (hq : ∀ (w : M.W), ∀ b ∈ B, M.act b w * w⁻¹ ∈ U) :
    fixW M B = ⊤ := by
  rw [eq_top_iff]
  intro v _ g hg
  let ψ : ↥B →* M.W :=
    { toFun := fun b => M.act (b : Perm (Fin n)) v * v⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hy : M.act (y : Perm (Fin n)) v = (M.act (y : Perm (Fin n)) v * v⁻¹) * v := by simp
        have hyU : M.act (y : Perm (Fin n)) v * v⁻¹ ∈ U := hq v y y.2
        have hfix : M.act (x : Perm (Fin n)) (M.act (y : Perm (Fin n)) v * v⁻¹) =
            M.act (y : Perm (Fin n)) v * v⁻¹ := hU1 hyU x x.2
        show M.act ((x : Perm (Fin n)) * (y : Perm (Fin n))) v * v⁻¹ = _
        rw [act_mul_apply]
        conv_lhs => rw [hy]
        rw [map_mul, hfix]
        simp only [mul_assoc, mul_comm] }
  have hker : ⁅B, B⁆ ≤ ψ.ker.map B.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    have hmem : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem h₁ h₂) (B.inv_mem h₁)) (B.inv_mem h₂)
    refine ⟨⟨g₁ * g₂ * g₁⁻¹ * g₂⁻¹, hmem⟩, ?_, rfl⟩
    have : (⟨g₁ * g₂ * g₁⁻¹ * g₂⁻¹, hmem⟩ : ↥B) =
        (⟨g₁, h₁⟩ : ↥B) * ⟨g₂, h₂⟩ * (⟨g₁, h₁⟩ : ↥B)⁻¹ * (⟨g₂, h₂⟩ : ↥B)⁻¹ := rfl
    show ψ ⟨g₁ * g₂ * g₁⁻¹ * g₂⁻¹, hmem⟩ = 1
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ψ _) (ψ _),
      mul_inv_cancel_right, mul_inv_cancel]
  have hg' : g ∈ ⁅B, B⁆ := by rw [hB]; exact hg
  obtain ⟨y, hy, hyg⟩ := hker hg'
  have : y = ⟨g, hg⟩ := Subtype.ext hyg
  rw [this] at hy
  exact mul_inv_eq_one.mp hy

end CFSG.Quasithin.F53Mod
