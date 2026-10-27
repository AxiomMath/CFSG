module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_mem_stabSub_of_mapsTo {U : Subgroup W} {x : MulAut W}
    (h : ∀ u ∈ U, x u ∈ U) : x ∈ stabSub U := by
  have hmap : U.map x.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      exact h u hu
    · exact (Subgroup.card_map_of_injective (K := U) x.injective).ge
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    rw [← hmap] at hu
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hu
    rwa [x.injective hwx] at hw
  · exact h u

theorem secCost_mono {t : MulAut W} {U₁ U₂ U₃ : Subgroup W} (h : U₂ ≤ U₃) :
    secCost t U₂ U₁ ≤ secCost t U₃ U₁ := by
  unfold secCost
  exact Nat.sub_le_sub_right (rk_mono (sup_le_sup_right (commSub_mono h le_rfl) U₁)) _

theorem secCost_add_le {t : MulAut W} {U₁ U₂ U₃ : Subgroup W} (htU₂ : ∀ u ∈ U₂, t u ∈ U₂)
    (h12 : U₁ ≤ U₂) (h23 : U₂ ≤ U₃) :
    secCost t U₂ U₁ + secCost t U₃ U₂ ≤ secCost t U₃ U₁ := by
  unfold secCost
  set A := commSub U₂ (Subgroup.zpowers t)
  set B := commSub U₃ (Subgroup.zpowers t)
  have hAB : A ≤ B := commSub_mono h23 le_rfl
  have hAU₂ : A ≤ U₂ := by
    refine commSub_le_of_invariant ?_
    intro x hx u hu
    have hle : Subgroup.zpowers t ≤ stabSub U₂ :=
      Subgroup.zpowers_le.mpr (w16f_mem_stabSub_of_mapsTo htU₂)
    exact ((mem_stabSub.mp (hle hx)) u).2 hu
  have hP : A ⊔ U₁ ≤ (B ⊔ U₁) ⊓ U₂ :=
    le_inf (sup_le (hAB.trans le_sup_left) le_sup_right) (sup_le hAU₂ h12)
  have hsum : rk ↥(B ⊔ U₂) + rk ↥(A ⊔ U₁) ≤ rk ↥(B ⊔ U₁) + rk U₂ := by
    have hsup : (B ⊔ U₁) ⊔ U₂ = B ⊔ U₂ := by rw [sup_assoc, sup_eq_right.mpr h12]
    have hrank := rk_sup_add_rk_inf (B ⊔ U₁) U₂
    rw [hsup] at hrank
    have hle : rk ↥(A ⊔ U₁) ≤ rk ↥((B ⊔ U₁) ⊓ U₂) := rk_mono hP
    omega
  have hd : rk ↥U₁ ≤ rk ↥(A ⊔ U₁) := rk_mono le_sup_right
  have he : rk ↥U₂ ≤ rk ↥(B ⊔ U₂) := rk_mono le_sup_right
  have hf : rk ↥U₁ ≤ rk ↥(B ⊔ U₁) := rk_mono le_sup_right
  omega

theorem secCost_top_bot (t : MulAut W) :
    secCost t ⊤ ⊥ = rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  unfold secCost
  rw [sup_bot_eq, rk_bot, Nat.sub_zero]

theorem exists_chief_nontrivial {L H : Subgroup (MulAut W)} (hL : ⁅L, L⁆ = L) (hLH : L ≤ H)
    {U₁ U₂ : Subgroup W} (hU₁ : StableUnder H U₁) (hU₂ : StableUnder H U₂) (hle : U₁ ≤ U₂)
    (hnt : ¬ commSub U₂ L ≤ U₁) :
    ∃ U₀ U : Subgroup W, U₁ ≤ U₀ ∧ U ≤ U₂ ∧ IsIrrOn H U U₀ ∧ commSub U₀ L ≤ U₁ ∧
      ¬ commSub U L ≤ U₀ := by
  classical
  let S : Set (Subgroup W) := {U | U₁ ≤ U ∧ U ≤ U₂ ∧ StableUnder H U ∧ ¬ commSub U L ≤ U₁}
  have hU₂S : U₂ ∈ S := ⟨hle, le_rfl, hU₂, hnt⟩
  obtain ⟨U, hUS, hmin⟩ := (wellFounded_lt (α := Subgroup W)).has_min S ⟨U₂, hU₂S⟩
  obtain ⟨hU₁U, hUU₂, hUstab, hUnt⟩ := hUS
  have hU₁ne : U₁ ≠ U := by
    intro h
    have h' : ¬ commSub U₁ L ≤ U₁ := by rwa [← h] at hUnt
    exact h' (commSub_le_of_invariant (fun x hx w hw => hU₁ x (hLH hx) w hw))
  have hU₁ltU : U₁ < U := lt_of_le_of_ne hU₁U hU₁ne
  let 𝒱 : Set (Subgroup W) := {V | U₁ ≤ V ∧ V < U ∧ StableUnder H V}
  let U₀ : Subgroup W := ⨆ V : {V : Subgroup W // V ∈ 𝒱}, (V : Subgroup W)
  have hU₁𝒱 : U₁ ∈ 𝒱 := ⟨le_rfl, hU₁ltU, hU₁⟩
  have hleU₁U₀ : U₁ ≤ U₀ :=
    le_iSup (fun V : {V : Subgroup W // V ∈ 𝒱} => (V : Subgroup W)) ⟨U₁, hU₁𝒱⟩
  have hU₀U : U₀ ≤ U :=
    iSup_le (fun V : {V : Subgroup W // V ∈ 𝒱} => V.2.2.1.le)
  have hU₀stab : StableUnder H U₀ :=
    stableUnder_iSup (fun V : {V : Subgroup W // V ∈ 𝒱} => V.2.2.2)
  have hcommV : ∀ V : {V : Subgroup W // V ∈ 𝒱}, commSub (V : Subgroup W) L ≤ U₁ := by
    intro V
    by_contra hc
    exact hmin V.1 ⟨V.2.1, V.2.2.1.le.trans hUU₂, V.2.2.2, hc⟩ V.2.2.1
  have hcommU₀ : commSub U₀ L ≤ U₁ := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    have hw' : w ∈ ⨆ V : {V : Subgroup W // V ∈ 𝒱}, (V : Subgroup W) := hw
    refine Subgroup.iSup_induction (fun V : {V : Subgroup W // V ∈ 𝒱} => (V : Subgroup W))
      (C := fun w => x w * w⁻¹ ∈ U₁) hw' ?_ ?_ ?_
    · intro V u hu
      exact hcommV V (Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩)
    · rw [map_one, inv_one, mul_one]
      exact U₁.one_mem
    · intro a b ha hb
      have h : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h]
      exact U₁.mul_mem ha hb
  have hU₀ne : U₀ ≠ U := by
    intro h
    exact hUnt (h ▸ hcommU₀)
  have hU₀ltU : U₀ < U := lt_of_le_of_ne hU₀U hU₀ne
  have hIrr : IsIrrOn H U U₀ := by
    refine ⟨hU₀ltU, hUstab, hU₀stab, ?_⟩
    intro J hJstab hU₀J hJU
    rcases eq_or_lt_of_le hJU with hJU' | hJU'
    · exact Or.inr hJU'
    · refine Or.inl (le_antisymm ?_ hU₀J)
      exact le_iSup (fun V : {V : Subgroup W // V ∈ 𝒱} => (V : Subgroup W))
        ⟨J, ⟨hleU₁U₀.trans hU₀J, hJU', hJstab⟩⟩
  have hntU : ¬ commSub U L ≤ U₀ := by
    intro hleU
    exact hUnt (s13_perfect_chain L hL U₁ U₀ U hcommU₀ hleU)
  exact ⟨U₀, U, hleU₁U₀, hUU₂, hIrr, hcommU₀, hntU⟩

end CFSG.LocalAnalysis.WeakClosure81
