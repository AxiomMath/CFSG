module

public import CFSG.Quasithin.Vol2.Ch6H11Main

public section

noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin (fixV mem_fixV)
open CFSG.Quasithin.JonesParshall (sig sig_apply)
open CFSG.Quasithin.H13.H11P (uu coe_uu uu_zero)
open CFSG.Quasithin.H13.H11M (VH hm mkH rhoH UH Ws SigInv Zy Zy_mem E11 hm_injective
  card_KS card_eq_card_Ws hm_rhoH twist_apply KS)

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

@[expose] def zy (y : F) : VH a F := mkH (Zy a y) (Zy_mem hσ y)

theorem hm_zy (y : F) : hm (zy hσ y) = Zy a y := rfl

theorem hm_rhoH_uu_zy (s y : F) :
    hm (rhoH hσ (uu s) (zy hσ y)) = Zy a y + (s * sig a y + sig a s * y) • E11 F := by
  rw [hm_rhoH, hm_zy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [twist_apply] <;>
    simp [coe_uu, Zy, E11, Matrix.add_apply, Matrix.smul_apply] <;>
    ring

include hσ in
theorem sig_trace_term (s y : F) :
    sig a (s * sig a y + sig a s * y) = s * sig a y + sig a s * y := by
  rw [map_add, map_mul, map_mul, hσ, hσ]
  ring

@[expose] def zyCoset (a : ℕ) (y : F) : Set (VH a F) :=
  {w | ∃ t : F, sig a t = t ∧ hm w = Zy a y + t • E11 F}

theorem rhoH_uu_zy_mem_zyCoset (s y : F) : rhoH hσ (uu s) (zy hσ y) ∈ zyCoset a y :=
  ⟨s * sig a y + sig a s * y, sig_trace_term hσ s y, hm_rhoH_uu_zy hσ s y⟩

private theorem sig_hm_of_mem_zyCoset_A01 {y : F} (w : zyCoset a y) :
    sig a (hm w.1 0 0) = hm w.1 0 0 := by
  obtain ⟨t, ht, hw⟩ := w.2
  have h00 : hm w.1 0 0 = t := by
    rw [hw]
    simp [Zy, E11, Matrix.add_apply, Matrix.smul_apply]
  rw [h00, ht]

private theorem hm_eq_of_zyCoset_A01 {y : F} {w w' : zyCoset a y}
    (h : hm w.1 0 0 = hm w'.1 0 0) : w = w' := by
  obtain ⟨t, _, hw⟩ := w.2
  obtain ⟨t', _, hw'⟩ := w'.2
  have h00 : hm w.1 0 0 = t := by
    rw [hw]
    simp [Zy, E11, Matrix.add_apply, Matrix.smul_apply]
  have h00' : hm w'.1 0 0 = t' := by
    rw [hw']
    simp [Zy, E11, Matrix.add_apply, Matrix.smul_apply]
  have htt : t = t' := by rw [← h00, ← h00', h]
  exact Subtype.ext (hm_injective (by rw [hw, hw', htt]))

theorem card_zyCoset_le [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) (y : F) :
    Nat.card (zyCoset a y) ≤ 2 ^ a := by
  rw [← card_KS ha hF]
  refine Nat.card_le_card_of_injective
    (fun w : zyCoset a y => (⟨hm w.1 0 0, sig_hm_of_mem_zyCoset_A01 w⟩ : KS a F)) ?_
  intro w w' h
  exact hm_eq_of_zyCoset_A01 (congrArg Subtype.val h)

theorem zy_not_mem_fixV {A : Subgroup (MulAut (VH a F))} {s y : F} (hs : s ∈ Ws hσ A)
    (ht : s * sig a y + sig a s * y ≠ 0) : zy hσ y ∉ fixV A := by
  intro hzy
  have hfix : rhoH hσ (uu s) (zy hσ y) = zy hσ y := (mem_fixV.mp hzy) _ hs
  have h := congrArg hm hfix
  rw [hm_rhoH_uu_zy, hm_zy] at h
  have hzero : (s * sig a y + sig a s * y) • E11 F = 0 := by
    have h' : Zy a y + (s * sig a y + sig a s * y) • E11 F = Zy a y + 0 := by
      rw [add_zero]
      exact h
    exact add_left_cancel h'
  have h00 : s * sig a y + sig a s * y = 0 := by
    have := congrFun (congrFun hzero 0) 0
    simpa [E11, Matrix.smul_apply] using this
  exact ht h00

include hσ in
theorem trace_term_inv_eq_zero_iff {s₀ s : F} (hs₀ : s₀ ≠ 0) :
    s * sig a ((sig a s₀)⁻¹) + sig a s * (sig a s₀)⁻¹ = 0 ↔ s * sig a s₀ = sig a s * s₀ := by
  have hu : sig a s₀ ≠ 0 := by
    rw [sig_apply]
    exact pow_ne_zero _ hs₀
  have hsig : sig a ((sig a s₀)⁻¹) = s₀⁻¹ := by
    rw [map_inv₀, hσ]
  rw [hsig, ← div_eq_mul_inv, ← div_eq_mul_inv, CharTwo.add_eq_zero, div_eq_div_iff hs₀ hu]

theorem exists_ne_zero_mem_Ws {B : Subgroup (MulAut (VH a F))} (hB : B ≤ UH hσ) (hB1 : B ≠ ⊥) :
    ∃ s ∈ Ws hσ B, s ≠ 0 := by
  by_contra hne
  push Not at hne
  apply hB1
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨g, ⟨s, rfl⟩, rfl⟩ := hB hb
  rw [hne s hb, uu_zero, map_one]
  exact Subgroup.one_mem _

theorem card_le_of_collinear [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {B : Subgroup (MulAut (VH a F))} (hB : B ≤ UH hσ) {s₀ : F} (hs₀ : s₀ ≠ 0)
    (hcol : ∀ s ∈ Ws hσ B, s * sig a s₀ = sig a s * s₀) : Nat.card B ≤ 2 ^ a := by
  have hσs₀ : sig a s₀ ≠ 0 := by
    rw [sig_apply]
    exact pow_ne_zero _ hs₀
  rw [card_eq_card_Ws hσ hB, ← card_KS ha hF]
  refine Nat.card_le_card_of_injective (fun s : Ws hσ B => (⟨s.1 / s₀, ?_⟩ : KS a F))
    fun s s' h => ?_
  · rw [map_div₀, div_eq_div_iff hσs₀ hs₀]
    exact (hcol s.1 s.2).symm
  · have e : s.1 / s₀ = s'.1 / s₀ := congrArg Subtype.val h
    exact Subtype.ext ((div_left_inj' hs₀).mp e)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

end
