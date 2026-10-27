module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin


theorem mem_line0_of_zElt_mem {p : Fin 819} (h : zElt p ∈ d4V) : p ∈ line0 := by
  rcases mem_d4V_iff.mp h with h1 | h1 | h1 | h1
  · exact absurd h1 (zElt_ne_one p)
  · have : p = pt0 := zElt_injective (h1.trans zElt_zero.symm)
    rw [this]; exact Finset.mem_insert_self _ _
  · have : p = pt1 := zElt_injective h1
    rw [this]; simp [line0]
  · have : p = pt5 := zElt_injective h1
    rw [this]; simp [line0]; rfl

theorem zElt_mem_d4V_of_mem_line0 {p : Fin 819} (h : p ∈ line0) : zElt p ∈ d4V := by
  simp only [line0, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · rw [zElt_zero]; exact mem_d4V_iff.mpr (Or.inr (Or.inl rfl))
  · exact mem_d4V_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))
  · exact mem_d4V_iff.mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem mem_d4N_of_normalizes {g : D} (hg : ∀ v ∈ d4V, g * v * g⁻¹ ∈ d4V) : g ∈ d4N := by
  classical
  rw [mem_d4N_iff, smul_line0]
  have hsub : line0.image (act g) ⊆ line0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply mem_line0_of_zElt_mem
    rw [zElt_act]
    exact hg _ (zElt_mem_d4V_of_mem_line0 hp)
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_image_of_injective _ (act g).injective])

end CFSG.Quasithin.D4Hex
