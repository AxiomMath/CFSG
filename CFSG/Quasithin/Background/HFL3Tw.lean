module

public import CFSG.Quasithin.Background.HFL3Par

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H.SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_le_two_of_inf_img_eq_bot (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {E : Subgroup (MulAut (HMod n K))} (hE : E ≤ norm hK) (hEe : IsElemAbelian2 E)
    (hEL : E ⊓ img hK = ⊥) : Nat.card E ≤ 2 := by
  classical
  have hlin : ∀ e ∈ E, e ∈ linImg hK → e = 1 := by
    intro e he hel
    have h2 : IsPGroup 2 (Subgroup.zpowers e) :=
      (IsElemAbelian2.isPGroup hEe).to_le ((Subgroup.zpowers_le).2 he)
    have h3 : e ∈ E ⊓ img hK := ⟨he, mem_img_of_isPGroup_zpowers hK hel h2⟩
    rw [hEL] at h3
    exact h3
  have htw : ∀ e ∈ E, e ≠ 1 → ∃ D : GL (Fin 3) K, e = rhoT hK D * fldAut (bar n) := by
    intro e he he1
    have he2 : e * e = 1 := by rw [← sq]; exact hEe.2 e he
    obtain ⟨D, hD | hD⟩ := exists_of_involution hn hK (hE he) he2
    · exact absurd (hlin e he (hD ▸ ⟨D, rfl⟩)) he1
    · exact ⟨D, hD⟩
  have hbar : (bar n : K ≃+* K) * bar n = 1 := by
    ext x
    exact SU3.bar_bar hK x
  have hFF : (fldAut (bar (K := K) n) * fldAut (bar (K := K) n) : MulAut (HMod n K)) = 1 := by
    rw [← fldAut_mul, hbar, fldAut_one]
  have huniq : ∀ e ∈ E, ∀ f ∈ E, e ≠ 1 → f ≠ 1 → e = f := by
    intro e he f hf he1 hf1
    obtain ⟨D₁, hD₁⟩ := htw e he he1
    obtain ⟨D₂, hD₂⟩ := htw f hf hf1
    have hprod : e * f ∈ linImg hK := by
      refine ⟨D₁ * mapGL (bar n) D₂, ?_⟩
      rw [hD₁, hD₂, map_mul]
      calc rhoT hK D₁ * rhoT hK (mapGL (bar n) D₂)
          = rhoT hK D₁ * rhoT hK (mapGL (bar n) D₂) * (fldAut (bar n) * fldAut (bar n)) := by
            rw [hFF, mul_one]
        _ = rhoT hK D₁ * (rhoT hK (mapGL (bar n) D₂) * fldAut (bar n)) * fldAut (bar n) := by
            simp only [mul_assoc]
        _ = rhoT hK D₁ * (fldAut (bar n) * rhoT hK D₂) * fldAut (bar n) := by
            rw [fldAut_mul_rhoT]
        _ = rhoT hK D₁ * fldAut (bar n) * (rhoT hK D₂ * fldAut (bar n)) := by
            simp only [mul_assoc]
    have h1 := hlin _ (mul_mem he hf) hprod
    have hf2 : f * f = 1 := by rw [← sq]; exact hEe.2 f hf
    calc e = e * (f * f) := by rw [hf2, mul_one]
      _ = (e * f) * f := by rw [mul_assoc]
      _ = f := by rw [h1, one_mul]
  by_cases hb : E = ⊥
  · rw [hb, Subgroup.card_bot]
    norm_num
  · obtain ⟨g₀, hg₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
    set e₀ : MulAut (HMod n K) := (g₀ : MulAut (HMod n K)) with he₀def
    have he₀ : e₀ ∈ E := g₀.2
    have he₀1 : e₀ ≠ 1 := fun h => hg₀ (Subtype.ext h)
    have hle : E ≤ Subgroup.zpowers e₀ := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]
        exact one_mem _
      · rw [huniq e he e₀ he₀ he1 he₀1]
        exact Subgroup.mem_zpowers e₀
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers e₀) := Subgroup.card_le_of_le hle
      _ = orderOf e₀ := Nat.card_zpowers e₀
      _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEe.2 e₀ he₀))

end CFSG.Quasithin.H.L3Nine
