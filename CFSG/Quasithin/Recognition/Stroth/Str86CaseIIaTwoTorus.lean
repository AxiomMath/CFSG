module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

open scoped Matrix

variable {F : Type} [Field F] [Finite F]

theorem u3_similitude_weight_fpf [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2) (g : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hgL : ∀ x ∈ su3Anti F k, ∃ x' ∈ su3Anti F k, ∀ v,
      g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ g v)
    (hgT : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k F, ∃ x' ∈ CFSG.Quasithin.H.SU3.ujSub k F, ∀ v,
      g ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (x' : Matrix (Fin 3) (Fin 3) F) *ᵥ g v)
    (hg0 : ∀ c : F, g (Pi.single 0 c) = Pi.single 0 c) :
    ∃ χ₂ χ₃ : Fˣ, (χ₃ : F) = (χ₂ : F) ^ (2 ^ k + 1) ∧ (χ₃ : F) ^ 2 ^ k = χ₃ ∧
      (∀ v : Fin 3 → F, v 2 = 0 → (g v) 2 = 0) ∧
      (∀ v : Fin 3 → F, v 2 = 0 → (g v) 1 = v 1 * (χ₂ : F)) ∧
      (∀ v : Fin 3 → F, (g v) 2 = v 2 * (χ₃ : F)) ∧
      ((χ₂ : F) ≠ 1 → ∀ v : Fin 3 → F, v 2 = 0 → (g v) 1 = v 1 → v 1 = 0) ∧
      ((χ₃ : F) ≠ 1 → ∀ v : Fin 3 → F, (g v) 2 = v 2 → v 2 = 0) ∧
      ((χ₂ : F) = 1 → ∀ v : Fin 3 → F, v 2 = 0 → (g v) 1 = v 1) ∧
      ((χ₃ : F) = 1 → ∀ v : Fin 3 → F, (g v) 2 = v 2) := by
  classical
  obtain ⟨hlin, χ₂, χ₃, hrel, hpow, ⟨x, hx⟩, ⟨y, z, hy⟩⟩ :=
    u3_similitude_weight (F := F) hk hFc g hgL hgT hg0
  have hdecomp : ∀ v : Fin 3 → F,
      v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    intro v
    funext i
    fin_cases i <;> simp
  have hgv : ∀ v : Fin 3 → F, g v = v 0 • g (Pi.single 0 1) + v 1 • g (Pi.single 1 1) +
      v 2 • g (Pi.single 2 1) := by
    intro v
    conv_lhs => rw [hdecomp v]
    rw [map_add, map_add, hlin, hlin, hlin]
  have h0 : g (Pi.single (0 : Fin 3) 1) = Pi.single (0 : Fin 3) 1 := hg0 1
  have hsub1 : ∀ (b : F), b • g (Pi.single 1 1) = b • ((χ₂ : F) • Pi.single 1 1 +
      Pi.single 0 x) := fun b => by rw [hx]
  have hsub2 : ∀ (c : F), c • g (Pi.single 2 1) = c • ((χ₃ : F) • Pi.single 2 1 +
      Pi.single 1 z + Pi.single 0 y) := fun c => by rw [hy]
  have hc2 : ∀ v : Fin 3 → F, (g v) 2 = v 2 * (χ₃ : F) := by
    intro v
    rw [hgv v, h0, hsub1, hsub2]
    simp [Pi.single_apply]
  have hc1 : ∀ v : Fin 3 → F, (g v) 1 = v 1 * (χ₂ : F) + v 2 * z := by
    intro v
    rw [hgv v, h0, hsub1, hsub2]
    simp [Pi.single_apply]
  refine ⟨χ₂, χ₃, hrel, hpow, ?_, ?_, hc2, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hc2, hv, zero_mul]
  · intro v hv
    rw [hc1, hv, zero_mul, add_zero]
  · intro hχ v hv hfix
    rw [hc1, hv, zero_mul, add_zero] at hfix
    have hzero : v 1 * ((χ₂ : F) - 1) = 0 := by
      rw [mul_sub, mul_one, hfix, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hχ
  · intro hχ v hfix
    have hEq : v 2 * (χ₃ : F) = v 2 := by rw [← hc2 v, hfix]
    have hzero : v 2 * ((χ₃ : F) - 1) = 0 := by
      rw [mul_sub, mul_one, hEq, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hχ
  · intro hχ v hv
    rw [hc1, hv, zero_mul, add_zero, hχ, mul_one]
  · intro hχ v
    rw [hc2, hχ, mul_one]

end CFSG.Quasithin.Stroth
