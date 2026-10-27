module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1O1Ne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c1_no_singular_transvection {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (hW : ∀ w : W, w * w = 1) (σ : MulAut W)
    (hσQ : ∀ x, Q (σ x) = Q x) {z : W} (hz1 : z ≠ 1) (hzQ : Q z = 0)
    (hfix : ∀ y : W, polarQ Q z y = 0 → σ y = y) : σ = 1 := by
  by_contra hσ1
  obtain ⟨v₀, hv₀⟩ : ∃ v : W, σ v ≠ v := by
    by_contra h
    push Not at h
    exact hσ1 (MulEquiv.ext h)
  have hinv : ∀ y : W, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (hW y)
  have hZ2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hZ2' : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hZ2add : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hZ2cancel : ∀ a b : ZMod 2, a + b = a → b = 0 := by decide
  have hzv₀ : polarQ Q z v₀ = 1 := hZ2' _ (fun h => hv₀ (hfix v₀ h))
  have hidx : ∀ x y : W, σ x ≠ x → σ y ≠ y → σ (x * y⁻¹) = x * y⁻¹ := by
    intro x y hx hy
    apply hfix
    have hzx : polarQ Q z x = 1 := hZ2' _ (fun h => hx (hfix x h))
    have hzy : polarQ Q z y = 1 := hZ2' _ (fun h => hy (hfix y h))
    calc polarQ Q z (x * y⁻¹)
        = polarQ Q z x + polarQ Q z y⁻¹ := hQ.1.2 z x y⁻¹
      _ = polarQ Q z x + polarQ Q z y := by rw [hinv y]
      _ = 1 + 1 := by rw [hzx, hzy]
      _ = 0 := by decide
  set c : W := σ v₀ * v₀⁻¹ with hcdef
  have hQc : Q c ≠ 0 := by
    rw [hcdef]
    exact quad_ne_zero_of_transvection hQ σ hσQ hidx hv₀
  have hc1 : c ≠ 1 := by
    intro h
    rw [hcdef] at h
    exact hv₀ (mul_inv_eq_one.1 h)
  have key1 : ∀ v : W, σ v ≠ v → σ v = v * c := by
    intro v hv
    have h := hidx v v₀ hv hv₀
    rw [map_mul, map_inv] at h
    calc σ v = σ v * (σ v₀)⁻¹ * σ v₀ := by group
      _ = v * v₀⁻¹ * σ v₀ := by rw [h]
      _ = v * c := by rw [hcdef]; ac_rfl
  have hpolarσ : ∀ x y : W, polarQ Q (σ x) (σ y) = polarQ Q x y := by
    intro x y
    unfold polarQ
    rw [← map_mul, hσQ (x * y), hσQ x, hσQ y]
  have hcase0 : ∀ y : W, polarQ Q z y = 0 → polarQ Q c y = 0 := by
    intro y hy
    have hσy : σ y = y := hfix y hy
    have hp : polarQ Q (σ v₀) (σ y) = polarQ Q v₀ y := hpolarσ v₀ y
    rw [hσy, key1 v₀ hv₀, hQ.1.1 v₀ c y] at hp
    exact hZ2cancel _ _ hp
  set ε : ZMod 2 := polarQ Q c v₀ with hεdef
  have hcase1 : ∀ y : W, polarQ Q z y = 1 → polarQ Q c y = ε := by
    intro y hy
    have hyv : polarQ Q z (y * v₀) = 0 := by
      rw [hQ.1.2 z y v₀, hy, hzv₀]
      decide
    have h0 := hcase0 (y * v₀) hyv
    rw [hQ.1.2 c y v₀, ← hεdef] at h0
    exact hZ2add _ _ h0
  by_cases hε0 : ε = 0
  · have hc0 : ∀ y : W, polarQ Q c y = 0 := by
      intro y
      rcases hZ2 (polarQ Q z y) with h | h
      · exact hcase0 y h
      · rw [hcase1 y h, hε0]
    obtain ⟨y, hy⟩ := hQ.2 c hc1
    exact hy (hc0 y)
  · have hε1 : ε = 1 := by
      rcases hZ2 ε with h | h
      · exact absurd h hε0
      · exact h
    have hcz : ∀ y : W, polarQ Q (c * z) y = 0 := by
      intro y
      rw [hQ.1.1 c z y]
      rcases hZ2 (polarQ Q z y) with h | h
      · rw [hcase0 y h, h, add_zero]
      · rw [hcase1 y h, h, hε1]
        decide
    have hcz1 : c * z = 1 := by
      by_contra hne
      obtain ⟨y, hy⟩ := hQ.2 (c * z) hne
      exact hy (hcz y)
    have hceq : c = z := mul_right_cancel (by rw [hcz1, hW z])
    exact hQc (by rw [hceq, hzQ])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
