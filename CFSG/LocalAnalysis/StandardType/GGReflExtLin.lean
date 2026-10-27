module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRefl
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hpge)

theorem refl_asym_transv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (s ρ : V ≃ₗ[ZMod p] V) (a b : Module.Dual (ZMod p) V) (h k : V)
    (hs : ∀ w, s w = w - a w • h) (hρ : ∀ w, ρ w = w - b w • k) (ha : a h = 2) (hb : b k = 2)
    (hak : a k = 0) (hbh : b h ≠ 0) : IsTransv (s * ρ * s * ρ) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hk : k ≠ 0 := by
    intro hk0
    rw [hk0, map_zero] at hb
    exact h2 hb.symm
  have hφ : (b h • a : Module.Dual (ZMod p) V) ≠ 0 := by
    intro h0
    have := LinearMap.congr_fun h0 h
    simp only [LinearMap.smul_apply, ha, smul_eq_mul, LinearMap.zero_apply] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hbh h1
    · exact h2 h1
  have hg : ∀ w, (s * ρ * s * ρ) w = w + (b h • a : Module.Dual (ZMod p) V) w • k := by
    intro w
    simp only [LinearEquiv.mul_apply, hs, hρ, map_sub, map_smul, smul_eq_mul, hak, ha, hb,
      LinearMap.smul_apply]
    module
  refine isTransv_of_witness (s * ρ * s * ρ) k (b h • a) hg hk hφ ?_
  simp only [LinearMap.smul_apply, hak, smul_eq_mul, mul_zero]

end CFSG.ReflExt

end
