module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverLin
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def coordParD (k : ℕ) (hk : 4 ≤ k) (i : Fin k) : Fin k :=
  ⟨if i.val = k - 1 then k - 3 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩

private def coordDepthD (k : ℕ) (i : Fin k) : ℕ := if i.val = k - 1 then k - 2 else i.val

private theorem coordHslD (k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    cartanD k i j = 0 ∨ cartanD k i j = -1 := by
  simp only [cartanD, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

private theorem coordHparD (k : ℕ) (hk : 4 ≤ k) (i j : Fin k) (hij : i ≠ j) :
    cartanD k i j = -1 ↔ ((i ≠ ⟨0, by omega⟩ ∧ coordParD k hk i = j) ∨
      (j ≠ ⟨0, by omega⟩ ∧ coordParD k hk j = i)) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij' : i ≠ j := fun h => hij (Fin.ext h)
  simp only [cartanD, Matrix.of_apply, coordParD, ne_eq, Fin.mk.injEq, if_neg hij']
  by_cases hc : i + 1 = j ∧ j + 1 < k ∨ j + 1 = i ∧ i + 1 < k ∨ i + 3 = k ∧ j + 1 = k ∨
      j + 3 = k ∧ i + 1 = k
  · rw [if_pos hc]
    refine iff_of_true rfl ?_
    split_ifs <;> omega
  · rw [if_neg hc]
    refine iff_of_false (by decide) ?_
    split_ifs <;> omega

private theorem coordHdepthD (k : ℕ) (hk : 4 ≤ k) (i : Fin k) (hi : i ≠ ⟨0, by omega⟩) :
    coordDepthD k (coordParD k hk i) < coordDepthD k i := by
  have := i.isLt
  have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
  simp only [coordDepthD, coordParD]
  split_ifs <;> omega

private theorem coord_simple_pow {k : ℕ} (a b : Fin k) :
    (cartanD k a b = 0 → ((coxeterMatrix (isFiniteType_cartanD k)).simple a *
      (coxeterMatrix (isFiniteType_cartanD k)).simple b) ^ 2 = 1) ∧
    (cartanD k a b = -1 → ((coxeterMatrix (isFiniteType_cartanD k)).simple a *
      (coxeterMatrix (isFiniteType_cartanD k)).simple b) ^ 3 = 1) := by
  have h := (coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.simple_mul_simple_pow a b
  have hM : (coxeterMatrix (isFiniteType_cartanD k)) a b =
      TauCeti.coxeterOrder (cartanD k a b * cartanD k b a) := by
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  have hsym : cartanD k b a = cartanD k a b := by
    rw [cartanD_eq]
    exact (CartanMatrix.D_isSymm k).apply a b
  rw [CoxeterMatrix.toCoxeterSystem_simple, hM, hsym] at h
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rwa [h0, zero_mul, TauCeti.coxeterOrder_zero] at h
  · rwa [h1, show (-1 : ℤ) * -1 = 1 by norm_num, TauCeti.coxeterOrder_one] at h

theorem ggDk_exists_cartanPairing {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) {k : ℕ} (hk : 4 ≤ k) {ρ : ggWeylD k →* MulAut ↥Bs}
    (hρ : Function.Injective ρ)
    (hrefl : ∀ a, GGIsReflection p (ρ ((coxeterMatrix (isFiniteType_cartanD k)).simple a))) :
    ∃ (x : Fin k → V) (f : Fin k → Module.Dual (ZMod p) V),
      (∀ a v, ggLin (p := p) ι (ρ ((coxeterMatrix (isFiniteType_cartanD k)).simple a)) v =
        v - f a v • x a) ∧ ∀ a b, f a (x b) = (cartanD k a b : ZMod p) := by
  classical
  choose x f hfx hlin using fun a => exists_of_ggIsReflection ι (hrefl a)
  have h2 := zmod_two_ne_zero hp2
  have hR := fun a => ggLin_eq_reflection (p := p) ι (hfx a) (hlin a)
  have hne : ∀ a b, a ≠ b → Module.reflection (hfx a) ≠ Module.reflection (hfx b) :=
    fun a b hab h => hab ((coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.simple_injective
      (by simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        hρ (ggLin_injective (p := p) ι ((hR a).trans (h.trans (hR b).symm)))))
  have hpow : ∀ a b n, ((coxeterMatrix (isFiniteType_cartanD k)).simple a *
      (coxeterMatrix (isFiniteType_cartanD k)).simple b) ^ n = 1 →
      (Module.reflection (hfx a) * Module.reflection (hfx b)) ^ n = 1 := fun a b n h => by
    rw [← hR, ← hR, ← map_mul, ← map_mul, ← map_pow, ← map_pow, h, map_one, map_one]
  have hP0 : ∀ a b, a ≠ b → cartanD k a b = 0 → f a (x b) = 0 := fun a b hab h0 =>
    (TypeAReflOver.reflection_mul_reflection_pow_two_cross h2 (hfx a) (hfx b)
      (hpow a b 2 ((coord_simple_pow a b).1 h0)) (hne a b hab)).1
  have hP1 : ∀ a b, cartanD k a b = -1 → f a (x b) * f b (x a) = 1 := fun a b h1 => by
    have hab : a ≠ b := by
      rintro rfl
      simp [cartanD] at h1
    exact TypeAReflOver.reflection_mul_reflection_pow_three_cross h2 (hfx a) (hfx b)
      (hpow a b 3 ((coord_simple_pow a b).2 h1)) (hne a b hab)
  obtain ⟨c, hc0, hc⟩ := SpJoinRefl.exists_unit_gauge_of_tree (K := ZMod p)
    (fun i j => cartanD k i j) (fun i j => f i (x j)) (coordParD k hk) ⟨0, by omega⟩
    (coordDepthD k) (coordHslD k) hP0 hP1 (coordHparD k hk) (coordHdepthD k hk)
  refine ⟨fun b => c b • x b, fun a => (c a)⁻¹ • f a, fun a v => ?_, fun a b => ?_⟩
  · rw [hlin, LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm (c a)⁻¹, mul_assoc,
      inv_mul_cancel₀ (hc0 a), mul_one]
  · rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    by_cases hab : a = b
    · subst hab
      rw [inv_mul_cancel₀ (hc0 a), one_mul, hfx a]
      simp [cartanD]
    · exact hc a b hab

end CFSG.StandardType

end
