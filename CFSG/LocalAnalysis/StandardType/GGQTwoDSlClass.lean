module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlChain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxRefl

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

theorem eq_dTau_of_reflection {m : ℕ} {u : DVec m ≃ₗ[ZMod 3] DVec m} (hu : u ∈ dEven m)
    {x : DVec m} {f : Module.Dual (ZMod 3) (DVec m)} (hfx : f x = 2)
    (h : ∀ v, u v = v - f v • x) :
    ∃ (ε : Bool) (p q : Fin m), p ≠ q ∧ u = dTau m ε p q := by
  obtain ⟨σ, c, hc, hprod, hact⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact absurd hfx (by decide)
  have hex : ∃ k₀, f (dBasis m k₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hf0 : f = 0 := (dBasis m).ext fun k => by simpa using hcon k
    rw [hf0, LinearMap.zero_apply] at hfx
    exact absurd hfx (by decide)
  obtain ⟨k₀, hk₀⟩ := hex
  have hcoord : ∀ k i, c k * dBasis m (σ k) i = dBasis m k i - f (dBasis m k) * x i := by
    intro k i
    have e1 : c k • dBasis m (σ k) = dBasis m k - f (dBasis m k) • x := by
      rw [← hact k, h]
    simpa using congrFun e1 i
  have hxs : ∀ i, i ≠ k₀ → i ≠ σ k₀ → x i = 0 := by
    intro i hi1 hi2
    have h1 := hcoord k₀ i
    simp only [dBasis_apply, hi1, hi2, if_false, mul_zero, zero_sub] at h1
    rcases mul_eq_zero.1 (neg_eq_zero.1 h1.symm) with h0 | h0
    · exact absurd h0 hk₀
    · exact h0
  have hfix : ∀ k, k ≠ k₀ → k ≠ σ k₀ → σ k = k ∧ c k = 1 := by
    intro k hk1 hk2
    have h1 := hcoord k k
    rw [hxs k hk1 hk2, mul_zero, sub_zero] at h1
    simp only [dBasis_apply, if_true] at h1
    by_cases hσ : k = σ k
    · rw [if_pos hσ, mul_one] at h1
      exact ⟨hσ.symm, h1⟩
    · rw [if_neg hσ, mul_zero] at h1
      exact absurd h1 (by decide)
  by_cases hA : σ k₀ = k₀
  · exfalso
    have hall : ∀ k, k ≠ k₀ → c k = 1 := fun k hk => (hfix k hk (by rw [hA]; exact hk)).2
    have hck : c k₀ = 1 := by
      have h1 := hprod
      rwa [Finset.prod_eq_single k₀ (fun k _ hk => hall k hk) (by simp)] at h1
    have h1 := hcoord k₀ k₀
    rw [hA] at h1
    simp only [dBasis_apply, if_true, hck, one_mul] at h1
    have hxk₀ : x k₀ = 0 := by
      have h2 : f (dBasis m k₀) * x k₀ = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h0 | h0
      · exact absurd h0 hk₀
      · exact h0
    apply hx0
    funext i
    by_cases hi : i = k₀
    · rw [hi]; exact hxk₀
    · exact hxs i hi (by rw [hA]; exact hi)
  · have hne : k₀ ≠ σ k₀ := fun h => hA h.symm
    have hσj : σ (σ k₀) ≠ σ k₀ := fun h => hne (σ.injective h).symm
    have hσσ : σ (σ k₀) = k₀ := by
      by_contra hcon
      exact hσj (σ.injective (hfix (σ (σ k₀)) hcon (fun h => hσj h)).1)
    have hcc : c k₀ * c (σ k₀) = 1 := by
      have h1 := hprod
      rwa [Finset.prod_eq_mul k₀ (σ k₀) hne (fun k _ hk => (hfix k hk.1 hk.2).2)
        (by simp) (by simp)] at h1
    have hcj : c (σ k₀) = c k₀ := by
      rcases hc k₀ with h0 | h0 <;> rcases hc (σ k₀) with h' | h' <;> rw [h0, h'] at hcc <;>
        first | exact absurd hcc (by decide) | rw [h0, h']
    have hsgn : sg (decide (c k₀ = -1)) = c k₀ := by
      rcases hc k₀ with h0 | h0
      · have hd : decide (c k₀ = -1) = false := by rw [h0]; decide
        rw [hd, h0]
        simp [sg]
      · have hd : decide (c k₀ = -1) = true := by rw [h0]; decide
        rw [hd, h0]
        simp [sg]
    refine ⟨decide (c k₀ = -1), k₀, σ k₀, hne, ?_⟩
    refine (dBasis m).ext' fun k => ?_
    rw [hact k]
    by_cases hk1 : k = k₀
    · rw [hk1, dTau_apply_left m _ hne]
      change c k₀ • dBasis m (σ k₀) = sg _ • dBasis m (σ k₀)
      rw [hsgn]
    · by_cases hk2 : k = σ k₀
      · rw [hk2, hσσ, dTau_apply_right m _ hne]
        change c (σ k₀) • dBasis m k₀ = sg _ • dBasis m k₀
        rw [hsgn, hcj]
      · rw [dTau_apply_of_ne m _ hk1 hk2, (hfix k hk1 hk2).1, (hfix k hk1 hk2).2, one_smul]

theorem e_dPermW {m : ℕ} (e : (ggCoxeterMatrixD m).Group ≃* dEven m) (π : Equiv.Perm (Fin m)) :
    ((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dPerm m π := by
  rw [dPermW, MulEquiv.apply_symm_apply]

theorem exists_conj_of_image_eq {m : ℕ} {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    {t : Fin m} {ε : Bool} {a b : Fin m} (hab : a ≠ b)
    (hs : ((e ((ggCoxeterMatrixD m).simple t) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m ε a b) {p q : Fin m} (hpq : p ≠ q) :
    ∃ u : (ggCoxeterMatrixD m).Group,
      ((e (u * (ggCoxeterMatrixD m).simple t * u⁻¹) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m ε p q := by
  have hf : Function.Injective ![a, b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have hg : Function.Injective ![p, q] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  have hπa : π a = p := by simpa using hπ 0
  have hπb : π b = q := by simpa using hπ 1
  refine ⟨dPermW e π, ?_⟩
  rw [coe_conj, hs, e_dPermW, dPerm_conj_dTau, hπa, hπb]

theorem exists_conj_simple_of_dTau {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e) (ε : Bool) {p q : Fin m}
    (hpq : p ≠ q) :
    ∃ (u : (ggCoxeterMatrixD m).Group) (t : Fin m),
      ((e (u * (ggCoxeterMatrixD m).simple t * u⁻¹) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m ε p q := by
  cases ε
  · have h0 : 0 < m := by omega
    have hm1 : 1 < m := by omega
    let q₀ : Fin m := ⟨0, h0⟩
    let q₁ : Fin m := ⟨1, hm1⟩
    have hs : ((e ((ggCoxeterMatrixD m).simple q₀) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m false q₀ q₁ := e_simple_of_lt he (j := q₀) (by simp [q₀]; omega)
    obtain ⟨u, hu⟩ := exists_conj_of_image_eq (Fin.ne_of_val_ne (by simp [q₀, q₁])) hs hpq
    exact ⟨u, q₀, hu⟩
  · have hlt : m - 1 < m := by omega
    let t : Fin m := ⟨m - 1, hlt⟩
    have hs := e_simple_last hm he (t := t) (by simp [t]; omega)
    obtain ⟨u, hu⟩ := exists_conj_of_image_eq (Fin.ne_of_val_ne (by simp; omega)) hs hpq
    exact ⟨u, t, hu⟩

end Sl

end CFSG.StandardType.QTwo

end
