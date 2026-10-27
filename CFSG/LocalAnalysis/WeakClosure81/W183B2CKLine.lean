module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct

private lemma w183b2_charP_end (k : Type*) [Field k] [CharP k 2]
    (V : Type*) [AddCommGroup V] [Module k V] [Nontrivial V] :
    CharP (Module.End k V) 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap k (Module.End k V)) 2 (by norm_num)

private lemma w183b2_sq_sub_one {A : Type*} [Ring A] [CharP A 2] (a : A) (ha : a * a = 1) :
    (a - 1) * (a - 1) = 0 := by
  rw [CharTwo.sub_eq_add, add_mul, mul_add, mul_add, ha, one_mul, mul_one, one_mul,
    add_comm a 1, CharTwo.add_self_eq_zero]

private lemma w183b2_smul_eq_zero_of_ne_zero {k : Type*} [Field k] {M : Type*}
    [AddCommGroup M] [Module k M] {c : k} (hc : c ≠ 0) {x : M} (h : c • x = 0) : x = 0 := by
  calc x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = 0 := by rw [h, smul_zero]

private lemma w183b2_map_mul_one_left {k : Type*} [Field k] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (x y : Module.End k V) (z : Module.End k W) :
    TensorProduct.map x (1 : Module.End k W) * TensorProduct.map y z
      = TensorProduct.map (x * y) z := by
  rw [← TensorProduct.map_mul, one_mul]

private theorem w183b2_map_sum_eq_zero {k : Type*} [Field k] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {n : ℕ} {v : Fin n → Module.End k V} {w : Fin n → Module.End k W}
    (hv : LinearIndependent k v)
    (h : (∑ i : Fin n, TensorProduct.map (v i) (w i)) = 0) :
    ∀ i, w i = 0 := by
  intro i
  ext y
  by_contra hy
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem (p := (⊥ : Submodule k W))
    (by simpa using hy)
  have hg : (∑ j : Fin n, ψ (w j y) • v j) = 0 := by
    ext x
    have hx : (∑ j : Fin n, (v j x) ⊗ₜ[k] (w j y)) = (0 : V ⊗[k] W) := by
      have h' := congrArg (fun T : Module.End k (V ⊗[k] W) => T (x ⊗ₜ[k] y)) h
      simpa [TensorProduct.map_tmul] using h'
    have hy0 : (∑ j : Fin n, ψ (w j y) • (v j x)) = 0 := by
      have h'' := congrArg (fun z => (TensorProduct.rid k V)
        ((TensorProduct.map (LinearMap.id : V →ₗ[k] V) ψ) z)) hx
      simpa [TensorProduct.map_tmul, TensorProduct.rid_tmul] using h''
    simpa using hy0
  have hgi := (Fintype.linearIndependent_iff.mp hv (fun j => ψ (w j y)) hg) i
  exact hψ hgi

private lemma w183b2_map_eq_zero_of_ne_zero {k : Type*} [Field k] {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {x : Module.End k V} (hx : x ≠ 0) {y : Module.End k W}
    (h : TensorProduct.map x y = 0) : y = 0 := by
  have hLI : LinearIndependent k ![x] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    intro i
    have hg' : g 0 • x = 0 := by simpa using hg
    fin_cases i
    by_contra hg0
    exact hx (w183b2_smul_eq_zero_of_ne_zero hg0 hg')
  have hsum : (∑ i : Fin 1, TensorProduct.map (![x] i) (![y] i)) = 0 := by
    simpa [Fin.sum_univ_one] using h
  have := w183b2_map_sum_eq_zero (v := ![x]) (w := ![y]) hLI hsum 0
  simpa using this

theorem w183b2_pair_line {k : Type} [Field k] [CharP k 2] {U₁ U₂ : Type} [AddCommGroup U₁]
    [Module k U₁] [FiniteDimensional k U₁] [Nontrivial U₁] [AddCommGroup U₂] [Module k U₂]
    [FiniteDimensional k U₂] [Nontrivial U₂] {af ag : Module.End k U₁} {bf bg : Module.End k U₂}
    (haf : af * af = 1) (hag : ag * ag = 1) (hbf : bf * bf = 1) (hbg : bg * bg = 1)
    (hf1 : af ≠ 1) (hg2 : bg ≠ 1) (hca : af * ag = ag * af)
    (hq : (TensorProduct.map af bf - 1) * (TensorProduct.map ag bg - 1) = 0) :
    ∃ c : k, ag - 1 = c • (af - 1) := by
  classical
  set α : Module.End k U₁ := af - 1 with hα
  set α' : Module.End k U₁ := ag - 1 with hα'
  set γ : Module.End k U₁ := α * α' with hγ
  set βf : Module.End k U₂ := bf - 1 with hβf
  set βg : Module.End k U₂ := bg - 1 with hβg
  haveI hchar₁ : CharP (Module.End k U₁) 2 := w183b2_charP_end k U₁
  haveI hchar₂ : CharP (Module.End k U₂) 2 := w183b2_charP_end k U₂
  have hα2 : α * α = 0 := by rw [hα]; exact w183b2_sq_sub_one af haf
  have hα'2 : α' * α' = 0 := by rw [hα']; exact w183b2_sq_sub_one ag hag
  have hc : α * α' = α' * α := by
    rw [hα, hα']
    simp only [CharTwo.sub_eq_add, add_mul, mul_add, mul_one, one_mul]
    rw [hca]
    abel
  have hαα' : α * α' = γ := hγ.symm
  have hα'α : α' * α = γ := by rw [← hc, hαα']
  have hγα : γ * α = 0 := by
    nth_rewrite 1 [hγ]
    rw [mul_assoc, ← hc, ← mul_assoc, hα2, zero_mul]
  have hγα' : γ * α' = 0 := by
    nth_rewrite 1 [hγ]
    rw [mul_assoc, hα'2, mul_zero]
  have hαγ : α * γ = 0 := by
    nth_rewrite 1 [hγ]
    rw [← mul_assoc, hα2, zero_mul]
  have hα'γ : α' * γ = 0 := by
    nth_rewrite 1 [hγ]
    rw [← mul_assoc, ← hc, mul_assoc, hα'2, mul_zero]
  have hγγ : γ * γ = 0 := by
    nth_rewrite 1 [hγ]
    rw [mul_assoc, hα'γ, mul_zero]
  have hST : TensorProduct.map af bf - 1
      = TensorProduct.map (1 : Module.End k U₁) βf + TensorProduct.map α bf := by
    have hbf' : bf = βf + 1 := by rw [hβf]; abel
    have haf' : af = 1 + α := by rw [hα]; abel
    have hmap : TensorProduct.map (1 : Module.End k U₁) bf
        = TensorProduct.map (1 : Module.End k U₁) βf + 1 := by
      rw [hbf', TensorProduct.map_add_right, TensorProduct.map_one]
    rw [haf', TensorProduct.map_add_left, hmap]
    abel
  have hTT : TensorProduct.map ag bg - 1
      = TensorProduct.map (1 : Module.End k U₁) βg + TensorProduct.map α' bg := by
    have hbg' : bg = βg + 1 := by rw [hβg]; abel
    have hag' : ag = 1 + α' := by rw [hα']; abel
    have hmap : TensorProduct.map (1 : Module.End k U₁) bg
        = TensorProduct.map (1 : Module.End k U₁) βg + 1 := by
      rw [hbg', TensorProduct.map_add_right, TensorProduct.map_one]
    rw [hag', TensorProduct.map_add_left, hmap]
    abel
  have hprod : (TensorProduct.map (1 : Module.End k U₁) βf + TensorProduct.map α bf)
      * (TensorProduct.map (1 : Module.End k U₁) βg + TensorProduct.map α' bg)
      = TensorProduct.map (1 : Module.End k U₁) (βf * βg)
        + TensorProduct.map α (bf * βg) + TensorProduct.map α' (βf * bg)
        + TensorProduct.map γ (bf * bg) := by
    rw [mul_add, add_mul, add_mul]
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, ← TensorProduct.map_mul,
      ← TensorProduct.map_mul]
    simp only [one_mul, mul_one, hαα']
    abel
  have hrel : TensorProduct.map (1 : Module.End k U₁) (βf * βg)
      + TensorProduct.map α (bf * βg) + TensorProduct.map α' (βf * bg)
      + TensorProduct.map γ (bf * bg) = 0 := by
    rw [← hq, hST, hTT, hprod]
  by_contra hcon
  have hnot : ∀ c : k, α' ≠ c • α := fun c hc' => hcon ⟨c, hc'⟩
  have hαne : α ≠ 0 := by
    intro hzero
    rw [hα] at hzero
    exact hf1 (sub_eq_zero.mp hzero)
  have hpair : LinearIndependent k ![α, α'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      refine ⟨?_, ht⟩
      by_contra hs
      exact hαne (w183b2_smul_eq_zero_of_ne_zero hs hst)
    · have h1 : t • α' = -(s • α) := eq_neg_of_add_eq_zero_right hst
      refine (hnot (-(t⁻¹ * s)) ?_).elim
      calc α' = t⁻¹ • (t • α') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (-(s • α)) := by rw [h1]
        _ = (-(t⁻¹ * s)) • α := by rw [smul_neg, smul_smul, neg_smul]
  by_cases hγ0 : γ = 0
  · have hαα'0 : α * α' = 0 := by rw [hαα', hγ0]
    have hrel0 : TensorProduct.map (1 : Module.End k U₁) (βf * βg)
        + TensorProduct.map α (bf * βg) + TensorProduct.map α' (βf * bg) = 0 := by
      have h := hrel
      simp only [hγ0, TensorProduct.map_zero_left, add_zero] at h
      exact h
    have hw0 : βf * βg = 0 := by
      have hmul : TensorProduct.map α (βf * βg) = 0 := by
        have h := congrArg (fun x => TensorProduct.map α (1 : Module.End k U₂) * x) hrel0
        simp only [mul_add, mul_add, w183b2_map_mul_one_left, one_mul, mul_one, hα2,
          hαα'0, TensorProduct.map_zero_left, mul_zero, add_zero, zero_add] at h
        exact h
      exact w183b2_map_eq_zero_of_ne_zero hαne hmul
    have hrel1 : TensorProduct.map α (bf * βg) + TensorProduct.map α' (βf * bg) = 0 := by
      have h := hrel0
      simp only [hw0, TensorProduct.map_zero_right, zero_add] at h
      exact h
    have hw1 : bf * βg = 0 := by
      have hsum : (∑ i : Fin 2, TensorProduct.map (![α, α'] i)
          (![bf * βg, βf * bg] i)) = 0 := by
        simpa [Fin.sum_univ_two] using hrel1
      have := w183b2_map_sum_eq_zero (v := ![α, α']) (w := ![bf * βg, βf * bg])
        hpair hsum 0
      simpa using this
    have hβg0 : βg = 0 := by
      calc βg = bf * (bf * βg) := by rw [← mul_assoc, hbf, one_mul]
        _ = 0 := by rw [hw1, mul_zero]
    have hbg1 : bg = 1 := by
      have : bg - 1 = 0 := by rw [← hβg]; exact hβg0
      exact sub_eq_zero.mp this
    exact hg2 hbg1
  · have hw0 : βf * βg = 0 := by
      have hmul : TensorProduct.map γ (βf * βg) = 0 := by
        have h := congrArg (fun x => TensorProduct.map γ (1 : Module.End k U₂) * x) hrel
        simp only [mul_add, mul_add, mul_add, w183b2_map_mul_one_left, one_mul, mul_one,
          hγα, hγα', hγγ, TensorProduct.map_zero_left, mul_zero, add_zero, zero_add] at h
        exact h
      exact w183b2_map_eq_zero_of_ne_zero hγ0 hmul
    have hrel1 : TensorProduct.map α (bf * βg) + TensorProduct.map α' (βf * bg)
        + TensorProduct.map γ (bf * bg) = 0 := by
      have h := hrel
      simp only [hw0, TensorProduct.map_zero_right, zero_add] at h
      exact h
    have hw1 : bf * βg = 0 := by
      have hmul : TensorProduct.map γ (bf * βg) = 0 := by
        have h := congrArg (fun x => TensorProduct.map α' (1 : Module.End k U₂) * x) hrel1
        simp only [mul_add, mul_add, w183b2_map_mul_one_left, one_mul, mul_one, hα'α,
          hα'2, hα'γ, TensorProduct.map_zero_left, mul_zero, add_zero, zero_add] at h
        exact h
      exact w183b2_map_eq_zero_of_ne_zero hγ0 hmul
    have hrel2 : TensorProduct.map α' (βf * bg) + TensorProduct.map γ (bf * bg) = 0 := by
      have h := hrel1
      simp only [hw1, TensorProduct.map_zero_right, zero_add] at h
      exact h
    have hw2 : βf * bg = 0 := by
      have hmul : TensorProduct.map γ (βf * bg) = 0 := by
        have h := congrArg (fun x => TensorProduct.map α (1 : Module.End k U₂) * x) hrel2
        simp only [mul_add, w183b2_map_mul_one_left, one_mul, mul_one, hαα', hαγ,
          TensorProduct.map_zero_left, mul_zero, add_zero, zero_add] at h
        exact h
      exact w183b2_map_eq_zero_of_ne_zero hγ0 hmul
    have hrel3 : TensorProduct.map γ (bf * bg) = 0 := by
      have h := hrel2
      simp only [hw2, TensorProduct.map_zero_right, zero_add] at h
      exact h
    have hw3 : bf * bg = 0 := w183b2_map_eq_zero_of_ne_zero hγ0 hrel3
    have hunit : bf * bg ≠ 0 := by
      intro hzero
      have h1 : (bf * bg) * (bg * bf) = 1 := by
        rw [mul_assoc, ← mul_assoc bg bg bf, hbg, one_mul, hbf]
      rw [hzero, zero_mul] at h1
      exact one_ne_zero h1.symm
    exact hunit hw3

end CFSG.LocalAnalysis.WeakClosure81

end
