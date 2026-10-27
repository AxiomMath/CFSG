module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def lr7er_C (i j : Fin 6) : ℤ :=
  if i = j then 2
  else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
          (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
    then -1 else 0

private theorem lr7er_C_apply (i j : Fin 6) : CartanMatrix.E 6 i j = lr7er_C i j := by
  fin_cases i <;> fin_cases j <;> decide

private def lr7er_k : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

private theorem lr7er_k_apply (i : Fin 6) :
    lr7er_k i = (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) i : ℕ) : ZMod 3) := by
  fin_cases i <;> rfl

private theorem lr7er_ker :
    ∀ c : Fin 6 → ZMod 3,
      (∀ j, ∑ i, (lr7er_C j i : ZMod 3) * c i = 0) ↔ ∃ a : ZMod 3, c = a • lr7er_k := by
  decide +kernel

private theorem lr7er_ker_zero (c : Fin 6 → ZMod 3)
    (hc : ∀ j, ∑ i, (lr7er_C j i : ZMod 3) * c i = 0) (h0 : c 0 = 0) : c = 0 := by
  obtain ⟨a, ha⟩ := (lr7er_ker c).mp hc
  have ha0 : a = 0 := by
    have h1 : c 0 = a * lr7er_k 0 := by
      rw [ha]
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [h0] at h1
    simpa [lr7er_k] using h1.symm
  rw [ha, ha0, zero_smul]

theorem ggDepE_relation {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod p) V} {x : V} (F : GGDepEFrame p h α x) :
    (∑ i : Fin 6, (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) i : ℕ) : ZMod p) • h i = 0) ∧
      x ∉ Submodule.span (ZMod p) (Set.range h) ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = 5 := by
  obtain rfl : p = 3 := F.p3
  have hdep := F.dep
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c, hcsum, i0, hi0⟩ := hdep
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hi0 (by rw [hzero]; simp)
  have hcC : ∀ j, ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * c k = 0 := by
    intro j
    have hh := congrArg (α j) hcsum
    simp only [map_sum, map_smul, F.pair, smul_eq_mul, map_zero] at hh
    calc ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * c k
        = ∑ k, c k * ((CartanMatrix.E 6) j k : ZMod 3) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm]
      _ = 0 := hh
  have hcC' : ∀ j, ∑ k, (lr7er_C j k : ZMod 3) * c k = 0 := by
    intro j
    simpa only [lr7er_C_apply] using hcC j
  obtain ⟨a, ha⟩ := (lr7er_ker c).mp hcC'
  have ha0 : a ≠ 0 := by
    intro haz
    apply hc0
    rw [ha, haz, zero_smul]
  have hsum0 : ∑ i, lr7er_k i • h i = 0 := by
    have hck : ∀ k, c k = a * lr7er_k k := by
      intro k
      rw [ha]
      simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : ∑ i, c i • h i = a • ∑ i, lr7er_k i • h i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hck i, mul_smul]
    rw [hcsum] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left ha0
  have hrel : ∑ i : Fin 6, (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) i : ℕ) : ZMod 3) • h i = 0 := by
    rw [← hsum0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lr7er_k_apply]
  have hxnot : x ∉ Submodule.span (ZMod 3) (Set.range h) := by
    intro hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨b, hb⟩ := hx
    have hbC : ∀ j, ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * b k = 0 := by
      intro j
      have hh := congrArg (α j) hb
      simp only [map_sum, map_smul, F.pair, smul_eq_mul, F.x_ker j, map_zero] at hh
      calc ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * b k
          = ∑ k, b k * ((CartanMatrix.E 6) j k : ZMod 3) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = 0 := hh
    have hbC' : ∀ j, ∑ k, (lr7er_C j k : ZMod 3) * b k = 0 := by
      intro j
      simpa only [lr7er_C_apply] using hbC j
    obtain ⟨a, ha⟩ := (lr7er_ker b).mp hbC'
    apply F.x_ne
    rw [← hb, ha]
    calc ∑ i, (a • lr7er_k) i • h i
        = ∑ i, a • (lr7er_k i • h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = a • ∑ i, lr7er_k i • h i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hsum0, smul_zero]
  have hk0 : lr7er_k ≠ 0 := by
    intro hz
    have h1 := congrFun hz 0
    simp [lr7er_k] at h1
  have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 5 := by
    let e := Finsupp.linearEquivFunOnFinite (ZMod 3) (ZMod 3) (Fin 6)
    let ψ : (Fin 6 →₀ ZMod 3) →ₗ[ZMod 3] V := Finsupp.linearCombination (ZMod 3) h
    let d₀ : Fin 6 →₀ ZMod 3 := e.symm lr7er_k
    have hd₀i : ∀ i, d₀ i = lr7er_k i := by
      intro i
      simp [d₀, e]
    have hψd₀ : ψ d₀ = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
      rw [show (∑ i, (fun i a => a • h i) i (d₀ i)) = ∑ i, lr7er_k i • h i from by
            exact Finset.sum_congr rfl fun i _ => by rw [hd₀i i]]
      exact hsum0
    have hd₀0 : d₀ ≠ 0 := by
      intro hz
      apply hk0
      funext i
      rw [← hd₀i i, hz]
      rfl
    have hker : ψ.ker = Submodule.span (ZMod 3) ({d₀} : Set (Fin 6 →₀ ZMod 3)) := by
      apply le_antisymm
      · intro l hl
        rw [LinearMap.mem_ker] at hl
        have hsuml : ∑ i, l i • h i = 0 := by
          rw [Finsupp.linearCombination_apply] at hl
          rwa [Finsupp.sum_fintype l (fun i a => a • h i) (fun i => by simp)] at hl
        let c : Fin 6 → ZMod 3 := fun i => l i
        have hcC : ∀ j, ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * c k = 0 := by
          intro j
          have hh := congrArg (α j) hsuml
          simp only [map_sum, map_smul, F.pair, smul_eq_mul, map_zero] at hh
          calc ∑ k, ((CartanMatrix.E 6) j k : ZMod 3) * c k
              = ∑ k, c k * ((CartanMatrix.E 6) j k : ZMod 3) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [mul_comm]
            _ = 0 := hh
        have hcC' : ∀ j, ∑ k, (lr7er_C j k : ZMod 3) * c k = 0 := by
          intro j
          simpa only [lr7er_C_apply] using hcC j
        rw [Submodule.mem_span_singleton]
        by_cases hl0 : l = 0
        · exact ⟨0, by rw [hl0]; simp⟩
        · have hc0 : c ≠ 0 := by
            intro hc
            apply hl0
            ext i
            exact congrFun hc i
          obtain ⟨a, ha⟩ := (lr7er_ker c).mp hcC'
          refine ⟨a, ?_⟩
          ext i
          have hi : c i = a * lr7er_k i := by
            rw [ha]
            simp only [Pi.smul_apply, smul_eq_mul]
          show (a • d₀) i = l i
          rw [Finsupp.smul_apply, smul_eq_mul, hd₀i i]
          exact hi.symm
      · intro l hl
        rw [Submodule.mem_span_singleton] at hl
        obtain ⟨a, ha⟩ := hl
        rw [LinearMap.mem_ker, ← ha]
        rw [map_smul, hψd₀, smul_zero]
    have hkerfin : Module.finrank (ZMod 3) ↥ψ.ker = 1 := by
      rw [hker]
      exact finrank_span_singleton hd₀0
    have hdomain : Module.finrank (ZMod 3) (Fin 6 →₀ ZMod 3) = 6 := by
      rw [Module.finrank_finsupp_self, Fintype.card_fin]
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    have hrange : Module.finrank (ZMod 3) ↥ψ.range = 5 := by
      rw [hkerfin, hdomain] at hrk
      omega
    rw [← Finsupp.range_linearCombination (ZMod 3) (v := h)]
    exact hrange
  exact ⟨hrel, hxnot, hfin⟩

theorem ggDepE_finrank_bounds {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V} {x : V} (F : GGDepEFrame p h α x) :
    6 ≤ Module.finrank (ZMod p) V ∧ Module.finrank (ZMod p) V ≤ 7 := by
  obtain ⟨hrel, hxnot, hfin⟩ := ggDepE_relation F
  have hx1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) = 1 := by
    simpa using finrank_span_singleton (K := ZMod p) (v := x) F.x_ne
  let e := Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin 6)
  let Ψ : V →ₗ[ZMod p] (Fin 6 →₀ ZMod p) :=
    e.symm.toLinearMap.comp (LinearMap.pi α)
  have hker_le : Ψ.ker ≤ Submodule.span (ZMod p) ({x} : Set V) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    apply F.fix v
    intro i
    have h1 := congrFun (congrArg (fun w => e w) hv) i
    simpa [Ψ, LinearMap.pi_apply, Finsupp.linearEquivFunOnFinite_apply] using h1
  have hkerfin : Module.finrank (ZMod p) ↥Ψ.ker ≤ 1 := by
    calc Module.finrank (ZMod p) ↥Ψ.ker
        ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) :=
          Submodule.finrank_mono hker_le
      _ = 1 := hx1
  have hcod : Module.finrank (ZMod p) (Fin 6 →₀ ZMod p) = 6 := by
    rw [Module.finrank_finsupp_self, Fintype.card_fin]
  have hrange_le : Module.finrank (ZMod p) ↥Ψ.range ≤ 6 := by
    calc Module.finrank (ZMod p) ↥Ψ.range
        ≤ Module.finrank (ZMod p) (Fin 6 →₀ ZMod p) := Submodule.finrank_le Ψ.range
      _ = 6 := hcod
  have hupper : Module.finrank (ZMod p) V ≤ 7 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [← hrk]
    omega
  let H := Submodule.span (ZMod p) (Set.range h)
  have hHfin : Module.finrank (ZMod p) ↥H = 5 := hfin
  have hinf_bot : H ⊓ Submodule.span (ZMod p) ({x} : Set V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvH, hvx⟩ := hv
    rw [Submodule.mem_span_singleton] at hvx
    obtain ⟨a, ha⟩ := hvx
    by_cases ha0 : a = 0
    · rw [← ha, ha0, zero_smul]
    · exfalso
      apply hxnot
      have hxv : x = a⁻¹ • v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hxv]
      exact Submodule.smul_mem H a⁻¹ hvH
  have hsupfin : Module.finrank (ZMod p) ↥(H ⊔ Submodule.span (ZMod p) ({x} : Set V)) = 6 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span (ZMod p) ({x} : Set V))
    rw [hinf_bot, finrank_bot, add_zero] at hsup
    rw [hsup, hHfin, hx1]
  have hlower : 6 ≤ Module.finrank (ZMod p) V := by
    have := Submodule.finrank_le (H ⊔ Submodule.span (ZMod p) ({x} : Set V))
    omega
  exact ⟨hlower, hupper⟩

end CFSG.StandardType
