module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l04fD5_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
    (hN : 2 ≤ N) : (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]
theorem l04fD5_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
    (j : Fin (N - 1)) : ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) *
      (((k : ℕ) + 1 : ℕ) : ZMod p) = 0 := by
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  change ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0
  rw [cartanA_row d j]
  have hc' : ∀ m : ℕ, (fun m => if hm : m < N - 1 then d ⟨m, hm⟩ else 0) m = (if m < N - 1 then (((m : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
    intro m
    by_cases hm : m < N - 1
    · simp [d, hm]
    · simp [hm]
  have hprev : (j : ℕ) - 1 < N - 1 := by omega
  simp only [hc']
  by_cases hlast : (j : ℕ) + 1 < N - 1
  · rw [if_pos j.isLt, if_pos hlast]
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]; norm_num
    · rw [if_neg hj0, if_pos hprev]
      have hsub : ((↑j - 1 : ℕ) : ZMod p) = (↑j : ZMod p) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
        norm_num
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hsub]; ring
  · rw [if_pos j.isLt, if_neg hlast]
    have hlast' : (j : ℕ) + 1 = N - 1 := by omega
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]
      have hN : N = 2 := by omega
      have h2 : (2 : ZMod p) = 0 := by
        have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
        simpa [hN] using hNcast
      norm_num
      exact h2
    · rw [if_neg hj0, if_pos hprev]
      have hjval : (j : ℕ) = N - 2 := by omega
      have e1 : (N - 2 : ℕ) + 1 = N - 1 := by omega
      have e2 : (N - 2 : ℕ) - 1 + 1 = N - 2 := by omega
      rw [hjval, e1, e2]
      convert l04fD5_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring
lemma l04fD5_relation {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    (hN : 11 ≤ N) (hpN : p ∣ N)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) : (∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h i = 0) ∧ Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = N - 2 := by
  classical
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨c, hcsum, i0, hi0⟩ := hdep
  have hc0 : c ≠ 0 := fun hc => hi0 (by rw [hc]; rfl)
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hd0 : d ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero ⟨0, by omega⟩
    simp [d] at h1
  have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
    intro j
    have hh := congrArg (α j) hcsum
    simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at hh
    calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k
        = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm]
      _ = 0 := hh
  have hdA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0 := fun j => l04fD5_A_mul_d (p := p) (N := N) hpN j
  have hsum : ∑ i : Fin (N - 1), d i • h i = 0 := by
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one c d hcA hdA hc0
    rw [hl]
    calc ∑ i, (l • c) i • h i
        = ∑ i, l • (c i • h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = l • ∑ i, c i • h i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hcsum, smul_zero]
  have hrel : ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h i = 0 := by simpa [d] using hsum
  let φ : (Fin (N - 1) → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  have hφd : φ d = 0 := by
    rw [Fintype.linearCombination_apply]
    simpa [d] using hrel
  have hker_le : φ.ker ≤ Submodule.span (ZMod p) ({d} : Set (Fin (N - 1) → ZMod p)) := by
    intro l hl
    rw [LinearMap.mem_ker] at hl
    have hlsum : ∑ i, l i • h i = 0 := by
      rw [Fintype.linearCombination_apply] at hl
      simpa using hl
    have hlA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * l k = 0 := by
      intro j
      have hh := congrArg (α j) hlsum
      simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at hh
      calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * l k
          = ∑ k, l k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = 0 := hh
    rw [Submodule.mem_span_singleton]
    by_cases hl0 : l = 0
    · exact ⟨0, by rw [hl0]; simp⟩
    · obtain ⟨a, ha⟩ := ggCartanA_ker_le_one d l hdA hlA hd0
      exact ⟨a, ha.symm⟩
  have hker_eq : φ.ker = Submodule.span (ZMod p) ({d} : Set (Fin (N - 1) → ZMod p)) := by
    apply le_antisymm hker_le
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [LinearMap.mem_ker, map_smul, hφd, smul_zero]
  have hkerfin : Module.finrank (ZMod p) ↥φ.ker = 1 := by
    rw [hker_eq]
    simpa using finrank_span_singleton (K := ZMod p) hd0
  have hdomain : Module.finrank (ZMod p) (Fin (N - 1) → ZMod p) = N - 1 := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrange : Module.finrank (ZMod p) ↥φ.range = N - 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    rw [hkerfin, hdomain] at hrk
    omega
  refine ⟨hrel, ?_⟩
  rw [← Fintype.range_linearCombination (ZMod p) h]
  exact hrange
lemma l04fD5_h_mem_move {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : V} {α : Module.Dual (ZMod p) V}
    {r : V ≃ₗ[ZMod p] V} (hα : α h = 2) (hr : ∀ v, r v = v - α v • h) : h ∈ ggLinMove r := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  rw [ggLinMove, LinearMap.mem_range]
  refine ⟨-(2 : ZMod p)⁻¹ • h, ?_⟩
  have hαv : α (-(2 : ZMod p)⁻¹ • h) = -1 := by
    rw [map_smul, hα, smul_eq_mul]
    have hc : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
    field_simp
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hr, hαv]
  module
lemma l04fD5_finite_of_moduleFinite {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] : Finite V := by
  obtain ⟨n, s, hs⟩ := (Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.Finite.fg_top (R := ZMod p) (M := V)))
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod p) s) := by
    intro v
    have hv : v ∈ Submodule.span (ZMod p) (Set.range s) := by rw [hs]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, hc⟩ := hv
    exact ⟨c, by rwa [Fintype.linearCombination_apply]⟩
  exact Finite.of_surjective _ hsurj
theorem l04fD5_dims {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) : (N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) ∧ Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N) ∧ Module.finrank (ZMod p) V = N ∧ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2 ∧ (Submodule.span (ZMod p) (Set.range h) ⊔ ggLinFix (Set.range r) = ⊤) := by
  classical
  have hN : 11 ≤ N := C.lin.N_ge
  have hN2 : 2 ≤ N := by omega
  have hp2 : p ≠ 2 := C.lin.p_ne_two
  have : Finite T := C.lin.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) (s := s) C.lin.s_refl C.lin.fix_s
  obtain ⟨hrel, hdimR⟩ := l04fD5_relation (p := p) (N := N) hN C.lin.p_dvd C.lin.pair C.dep
  let R : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  have hdimR' : Module.finrank (ZMod p) ↥R = N - 2 := hdimR
  have hR_le_T : R ≤ ggFixLineT r s := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    have hmem : h i ∈ ⨆ i, ggLinMove (r i) := le_iSup (fun i => ggLinMove (r i)) i
        (l04fD5_h_mem_move hp2 (hα := by rw [C.lin.pair i i]; simp [CartanMatrix.A])
          (hr := C.lin.refl_form i))
    show h i ∈ (⨆ i, ggLinMove (r i)) ⊔ (⨆ k, ggLinMove (s k))
    exact Submodule.mem_sup_left hmem
  have hTlow : N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    calc N - 2 = Module.finrank (ZMod p) ↥R := hdimR'.symm
      _ ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := Submodule.finrank_mono hR_le_T
  have hTup : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N := by
    calc Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ Module.finrank (ZMod p) V := Submodule.finrank_le _
      _ ≤ N := C.lin.dim_le
  have hRF : R ⊓ F = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvR, hvF⟩ := hv
    rw [Submodule.mem_span_range_iff_exists_fun] at hvR
    obtain ⟨c, rfl⟩ := hvR
    have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
      intro j
      have hfixj : r j (Fintype.linearCombination (ZMod p) h c) = Fintype.linearCombination (ZMod p) h c := hvF (r j) ⟨j, rfl⟩
      have hα0 : α j (Fintype.linearCombination (ZMod p) h c) = 0 := by
        have hz : α j (Fintype.linearCombination (ZMod p) h c) • h j = 0 := by
          have hsub : Fintype.linearCombination (ZMod p) h c -
              α j (Fintype.linearCombination (ZMod p) h c) • h j = Fintype.linearCombination (ZMod p) h c := by
            rw [← C.lin.refl_form j]
            exact hfixj
          exact sub_eq_self.mp hsub
        have hhj : h j ≠ 0 := by
          intro h0
          have hαj : α j (h j) = 2 := by rw [C.lin.pair j j]; simp [CartanMatrix.A]
          rw [h0, map_zero] at hαj
          exact (ZMod.prime_ne_zero p 2 hp2) hαj.symm
        exact (smul_eq_zero.mp hz).resolve_right hhj
      rw [Fintype.linearCombination_apply, map_sum] at hα0
      simp only [map_smul, C.lin.pair, smul_eq_mul] at hα0
      calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k
          = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = 0 := hα0
    let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
    have hφd : Fintype.linearCombination (ZMod p) h d = 0 := by
      rw [Fintype.linearCombination_apply]
      simpa [d] using hrel
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one d c
      (fun j => l04fD5_A_mul_d (p := p) (N := N) C.lin.p_dvd j) hcA (by
        intro hzero
        have h1 := congrFun hzero ⟨0, by omega⟩
        simp [d] at h1)
    have hzero : Fintype.linearCombination (ZMod p) h c = 0 := by rw [hl, map_smul, hφd, smul_zero]
    exact hzero
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq R F
  rw [hRF, finrank_bot, add_zero] at hsup
  have hsup_le : Module.finrank (ZMod p) ↥(R ⊔ F) ≤ Module.finrank (ZMod p) V := Submodule.finrank_le _
  have hFle : Module.finrank (ZMod p) ↥F ≤ 2 := by
    have hle : (N - 2) + Module.finrank (ZMod p) ↥F ≤ N := by
      calc (N - 2) + Module.finrank (ZMod p) ↥F
          = Module.finrank (ZMod p) ↥(R ⊔ F) := by rw [hsup, hdimR']
        _ ≤ Module.finrank (ZMod p) V := hsup_le
        _ ≤ N := C.lin.dim_le
    omega
  have hFdim : Module.finrank (ZMod p) ↥F = 2 := le_antisymm hFle C.two
  have htopdim : Module.finrank (ZMod p) ↥(R ⊔ F) = N := by
    rw [hsup, hdimR', hFdim]
    omega
  have hVdim : Module.finrank (ZMod p) V = N := by
    have h1 : Module.finrank (ZMod p) ↥(R ⊔ F) ≤ Module.finrank (ZMod p) V := hsup_le
    have h2 : Module.finrank (ZMod p) V ≤ N := C.lin.dim_le
    omega
  have htop : R ⊔ F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [htopdim, hVdim])
  exact ⟨⟨hTlow, hTup⟩, hVdim, by simpa [F] using hFdim, by simpa [R, F] using htop⟩

end CFSG.StandardType

end
