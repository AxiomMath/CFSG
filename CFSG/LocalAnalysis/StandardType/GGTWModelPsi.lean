module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTM_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

private theorem l05nTM_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
    (j : Fin (N - 1)) :
    ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) *
      (((k : ℕ) + 1 : ℕ) : ZMod p) = 0 := by
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  change ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0
  rw [cartanA_row d j]
  have hc' : ∀ m : ℕ, (fun m => if hm : m < N - 1 then d ⟨m, hm⟩ else 0) m =
      (if m < N - 1 then (((m : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
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
      convert l05nTM_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

private lemma l05nTM_sum_ggTWh {p N : ℕ} :
    (∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • ggTWh p N i) = 0 := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ggTWh, Pi.zero_apply]
  by_cases hj : j.val + 2 = N
  · simp [hj]
  · simp only [hj, if_false]
    have hjlt : j.val + 1 < N - 1 := by have := j.isLt; omega
    let i0 : Fin (N - 1) := ⟨0, by omega⟩
    let i1 : Fin (N - 1) := ⟨j.val+1, hjlt⟩
    have hne : i0 ≠ i1 := by
      intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    have hpt : ∀ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) *
        (if i.val = 0 then -(((j.val:ℕ):ZMod p) + 2) else if j.val + 1 = i.val then 1 else 0)
        = (if i = i0 then -(((j.val:ℕ):ZMod p) + 2) else 0)
          + (if i = i1 then (((j.val:ℕ):ZMod p) + 2) else 0) := by
      intro i
      by_cases h0 : i.val = 0
      · have hi0 : i = i0 := Fin.ext (by simpa [i0] using h0)
        subst hi0
        have hc : ¬ (j.val + 1 = 0) := by omega
        simp only [Fin.val_mk, if_pos rfl, if_neg hc, if_neg hne, if_neg (Ne.symm hne)]
        norm_num
      · have hi0 : i ≠ i0 := by
          intro h; exact h0 (by simpa [i0] using congrArg Fin.val h)
        by_cases h1 : i.val = j.val + 1
        · have hi1 : i = i1 := Fin.ext (by simpa [i1] using h1)
          subst hi1
          have hc0 : ¬ (i1.val = 0) := by simp [i1]
          have hc1 : j.val + 1 = i1.val := by simp [i1]
          simp only [hc0, hc1, if_false, if_true, if_neg hne, if_neg (Ne.symm hne)]
          have hv1 : (i1.val : ℕ) = j.val + 1 := rfl
          rw [hv1]
          push_cast
          ring
        · have hi1 : i ≠ i1 := by
            intro h; exact h1 (by simpa [i1] using congrArg Fin.val h)
          have hcond1 : ¬ (j.val + 1 = i.val) := by omega
          rw [if_neg h0, if_neg hcond1, if_neg hi0, if_neg hi1]
          ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [i0, i1, hne]

@[expose] noncomputable def l05nTMψ {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (x : V) :
    (Fin (N - 1) → ZMod p) →ₗ[ZMod p] V :=
  ∑ k : Fin (N - 1), (LinearMap.proj k).smulRight
    (if hk : k.val + 2 = N then x else h ⟨k.val + 1, by have := k.isLt; omega⟩)

private lemma l05nTMψ_apply {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (x : V) (w : Fin (N - 1) → ZMod p) :
    l05nTMψ h x w = ∑ k : Fin (N - 1), w k •
      (if hk : k.val + 2 = N then x else h ⟨k.val + 1, by have := k.isLt; omega⟩) := by
  simp [l05nTMψ, Finset.sum_apply, LinearMap.smulRight_apply]

lemma l05nTMψ_single {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (x : V) (k : Fin (N - 1)) :
    l05nTMψ h x (Pi.single k (1 : ZMod p)) =
      (if hk : k.val + 2 = N then x else h ⟨k.val + 1, by have := k.isLt; omega⟩) := by
  rw [l05nTMψ_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

lemma l05nTM_x_single {p N : ℕ} (hN : 5 ≤ N) :
    ggTWx p N = Pi.single ⟨N - 2, by omega⟩ (1 : ZMod p) := by
  funext j
  by_cases hj : j = ⟨N - 2, by omega⟩
  · subst hj
    simp only [ggTWx, Fin.val_mk]
    rw [if_pos (show N - 2 + 2 = N by omega), Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, ggTWx]
    rw [if_neg]
    intro h
    apply hj
    ext
    simp only [Fin.val_mk]
    omega

private lemma l05nTM_ggTWh_single {p N : ℕ} (i : Fin (N - 1)) (hi : i.val ≠ 0) :
    ggTWh p N i = Pi.single ⟨i.val - 1, by have := i.isLt; omega⟩ (1 : ZMod p) := by
  funext j
  by_cases hj : j = ⟨i.val - 1, by have := i.isLt; omega⟩
  · subst hj
    rw [Pi.single_eq_same, ggTWh]
    have h1 : ¬ (i.val - 1 + 2 = N) := by have := i.isLt; omega
    rw [if_neg h1, if_neg hi]
    have h2 : (i.val - 1 + 1 = i.val) := by omega
    simp [h2]
  · rw [Pi.single_eq_of_ne hj, ggTWh]
    by_cases hlast : j.val + 2 = N
    · simp [hlast]
    · rw [if_neg hlast, if_neg hi]
      rw [if_neg]
      intro hv
      apply hj
      ext
      simp only [Fin.val_mk]
      omega

lemma l05nTM_alpha_coeff {p N : ℕ} (i k : Fin (N - 1)) (hk : ¬ k.val + 2 = N) :
    ggTWα p N i k =
      (CartanMatrix.A (N - 1) i
        ⟨k.val + 1, by have h1 := k.isLt; have h2 := hk; omega⟩ : ZMod p) := by
  have hk' : k.val + 2 ≠ N := hk
  simp only [ggTWα, CartanMatrix.A, Matrix.of_apply, Fin.val_mk, Fin.ext_iff, hk', if_false]
  split_ifs <;> (first | rfl | (exfalso; omega) | norm_num)

private lemma l05nTM_kernel_eq_zero {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (hN : 2 ≤ N) (F : GGDepAFrame p N h α x) (c : Fin (N - 1) → ZMod p)
    (hc : ∑ i : Fin (N - 1), c i • h i = 0) (h0 : c ⟨0, by omega⟩ = 0) : c = 0 := by
  classical
  by_cases hc0 : c = 0
  · exact hc0
  · let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
    have hcA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
      intro j
      have hh := congrArg (α j) hc
      simp only [map_sum, map_smul, F.pair, smul_eq_mul, map_zero] at hh
      calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k
          = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = 0 := hh
    have hdA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0 :=
      fun j => l05nTM_A_mul_d F.dvd j
    have hd0 : d ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, by omega⟩
      simp [d] at this
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one d c hdA hcA hd0
    have hl0 : l = 0 := by
      have hcong := congrFun hl ⟨0, by omega⟩
      simp only [Pi.smul_apply, smul_eq_mul, d, Fin.val_mk, Nat.cast_zero, zero_add,
        Nat.cast_one, mul_one] at hcong
      rw [h0] at hcong
      exact hcong.symm
    subst hl0
    simpa using hl

lemma l05nTM_finRotate_succ {N : ℕ} (k : Fin (N - 1)) (hk : ¬ k.val + 2 = N) :
    (finRotate (N - 1)) k = ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  have hlt : k.val + 1 < N - 1 := by have := k.isLt; omega
  ext
  simp [finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt hlt]

private lemma l05nTM_finRotate_symm_zero {N : ℕ} (hN : 2 ≤ N) :
    (finRotate (N - 1)).symm ⟨0, by omega⟩ = ⟨N - 2, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [finRotate_apply, Fin.val_add]
  have h : N - 2 + 1 = N - 1 := by omega
  rw [h, Nat.mod_self]

lemma l05nTMψ_ggTWh_succ {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (x : V) (i : Fin (N - 1)) (hi : i.val ≠ 0) :
    l05nTMψ h x (ggTWh p N i) = h i := by
  rw [l05nTM_ggTWh_single i hi, l05nTMψ_single]
  have hk : ¬ ((⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (N - 1)).val + 2 = N) := by
    simp only [Fin.val_mk]; have := i.isLt; omega
  rw [dif_neg hk]
  congr 1
  ext
  simp only [Fin.val_mk]
  omega

lemma l05nTM_alpha_ψ {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (i : Fin (N - 1)) (w : Fin (N - 1) → ZMod p) :
    α i (l05nTMψ h x w) = ggTWdot (ggTWα p N i) w := by
  rw [l05nTMψ_apply, ggTWdot, map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, smul_eq_mul]
  have hc : α i (if hk : k.val + 2 = N then x else
      h ⟨k.val + 1, by have := k.isLt; omega⟩) = ggTWα p N i k := by
    by_cases hk : k.val + 2 = N
    · rw [dif_pos hk, F.x_ker i]
      simp [ggTWα, hk]
    · rw [dif_neg hk, F.pair, ← l05nTM_alpha_coeff i k hk]
  rw [hc, mul_comm]

lemma l05nTM_ψ_ggTWh_zero {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) :
    l05nTMψ h x (ggTWh p N ⟨0, by omega⟩) = h ⟨0, by omega⟩ := by
  let i0 : Fin (N - 1) := ⟨0, by omega⟩
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hrel := (ggDepA_relation F).1
  have hmod := l05nTM_sum_ggTWh (p := p) (N := N)
  have hrel_split : d i0 • h i0 + (∑ i ∈ (Finset.univ.erase i0), d i • h i) = 0 := by
    have he := Finset.add_sum_erase (Finset.univ : Finset (Fin (N - 1)))
      (fun i => d i • h i) (Finset.mem_univ i0)
    rw [hrel] at he
    exact he
  have hmod_split : d i0 • ggTWh p N i0 +
      (∑ i ∈ (Finset.univ.erase i0), d i • ggTWh p N i) = 0 := by
    have he := Finset.add_sum_erase (Finset.univ : Finset (Fin (N - 1)))
      (fun i => d i • ggTWh p N i) (Finset.mem_univ i0)
    rw [hmod] at he
    exact he
  have hd0 : d i0 = 1 := by simp [d, i0]
  rw [hd0, one_smul] at hrel_split hmod_split
  have hmap := congrArg (l05nTMψ h x) hmod_split
  simp only [map_add, map_zero, map_sum, map_smul] at hmap
  have hS : (∑ i ∈ (Finset.univ.erase i0), d i • l05nTMψ h x (ggTWh p N i))
      = ∑ i ∈ (Finset.univ.erase i0), d i • h i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hine : i ≠ i0 := (Finset.mem_erase.mp hi).1
    have hival : i.val ≠ 0 := by
      intro hv; exact hine (Fin.ext (by simpa [i0] using hv))
    rw [l05nTMψ_ggTWh_succ h x i hival]
  rw [hS] at hmap
  have hA : l05nTMψ h x (ggTWh p N i0) =
      - (∑ i ∈ Finset.univ.erase i0, d i • h i) := eq_neg_of_add_eq_zero_left hmap
  have hB : h i0 = - (∑ i ∈ (Finset.univ.erase i0), d i • h i) :=
    eq_neg_of_add_eq_zero_left hrel_split
  exact hA.trans hB.symm

private lemma l05nTM_ψ_ker {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (w : Fin (N - 1) → ZMod p) (hw : l05nTMψ h x w = 0) : w = 0 := by
  classical
  obtain ⟨hrel, hxH, -⟩ := ggDepA_relation F
  let iL : Fin (N - 1) := ⟨N - 2, by omega⟩
  let i0 : Fin (N - 1) := ⟨0, by omega⟩
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let c : Fin (N - 1) → V := fun k =>
    if hk : k.val + 2 = N then x else h ⟨k.val + 1, by have := k.isLt; omega⟩
  have hsum : ∑ k : Fin (N - 1), w k • c k = 0 := by
    rw [← l05nTMψ_apply]; exact hw
  have hcL : c iL = x := by
    simp only [c, iL]
    rw [dif_pos (show N - 2 + 2 = N by omega)]
  have hdecomp : w iL • x + (∑ k ∈ (Finset.univ.erase iL), w k • c k) = 0 := by
    have he := Finset.add_sum_erase (Finset.univ : Finset (Fin (N - 1)))
      (fun k => w k • c k) (Finset.mem_univ iL)
    rw [hsum] at he
    rw [← hcL]
    exact he
  have hrestH : (∑ k ∈ (Finset.univ.erase iL), w k • c k) ∈ H := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    have hkne : k ≠ iL := (Finset.mem_erase.mp hk).1
    have hknot : ¬ (k.val + 2 = N) := by
      intro hcon
      apply hkne
      ext
      simp only [iL, Fin.val_mk]
      omega
    simp only [c, dif_neg hknot]
    exact Submodule.subset_span ⟨⟨k.val + 1, by have := k.isLt; omega⟩, rfl⟩
  have hwL : w iL = 0 := by
    by_contra hne
    have hxmem : x ∈ H := by
      have hmem : (w iL)⁻¹ • (-(∑ k ∈ (Finset.univ.erase iL), w k • c k)) ∈ H :=
        Submodule.smul_mem H _ (neg_mem hrestH)
      have hux : w iL • x = -(∑ k ∈ (Finset.univ.erase iL), w k • c k) :=
        eq_neg_of_add_eq_zero_left hdecomp
      have heq : x = (w iL)⁻¹ • (-(∑ k ∈ (Finset.univ.erase iL), w k • c k)) := by
        calc x = (w iL)⁻¹ • (w iL • x) := by
              rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = (w iL)⁻¹ • (-(∑ k ∈ (Finset.univ.erase iL), w k • c k)) := by rw [hux]
      rwa [heq]
    exact hxH hxmem
  have hrest0 : ∑ k ∈ (Finset.univ.erase iL), w k • c k = 0 := by
    have h := hdecomp
    rw [hwL, zero_smul, zero_add] at h
    exact h
  let σ := finRotate (N - 1)
  let cf : Fin (N - 1) → ZMod p := fun i => w (σ.symm i)
  have hcf0 : cf i0 = 0 := by
    simp only [cf, i0]
    rw [l05nTM_finRotate_symm_zero (N := N) (by omega)]
    exact hwL
  have hcomp : ∑ k : Fin (N - 1), w k • h (σ k) = ∑ i, cf i • h i := by
    have hc := Equiv.sum_comp σ (fun i => w (σ.symm i) • h i)
    simpa [cf] using hc
  have hleft : ∑ k : Fin (N - 1), w k • h (σ k) =
      ∑ k ∈ (Finset.univ.erase iL), w k • c k := by
    have hadd := Finset.add_sum_erase (Finset.univ : Finset (Fin (N - 1)))
      (fun k => w k • h (σ k)) (Finset.mem_univ iL)
    have hfL : w iL • h (σ iL) = 0 := by rw [hwL, zero_smul]
    have herase : ∀ k ∈ (Finset.univ.erase iL), w k • h (σ k) = w k • c k := by
      intro k hk
      have hkne : k ≠ iL := (Finset.mem_erase.mp hk).1
      have hknot : ¬ (k.val + 2 = N) := by
        intro hcon
        apply hkne
        ext
        simp only [iL, Fin.val_mk]
        omega
      simp only [c, dif_neg hknot]
      congr 1
      rw [l05nTM_finRotate_succ k hknot]
    calc ∑ k : Fin (N - 1), w k • h (σ k)
        = w iL • h (σ iL) + ∑ k ∈ (Finset.univ.erase iL), w k • h (σ k) := hadd.symm
      _ = 0 + ∑ k ∈ (Finset.univ.erase iL), w k • c k := by
            rw [hfL, Finset.sum_congr rfl herase]
      _ = ∑ k ∈ (Finset.univ.erase iL), w k • c k := by rw [zero_add]
  have hcfsum : ∑ i, cf i • h i = 0 := by
    rw [← hcomp]
    exact hleft.trans hrest0
  have hcf : cf = 0 := l05nTM_kernel_eq_zero (N := N) (by omega) F cf hcfsum hcf0
  funext k
  have := congrFun hcf (σ k)
  simpa [cf] using this

lemma l05nTM_ψ_inj {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) :
    Function.Injective (l05nTMψ (p := p) (N := N) h x) := by
  intro a b hab
  have hzero : l05nTMψ h x (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h := l05nTM_ψ_ker hN F (a - b) hzero
  exact sub_eq_zero.mp h

end CFSG.StandardType
