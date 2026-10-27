module

public import CFSG.LocalAnalysis.StandardType.ZS.FrameSigns
public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
public import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U]

local instance (priority := high) zff_zmodAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup

instance finite_linearEquiv : Finite (U ≃ₗ[ZMod p] U) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective

private lemma zff_orderOf_le_three_cases {G : Type*} [Group G] [hG : Finite G] {x : G}
    (h : orderOf x ≤ 3) : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 := by
  have hpos : 0 < orderOf x := @orderOf_pos G _ hG x
  omega

theorem eq_or_pairings_of_orderOf_le_three (hp : p ≠ 2) {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (h : orderOf (reflection hu * reflection hv) ≤ 3) :
    reflection hu = reflection hv ∨ (φ v = 0 ∧ ψ u = 0) ∨ φ v * ψ u = 1 := by
  rcases zff_orderOf_le_three_cases h with h1 | h2 | h3
  · left
    have hmul : reflection hu * reflection hv = 1 := orderOf_eq_one_iff.mp h1
    have hru : reflection hu * reflection hu = 1 := by
      rw [← Module.reflection_inv hu]
      exact inv_mul_cancel _
    calc reflection hu = reflection hu * 1 := (mul_one _).symm
      _ = reflection hu * (reflection hu * reflection hv) := by rw [hmul]
      _ = (reflection hu * reflection hu) * reflection hv := by rw [mul_assoc]
      _ = reflection hv := by rw [hru, one_mul]
  · right; left
    exact eq_zero_of_orderOf_eq_two hp hu hv h2
  · right; right
    exact mul_eq_one_of_orderOf_eq_three hp hu hv h3

omit [Module.Finite (ZMod p) U] in
private lemma zff_range_reflection_sub_id (hp : p ≠ 2) {a : U} {φ : Dual (ZMod p) U}
    (hφ : φ a = 2) :
    LinearMap.range ((reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) =
      Submodule.span (ZMod p) {a} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha : a ≠ 0 := fun h => h2 (by rw [h, map_zero] at hφ; exact hφ.symm)
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change reflection hφ v - v ∈ Submodule.span (ZMod p) {a}
    have hv : reflection hφ v - v = -(φ v • a) := by
      rw [reflection_apply]
      abel
    rw [hv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v)
      (Submodule.subset_span (Set.mem_singleton a)))
  · rw [Submodule.span_singleton_le_iff_mem]
    have hmem : -a ∈ LinearMap.range ((reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) := by
      refine ⟨(2 : ZMod p)⁻¹ • a, ?_⟩
      have hφv : φ ((2 : ZMod p)⁻¹ • a) = 1 := by
        rw [map_smul, hφ, smul_eq_mul, inv_mul_cancel₀ h2]
      change reflection hφ ((2 : ZMod p)⁻¹ • a) - (2 : ZMod p)⁻¹ • a = -a
      rw [show reflection hφ ((2 : ZMod p)⁻¹ • a) - (2 : ZMod p)⁻¹ • a
          = -(φ ((2 : ZMod p)⁻¹ • a) • a) by rw [reflection_apply]; abel]
      rw [hφv, one_smul]
    simpa using Submodule.neg_mem _ hmem

omit [Module.Finite (ZMod p) U] in
private lemma zff_exists_smul_of_reflection_eq (hp : p ≠ 2) {a b : U}
    {φ ψ : Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : reflection hφ = reflection hψ) : ∃ c : ZMod p, b = c • a := by
  have hspan : Submodule.span (ZMod p) {b} = Submodule.span (ZMod p) {a} := by
    rw [← zff_range_reflection_sub_id hp hψ, ← zff_range_reflection_sub_id hp hφ, h]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.mem_span_singleton_self b)
  exact ⟨c, hc.symm⟩

omit [Module.Finite (ZMod p) U] in
private lemma zff_reflection_eq_of_smul {a b : U} {φ ψ : Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) {c : ZMod p} (hc : c ≠ 0)
    (hb : b = c • a) (hψφ : ψ = c⁻¹ • φ) : reflection hψ = reflection hφ := by
  apply LinearEquiv.ext
  intro v
  rw [reflection_apply v hψ, reflection_apply v hφ, hb]
  have hψv : ψ v = c⁻¹ * φ v := by
    rw [hψφ, LinearMap.smul_apply, smul_eq_mul]
  have hcoef : (c⁻¹ * φ v) * c = φ v := by
    rw [mul_assoc, mul_comm (φ v) c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hψv, smul_smul, hcoef]

private lemma zff_exists_frame (hp : p ≠ 2) (hn : Module.finrank (ZMod p) U = 4)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hr : ∀ i, IsRefl p (r i))
    (hcomm : Pairwise fun i j => Commute (r i) (r j)) (hinj : Function.Injective r) :
    ∃ (b : Basis (Fin 4) (ZMod p) U) (φ : Fin 4 → Dual (ZMod p) U)
      (hφ : ∀ i, φ i (b i) = 2),
      (∀ i, r i = reflection (hφ i)) ∧
      (∀ i j, i ≠ j → φ i (b j) = 0) ∧
      (∀ i, φ i = (2 : ZMod p) • b.coord i) := by
  choose e φ hφe hr_eq using fun i => (isRefl_iff hp (r i)).mp (hr i)
  have hcomm' : Pairwise fun i j => Commute (reflection (hφe i)) (reflection (hφe j)) := by
    intro i j hij
    rw [← hr_eq i, ← hr_eq j]
    exact hcomm hij
  have hne : Pairwise fun i j => reflection (hφe i) ≠ reflection (hφe j) := by
    intro i j hij heq
    exact hij (hinj (by rw [hr_eq i, hr_eq j, heq]))
  have hLI : LinearIndependent (ZMod p) e :=
    linearIndependent_of_pairwise_commute hp hφe hcomm' hne
  have hzero : ∀ i j, i ≠ j → φ i (e j) = 0 := by
    intro i j hij
    exact apply_eq_zero_of_commute hp (hφe i) (hφe j) (hcomm' hij) (hne hij)
  have hcard : Fintype.card (Fin 4) = Module.finrank (ZMod p) U := by
    rw [Fintype.card_fin, hn]
  let b : Basis (Fin 4) (ZMod p) U := basisOfLinearIndependentOfCardEqFinrank hLI hcard
  have hb : ∀ i, b i = e i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard) i
  have hφb : ∀ i, φ i (b i) = 2 := fun i => by rw [hb i]; exact hφe i
  have hcoord : ∀ i, φ i = (2 : ZMod p) • b.coord i := by
    intro i
    refine b.ext (fun j => ?_)
    rw [LinearMap.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · subst j
      rw [hφb i, Basis.coord_apply, Basis.repr_self]
      simp
    · have hφij : φ i (b j) = 0 := by
        rw [hb j]
        exact hzero i j (Ne.symm hji)
      rw [hφij, Basis.coord_apply, Basis.repr_self]
      simp [hji]
  have hr_eq' : ∀ i, r i = reflection (hφb i) := by
    intro i
    rw [hr_eq i]
    apply LinearEquiv.ext
    intro v
    rw [reflection_apply v (hφe i), reflection_apply v (hφb i), hb i]
  exact ⟨b, φ, hφb, hr_eq', fun i j hij => by rw [hb j]; exact hzero i j hij, hcoord⟩

private lemma zff_natCast_eq_four {k : ℕ} (hp : p ≠ 2) (hk : (k : ZMod p) = 4)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) : k = 4 ∨ (p = 3 ∧ k = 1) := by
  interval_cases k
  · right
    refine ⟨?_, rfl⟩
    have h3 : (3 : ZMod p) = 0 := by
      have h := congrArg (fun z : ZMod p => z - 1) hk
      rw [show (4 : ZMod p) - 1 = 3 by norm_num] at h
      simp only [Nat.cast_one, sub_self] at h
      exact h.symm
    have hdvd : p ∣ 3 :=
      Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff 3 0 p).mp (by simpa using h3))
    have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  · exfalso
    have h2 : (2 : ZMod p) = 0 := by
      have h := congrArg (fun z : ZMod p => z - 2) hk
      rw [show (4 : ZMod p) - 2 = 2 by norm_num] at h
      norm_num at h
      exact h.symm
    exact (ZMod.prime_ne_zero p 2 hp) h2
  · exfalso
    have h1 : (1 : ZMod p) = 0 := by
      have h := congrArg (fun z : ZMod p => z - 3) hk
      rw [show (4 : ZMod p) - 3 = 1 by norm_num] at h
      norm_num at h
    exact one_ne_zero h1
  · exact Or.inl rfl

private lemma zff_pairing_alt (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Basis (Fin 4) (ZMod p) U} {φ : Fin 4 → Dual (ZMod p) U}
    (hφ : ∀ i, φ i (b i) = 2) (hφeq : ∀ i, φ i = (2 : ZMod p) • b.coord i)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hr : ∀ i, r i = reflection (hφ i))
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (hs : s = reflection hψ) (hrA : ∀ i, r i ∈ A) (hsA : s ∈ A)
    (hrefl_r : ∀ i, IsRefl p (r i)) (hrefl_s : IsRefl p s)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    (hsne : ∀ i, s ≠ r i) :
    ∀ i, (b.coord i u = 0 ∧ ψ (b i) = 0) ∨ (2 * b.coord i u) * ψ (b i) = 1 := by
  intro i
  have hle : orderOf (reflection (hφ i) * reflection hψ) ≤ 3 := by
    have := h3 (r i) (hrA i) s hsA (hrefl_r i) hrefl_s
    simpa [hr i, hs] using this
  rcases eq_or_pairings_of_orderOf_le_three hp (hφ i) hψ hle with heq | hzero | hone
  · exfalso
    apply hsne i
    rw [hs, hr i]
    exact heq.symm
  · left
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    refine ⟨?_, hzero.2⟩
    have h1 := hzero.1
    rw [hφeq i, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left h2
  · right
    have h1 := hone
    rw [hφeq i, LinearMap.smul_apply, smul_eq_mul] at h1
    exact h1

omit [Module.Finite (ZMod p) U] in
private lemma zff_pairing_card_eq (hp : p ≠ 2) {b : Basis (Fin 4) (ZMod p) U} {u : U}
    {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (halt : ∀ i, (b.coord i u = 0 ∧ ψ (b i) = 0) ∨ (2 * b.coord i u) * ψ (b i) = 1) :
    let J : Finset (Fin 4) := Finset.univ.filter (fun i => b.coord i u ≠ 0)
    (J.card : ZMod p) = 4 := by
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => b.coord i u ≠ 0)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hexp : u = ∑ i, b.coord i u • b i := by
    simp [Basis.coord_apply]
  have hsum : ∑ i, b.coord i u * ψ (b i) = 2 := by
    have h : ψ (∑ i, b.coord i u • b i) = 2 := by
      rw [← hexp]
      exact hψ
    rw [map_sum] at h
    simpa [map_smul, smul_eq_mul] using h
  have hterm : ∀ i, b.coord i u * ψ (b i) =
      if b.coord i u ≠ 0 then (2 : ZMod p)⁻¹ else 0 := by
    intro i
    rcases halt i with ⟨hx, _⟩ | hprod
    · rw [hx, zero_mul]
      simp
    · have hxy : b.coord i u * ψ (b i) = (2 : ZMod p)⁻¹ := by
        have h := hprod
        rw [mul_assoc] at h
        exact eq_inv_of_mul_eq_one_right h
      have hx : b.coord i u ≠ 0 := by
        intro hx0
        rw [hx0, zero_mul] at hxy
        exact (inv_ne_zero h2) hxy.symm
      rw [hxy, if_pos hx]
  have hsumJ : (J.card : ZMod p) * (2 : ZMod p)⁻¹ = 2 := by
    calc (J.card : ZMod p) * (2 : ZMod p)⁻¹
        = ∑ i ∈ J, (2 : ZMod p)⁻¹ := by simp [J]
      _ = ∑ i, if b.coord i u ≠ 0 then (2 : ZMod p)⁻¹ else 0 := by
            simp only [J, Finset.sum_filter]
      _ = ∑ i, b.coord i u * ψ (b i) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact (hterm i).symm
      _ = 2 := hsum
  have hk : (J.card : ZMod p) = 4 := by
    have hmul : (J.card : ZMod p) * (2 : ZMod p)⁻¹ * 2 = 2 * 2 := by rw [hsumJ]
    calc (J.card : ZMod p) = (J.card : ZMod p) * (2 : ZMod p)⁻¹ * 2 := by
          rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
      _ = 2 * 2 := hmul
      _ = 4 := by norm_num
  exact hk

omit [Module.Finite (ZMod p) U] in
private lemma zff_pairing_card (hp : p ≠ 2) {b : Basis (Fin 4) (ZMod p) U} {u : U}
    {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (halt : ∀ i, (b.coord i u = 0 ∧ ψ (b i) = 0) ∨ (2 * b.coord i u) * ψ (b i) = 1) :
    let J : Finset (Fin 4) := Finset.univ.filter (fun i => b.coord i u ≠ 0)
    (J.card : ZMod p) = 4 ∧ 1 ≤ J.card ∧ J.card ≤ 4 := by
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => b.coord i u ≠ 0)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hexp : u = ∑ i, b.coord i u • b i := by
    simp [Basis.coord_apply]
  have hk : (J.card : ZMod p) = 4 := zff_pairing_card_eq hp hψ halt
  have hcard4 : J.card ≤ 4 := by
    have := Finset.card_le_card (Finset.filter_subset (fun i => b.coord i u ≠ 0) Finset.univ)
    simpa [J] using this
  have hcard1 : 1 ≤ J.card := by
    by_contra h
    have h0 : J.card = 0 := Nat.eq_zero_of_not_pos h
    have hu0 : u = 0 := by
      rw [hexp]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hi : b.coord i u = 0 := by
        by_contra hne
        have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
        have : 0 < J.card := Finset.card_pos.mpr ⟨i, hiJ⟩
        omega
      rw [hi, zero_smul]
    have hzero : ψ u = 0 := by rw [hu0, map_zero]
    rw [hψ] at hzero
    exact h2 hzero
  exact ⟨hk, hcard1, hcard4⟩

omit [Module.Finite (ZMod p) U] in
private lemma zff_eq_of_unique_coord (hp3 : p = 3) {b : Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Dual (ZMod p) U} (hφ : ∀ i, φ i (b i) = 2)
    (hφeq : ∀ i, φ i = (2 : ZMod p) • b.coord i)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hr : ∀ i, r i = reflection (hφ i))
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (hs : s = reflection hψ) {i : Fin 4} (hx : b.coord i u ≠ 0)
    (hxj : ∀ j, j ≠ i → b.coord j u = 0)
    (hyj : ∀ j, j ≠ i → ψ (b j) = 0)
    (hprod_i : (2 * b.coord i u) * ψ (b i) = 1) : s = r i := by
  have hexp : u = ∑ j, b.coord j u • b j := by
    simp [Basis.coord_apply]
  have hui : u = b.coord i u • b i := by
    conv_lhs => rw [hexp]
    exact Finset.sum_eq_single i (fun j _ hj => by rw [hxj j hj, zero_smul])
      (fun hi' => absurd (Finset.mem_univ i) hi')
  have h2inv : (2 : ZMod p)⁻¹ = 2 := by
    have h4 : (4 : ZMod p) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff' 4 1 p).mpr (by rw [hp3])
      simpa using h
    have h22 : (2 : ZMod p) * 2 = 1 := by
      rw [show (2 : ZMod p) * 2 = 4 by norm_num]
      exact h4
    exact inv_eq_of_mul_eq_one_right h22
  have hy : ψ (b i) = (b.coord i u)⁻¹ * 2 := by
    have hxy : b.coord i u * ψ (b i) = (2 : ZMod p)⁻¹ := by
      have h := hprod_i
      rw [mul_assoc] at h
      exact eq_inv_of_mul_eq_one_right h
    rw [h2inv] at hxy
    calc ψ (b i) = (b.coord i u)⁻¹ * (b.coord i u * ψ (b i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
      _ = (b.coord i u)⁻¹ * 2 := by rw [hxy]
  have hψφ : ψ = (b.coord i u)⁻¹ • φ i := by
    apply b.ext
    intro j
    rw [LinearMap.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · subst j
      rw [hy, hφ i]
    · have hcj : (b.coord i) (b j) = 0 := by
        rw [Basis.coord_apply, Basis.repr_self]
        simp [hji]
      have hφj : φ i (b j) = 0 := by
        rw [hφeq i, LinearMap.smul_apply, hcj, smul_zero]
      rw [hyj j hji, hφj, mul_zero]
  rw [hs, hr i]
  exact zff_reflection_eq_of_smul (hφ i) hψ hx hui hψφ

private lemma zff_coords_ne_zero (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : Basis (Fin 4) (ZMod p) U} {φ : Fin 4 → Dual (ZMod p) U}
    (hφ : ∀ i, φ i (b i) = 2) (hφeq : ∀ i, φ i = (2 : ZMod p) • b.coord i)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hr : ∀ i, r i = reflection (hφ i))
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (hs : s = reflection hψ) (hrA : ∀ i, r i ∈ A) (hsA : s ∈ A)
    (hrefl_r : ∀ i, IsRefl p (r i)) (hrefl_s : IsRefl p s)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    (hsne : ∀ i, s ≠ r i) : ∀ i, b.coord i u ≠ 0 := by
  have halt := zff_pairing_alt hp hφ hφeq hr hψ hs hrA hsA hrefl_r hrefl_s h3 hsne
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => b.coord i u ≠ 0)
  have hcard := zff_pairing_card hp hψ halt
  have hk : (J.card : ZMod p) = 4 := hcard.1
  have hcard1 : 1 ≤ J.card := hcard.2.1
  have hcard4 : J.card ≤ 4 := hcard.2.2
  rcases zff_natCast_eq_four hp hk hcard1 hcard4 with h4 | ⟨hp3, h1⟩
  · intro i
    have hmem : i ∈ J := by
      by_contra hi
      have hsub : J ⊆ Finset.univ.erase i := by
        intro j hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact fun hji => hi (hji ▸ hj)
      have hle := Finset.card_le_card hsub
      simp at hle
      omega
    have hm : i ∈ (Finset.univ : Finset (Fin 4)).filter (fun i => b.coord i u ≠ 0) := by
      simpa [J] using hmem
    exact (Finset.mem_filter.mp hm).2
  · exfalso
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    have hx : b.coord i u ≠ 0 := by
      have : i ∈ J := by rw [hi]; simp
      have hm : i ∈ (Finset.univ : Finset (Fin 4)).filter (fun i => b.coord i u ≠ 0) := by
        simpa [J] using this
      exact (Finset.mem_filter.mp hm).2
    have hxj : ∀ j, j ≠ i → b.coord j u = 0 := by
      intro j hj
      have hnot : j ∉ J := by rw [hi]; simp [hj]
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
    have hyj : ∀ j, j ≠ i → ψ (b j) = 0 := by
      intro j hj
      rcases halt j with ⟨_, h⟩ | hprod
      · exact h
      · exfalso
        rw [hxj j hj, mul_zero, zero_mul] at hprod
        exact zero_ne_one hprod
    have hprod_i : (2 * b.coord i u) * ψ (b i) = 1 := by
      rcases halt i with ⟨hx0, _⟩ | hprod
      · exact absurd hx0 hx
      · exact hprod
    exact hsne i (zff_eq_of_unique_coord hp3 hφ hφeq hr hψ hs hx hxj hyj hprod_i)

omit [Module.Finite (ZMod p) U] in
private lemma zff_psi_coords {b : Basis (Fin 4) (ZMod p) U} {u : U} {ψ : Dual (ZMod p) U}
    (hx : ∀ i, b.coord i u ≠ 0)
    (halt : ∀ i, (b.coord i u = 0 ∧ ψ (b i) = 0) ∨
      (2 * b.coord i u) * ψ (b i) = 1) :
    ∀ i, ψ (b i) = (2 * b.coord i u)⁻¹ := by
  intro i
  rcases halt i with ⟨hx0, _⟩ | hprod
  · exact absurd hx0 (hx i)
  · exact eq_inv_of_mul_eq_one_right hprod

omit [Module.Finite (ZMod p) U] in
private lemma zff_rescaled_basis (hp : p ≠ 2) (hn : Module.finrank (ZMod p) U = 4)
    {b : Basis (Fin 4) (ZMod p) U} {u : U} {ψ : Dual (ZMod p) U}
    (hx : ∀ i, b.coord i u ≠ 0)
    (hy : ∀ i, ψ (b i) = (2 * b.coord i u)⁻¹) :
    ∃ bf : Basis (Fin 4) (ZMod p) U,
      (∀ i, bf i = b.coord i u • b i) ∧
      (∀ i, bf.coord i u = 1) ∧
      (∀ i, ψ (bf i) = (2 : ZMod p)⁻¹) ∧
      u = ∑ i, bf i := by
  let w : Fin 4 → (ZMod p)ˣ := fun i => Units.mk0 (b.coord i u) (hx i)
  let f : Fin 4 → U := fun i => (w i : ZMod p) • b i
  have hfLI : LinearIndependent (ZMod p) f := by
    have hfw : f = w • b := by funext i; rfl
    rw [hfw]
    exact b.linearIndependent.units_smul w
  have hcard : Fintype.card (Fin 4) = Module.finrank (ZMod p) U := by
    rw [Fintype.card_fin, hn]
  let bf : Basis (Fin 4) (ZMod p) U := basisOfLinearIndependentOfCardEqFinrank hfLI hcard
  have hbf : ∀ i, bf i = b.coord i u • b i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hfLI hcard) i
  have hu_sum : u = ∑ i, bf i := by
    have hexp : u = ∑ i, b.coord i u • b i := by
      simp [Basis.coord_apply]
    rw [hexp]
    simp [hbf]
  have hcoord_u : ∀ i, bf.coord i u = 1 := by
    intro i
    rw [hu_sum, map_sum]
    rw [Finset.sum_eq_single i]
    · rw [Basis.coord_apply, Basis.repr_self]
      simp
    · intro j _ hj
      rw [Basis.coord_apply, Basis.repr_self]
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹ := by
    intro i
    rw [hbf i, map_smul, smul_eq_mul, hy i]
    change (w i : ZMod p) * (2 * (w i : ZMod p))⁻¹ = (2 : ZMod p)⁻¹
    have hwi : (w i : ZMod p) ≠ 0 := (w i).ne_zero
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    rw [mul_inv]
    field_simp [hwi, h2]
  exact ⟨bf, hbf, hcoord_u, hψf, hu_sum⟩

private def zff_signUnit (a : ZMod p) (_h : a = 1 ∨ a = -1) : (ZMod p)ˣ :=
  if a = -1 then -1 else 1

private lemma zff_signUnit_val (a : ZMod p) (h : a = 1 ∨ a = -1) :
    (zff_signUnit a h : ZMod p) = a := by
  rw [zff_signUnit]
  by_cases ha : a = -1
  · rw [if_pos ha, ha]
    rfl
  · rw [if_neg ha]
    rcases h with h1 | hneg
    · exact h1.symm
    · exact absurd hneg ha

omit [Module.Finite (ZMod p) U] in
private lemma zff_r_eq_diagMap {b : Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Dual (ZMod p) U} (hφ : ∀ i, φ i (b i) = 2)
    (hφzero : ∀ i j, i ≠ j → φ i (b j) = 0) {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hr : ∀ i, r i = reflection (hφ i)) (i : Fin 4) :
    r i = diagMap p b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) := by
  apply LinearEquiv.ext
  intro v
  have hlin : ((r i : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      ((diagMap p b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) :
        U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by
    refine b.ext (fun k => ?_)
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap]
    rw [hr i, reflection_apply (b k) (hφ i),
      diagMap_apply_basis b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) k]
    by_cases hki : k = i
    · subst k
      rw [hφ i, if_pos rfl]
      module
    · rw [hφzero i k (Ne.symm hki), if_neg hki]
      simp
  exact congrArg (fun f : U →ₗ[ZMod p] U => f v) hlin

omit [Module.Finite (ZMod p) U] in
private lemma zff_diagMap_sign_mem {b : Basis (Fin 4) (ZMod p) U}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrA : ∀ i, r i ∈ A)
    (hrdiag : ∀ i, r i = diagMap p b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    {u : Fin 4 → (ZMod p)ˣ} (hu : ∀ i, u i = 1 ∨ u i = -1) :
    diagMap p b u ∈ A := by
  let u0 : Fin 4 → (ZMod p)ˣ := fun k => if k = 0 then u 0 else 1
  let u1 : Fin 4 → (ZMod p)ˣ := fun k => if k = 1 then u 1 else 1
  let u2 : Fin 4 → (ZMod p)ˣ := fun k => if k = 2 then u 2 else 1
  let u3 : Fin 4 → (ZMod p)ˣ := fun k => if k = 3 then u 3 else 1
  have hdecomp : u = u0 * u1 * u2 * u3 := by
    funext k
    fin_cases k <;> simp [u0, u1, u2, u3, Pi.mul_apply]
  have hfac : ∀ i : Fin 4, diagMap p b (fun k => if k = i then u i else 1) ∈ A := by
    intro i
    by_cases hui : u i = -1
    · have hfun : (fun k => if k = i then u i else 1) =
          (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) := by
        funext k
        by_cases hki : k = i <;> simp [hki, hui]
      rw [hfun, ← hrdiag i]
      exact hrA i
    · have hui1 : u i = 1 := by
        rcases hu i with h | h
        · exact h
        · exact absurd h hui
      have hfun : (fun k => if k = i then u i else 1) = 1 := by
        funext k
        by_cases hki : k = i <;> simp [hki, hui1]
      rw [hfun, diagMap_one]
      exact A.one_mem
  have hprod : diagMap p b u =
      diagMap p b u0 * diagMap p b u1 * diagMap p b u2 * diagMap p b u3 := by
    rw [hdecomp]
    simp only [diagMap_mul]
  rw [hprod]
  exact A.mul_mem (A.mul_mem (A.mul_mem (hfac 0) (hfac 1)) (hfac 2)) (hfac 3)

private lemma zff_signUnit_eq_one_or_neg (a : ZMod p) (h : a = 1 ∨ a = -1) :
    zff_signUnit a h = 1 ∨ zff_signUnit a h = -1 := by
  rw [zff_signUnit]
  by_cases ha : a = -1
  · right
    rw [if_pos ha]
  · left
    rw [if_neg ha]

private lemma zff_sign_eq_or_neg {a b : ZMod p} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    b = a ∨ b = -a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (by simp)
  · exact Or.inl rfl

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_apply {b : Basis (Fin 4) (ZMod p) U} {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin 4) :
    diagMap p b (fun j => zff_signUnit (ε j) (hε j)) (b i) = ε i • b i := by
  rw [diagMap_apply_basis, zff_signUnit_val]

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_mul_self {b : Basis (Fin 4) (ZMod p) U} {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    diagMap p b (fun j => zff_signUnit (ε j) (hε j)) *
      diagMap p b (fun j => zff_signUnit (ε j) (hε j)) = 1 := by
  let u : Fin 4 → (ZMod p)ˣ := fun j => zff_signUnit (ε j) (hε j)
  have hu : u * u = 1 := by
    ext i
    rcases zff_signUnit_eq_one_or_neg (ε i) (hε i) with h | h <;>
      simp [u, Pi.mul_apply, h]
  rw [diagMap_mul, hu, diagMap_one]

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_inv {b : Basis (Fin 4) (ZMod p) U} {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (diagMap p b (fun j => zff_signUnit (ε j) (hε j)))⁻¹ =
      diagMap p b (fun j => zff_signUnit (ε j) (hε j)) :=
  inv_eq_of_mul_eq_one_right (zff_wEps_mul_self hε)

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_mem {b : Basis (Fin 4) (ZMod p) U}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrA : ∀ i, r i ∈ A)
    (hrdiag : ∀ i, r i = diagMap p b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    diagMap p b (fun j => zff_signUnit (ε j) (hε j)) ∈ A :=
  zff_diagMap_sign_mem hrA hrdiag (fun i => zff_signUnit_eq_one_or_neg (ε i) (hε i))

private noncomputable def zff_coordPhi (bf : Basis (Fin 4) (ZMod p) U) (i : Fin 4) :
    Dual (ZMod p) U :=
  (2 : ZMod p) • bf.coord i

omit [Module.Finite (ZMod p) U] in
private lemma zff_coordPhi_self (bf : Basis (Fin 4) (ZMod p) U) (i : Fin 4) :
    zff_coordPhi bf i (bf i) = 2 := by
  rw [zff_coordPhi, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self]
  norm_num

private noncomputable def zff_coordRefl (bf : Basis (Fin 4) (ZMod p) U) (i : Fin 4) :
    U ≃ₗ[ZMod p] U :=
  reflection (zff_coordPhi_self bf i)

omit [Module.Finite (ZMod p) U] in
private lemma zff_coordRefl_apply (bf : Basis (Fin 4) (ZMod p) U) (i : Fin 4) (v : U) :
    zff_coordRefl bf i v = v - (2 * bf.coord i v) • bf i := by
  rw [zff_coordRefl, reflection_apply, zff_coordPhi, LinearMap.smul_apply, smul_eq_mul]

omit [Module.Finite (ZMod p) U] in
private lemma zff_diagMap_bf_eq {b bf : Basis (Fin 4) (ZMod p) U} {x : Fin 4 → ZMod p}
    (hx : ∀ i, x i ≠ 0) (hbf : ∀ i, bf i = x i • b i) (u : Fin 4 → (ZMod p)ˣ) :
    diagMap p bf u = diagMap p b u := by
  apply LinearEquiv.ext
  intro v
  have hlin : ((diagMap p bf u : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      ((diagMap p b u : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by
    refine b.ext (fun k => ?_)
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, diagMap_apply_basis]
    have hb : b k = (x k)⁻¹ • bf k := by
      rw [hbf k, smul_smul, inv_mul_cancel₀ (hx k), one_smul]
    conv_lhs =>
      rw [hb, map_smul, diagMap_apply_basis]
    rw [hb, smul_smul, mul_comm ((x k)⁻¹) (u k : ZMod p), smul_smul]
  exact congrArg (fun f : U →ₗ[ZMod p] U => f v) hlin

omit [Module.Finite (ZMod p) U] in
private lemma zff_r_eq_diagMap_bf {b bf : Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Dual (ZMod p) U} (hφ : ∀ i, φ i (b i) = 2)
    (hφzero : ∀ i j, i ≠ j → φ i (b j) = 0) {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hr : ∀ i, r i = reflection (hφ i)) {x : Fin 4 → ZMod p} (hx : ∀ i, x i ≠ 0)
    (hbf : ∀ i, bf i = x i • b i) (i : Fin 4) :
    r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) := by
  rw [zff_diagMap_bf_eq hx hbf]
  exact zff_r_eq_diagMap hφ hφzero hr i

omit [Module.Finite (ZMod p) U] in
private lemma zff_diagMap_sign_eq_coordRefl (bf : Basis (Fin 4) (ZMod p) U) (i : Fin 4) :
    diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) = zff_coordRefl bf i := by
  apply LinearEquiv.ext
  intro v
  have hlin : ((diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) :
        U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      ((zff_coordRefl bf i : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by
    refine bf.ext (fun k => ?_)
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, diagMap_apply_basis,
      zff_coordRefl_apply, Basis.coord_apply, Basis.repr_self]
    by_cases hki : k = i
    · subst k
      simp
      module
    · simp [hki]
  exact congrArg (fun f : U →ₗ[ZMod p] U => f v) hlin

private lemma zff_sum_inv_pairing (hp : p ≠ 2) {c : Fin 4 → ZMod p} (_hc : ∀ i, c i ≠ 0)
    (ε : Fin 4 → ZMod p) :
    (∑ i, ε i * (2 * c i)⁻¹) = (2 : ZMod p)⁻¹ * (∑ i, ε i / c i) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

private lemma zff_sum_mul_pairing (ε c : Fin 4 → ZMod p) :
    (∑ i, (ε i * c i) * (2 : ZMod p)⁻¹) = (2 : ZMod p)⁻¹ * (∑ i, ε i * c i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_pairing (hp : p ≠ 2) {bf : Basis (Fin 4) (ZMod p) U} {u z : U}
    {χ ψ : Dual (ZMod p) U} {c ε : Fin 4 → ZMod p}
    (_hε : ∀ i, ε i = 1 ∨ ε i = -1) (hc : ∀ i, c i ≠ 0)
    (hu : u = ∑ i, bf i) (hz : z = ∑ i, c i • bf i)
    (hχ : ∀ i, χ (bf i) = (2 * c i)⁻¹) (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹)
    (w : U ≃ₗ[ZMod p] U) (β : Dual (ZMod p) U)
    (hw : ∀ i, w (bf i) = ε i • bf i) (hβeq : β = ψ.comp (w.symm : U →ₗ[ZMod p] U))
    (hw_inv : w.symm = w) :
    w u = ∑ i, ε i • bf i ∧
    w z = ∑ i, (ε i * c i) • bf i ∧
    χ (w u) = (2 : ZMod p)⁻¹ * (∑ i, ε i / c i) ∧
    β z = (2 : ZMod p)⁻¹ * (∑ i, ε i * c i) := by
  have hwu : w u = ∑ i, ε i • bf i := by
    rw [hu, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact hw i
  have hwz : w z = ∑ i, (ε i * c i) • bf i := by
    rw [hz, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hw i, smul_smul, mul_comm (c i) (ε i)]
  have hχw : χ (w u) = (2 : ZMod p)⁻¹ * (∑ i, ε i / c i) := by
    rw [hwu, map_sum]
    simp only [map_smul, smul_eq_mul, hχ]
    exact zff_sum_inv_pairing hp hc ε
  have hβz : β z = (2 : ZMod p)⁻¹ * (∑ i, ε i * c i) := by
    rw [hβeq, LinearMap.comp_apply, hw_inv]
    change ψ (w z) = (2 : ZMod p)⁻¹ * (∑ i, ε i * c i)
    rw [hwz, map_sum]
    simp only [map_smul, smul_eq_mul, hψf]
    exact zff_sum_mul_pairing ε c
  exact ⟨hwu, hwz, hχw, hβz⟩

omit [Module.Finite (ZMod p) U] in
private lemma zff_coords_eq_smul_sign_of_reflection_eq (hp : p ≠ 2)
    {bf : Basis (Fin 4) (ZMod p) U} {z u : U} {χ β : Dual (ZMod p) U}
    {c ε : Fin 4 → ZMod p} (hχ : χ z = 2) (hβ : β u = 2)
    (heq : reflection hχ = reflection hβ)
    (hz : z = ∑ i, c i • bf i) (hu : u = ∑ i, ε i • bf i) :
    ∃ c0 : ZMod p, c = c0 • ε := by
  obtain ⟨c0, hc0⟩ := zff_exists_smul_of_reflection_eq hp hβ hχ heq.symm
  have hz' : z = ∑ i, (c0 * ε i) • bf i := by
    rw [hc0, hu, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul]
  have hsum : ∑ i, (c i - c0 * ε i) • bf i = 0 := by
    have hsplit : (∑ i, (c i • bf i - (c0 * ε i) • bf i)) =
        ∑ i, c i • bf i - ∑ i, (c0 * ε i) • bf i :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => c i • bf i)
        (g := fun i => (c0 * ε i) • bf i)
    calc ∑ i, (c i - c0 * ε i) • bf i
        = ∑ i, (c i • bf i - (c0 * ε i) • bf i) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [sub_smul]
      _ = ∑ i, c i • bf i - ∑ i, (c0 * ε i) • bf i := hsplit
      _ = z - ∑ i, (c0 * ε i) • bf i := by rw [← hz]
      _ = z - z := by rw [← hz']
      _ = 0 := sub_self z
  have hg := (linearIndependent_iff'.mp bf.linearIndependent) Finset.univ
    (fun i => c i - c0 * ε i) hsum
  refine ⟨c0, ?_⟩
  funext i
  exact sub_eq_zero.mp (hg i (Finset.mem_univ i))

private lemma zff_mul_eq_four_of_inv_mul (hp : p ≠ 2) {S T : ZMod p}
    (h : (2 : ZMod p)⁻¹ * T * ((2 : ZMod p)⁻¹ * S) = 1) : S * T = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h' : ((2 : ZMod p)⁻¹ * 2⁻¹) * (S * T) = 1 := by
    calc ((2 : ZMod p)⁻¹ * 2⁻¹) * (S * T) = (2⁻¹ * T) * (2⁻¹ * S) := by ring
      _ = 1 := h
  calc S * T = (2 * 2 : ZMod p) * (((2 : ZMod p)⁻¹ * 2⁻¹) * (S * T)) := by
        field_simp
    _ = (2 * 2 : ZMod p) * 1 := by rw [h']
    _ = 4 := by norm_num

omit [Module.Finite (ZMod p) U] in
private lemma zff_stub_condition (hp : p ≠ 2) {bf : Basis (Fin 4) (ZMod p) U}
    {u z : U} {χ ψ : Dual (ZMod p) U} {c ε : Fin 4 → ZMod p}
    (_hε : ∀ i, ε i = 1 ∨ ε i = -1) (_hc : ∀ i, c i ≠ 0)
    (_hu : u = ∑ i, bf i) (hz : z = ∑ i, c i • bf i)
    (hχz : χ z = 2) (_hψu : ψ u = 2) (_hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹)
    (_hχc : ∀ i, χ (bf i) = (2 * c i)⁻¹)
    (w : U ≃ₗ[ZMod p] U) (β : Dual (ZMod p) U)
    (hwu : w u = ∑ i, ε i • bf i) (hχw : χ (w u) = 2⁻¹ * (∑ i, ε i / c i))
    (hβz : β z = 2⁻¹ * (∑ i, ε i * c i)) (hβ : β (w u) = 2)
    (hres : reflection hχz = reflection hβ ∨
      (χ (w u) = 0 ∧ β z = 0) ∨ χ (w u) * β z = 1) :
    (∃ c0 : ZMod p, c = c0 • ε) ∨
      ((∑ i, ε i * c i) = 0 ∧ (∑ i, ε i / c i) = 0) ∨
      (∑ i, ε i * c i) * (∑ i, ε i / c i) = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases hres with heq | hzero | hone
  · left
    exact zff_coords_eq_smul_sign_of_reflection_eq hp hχz hβ heq hz hwu
  · right; left
    constructor
    · have h : (2 : ZMod p)⁻¹ * (∑ i, ε i * c i) = 0 := by rw [← hβz]; exact hzero.2
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero h2)
    · have h : (2 : ZMod p)⁻¹ * (∑ i, ε i / c i) = 0 := by rw [← hχw]; exact hzero.1
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero h2)
  · right; right
    rw [hχw, hβz] at hone
    exact zff_mul_eq_four_of_inv_mul hp hone

omit [Module.Finite (ZMod p) U] in
private lemma zff_eq_sEps_of_coords (hp : p ≠ 2) {bf : Basis (Fin 4) (ZMod p) U}
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2)
    (_hs : s = reflection hψ) {t : U ≃ₗ[ZMod p] U} {z : U} {χ : Dual (ZMod p) U}
    (hχz : χ z = 2) (ht : t = reflection hχz)
    (hz : z = ∑ i, bf.coord i z • bf i)
    (hc : ∀ i, bf.coord i z ≠ 0)
    (hχc : ∀ i, χ (bf i) = (2 * bf.coord i z)⁻¹)
    (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹)
    {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {w : U ≃ₗ[ZMod p] U} {β : Dual (ZMod p) U}
    (hβ : β (w u) = 2) (hsE : w * s * w⁻¹ = reflection hβ)
    (hwu : w u = ∑ i, ε i • bf i) (hw : ∀ i, w (bf i) = ε i • bf i)
    (hβeq : β = ψ.comp (w.symm : U →ₗ[ZMod p] U)) (hsymm : w.symm = w)
    {c0 : ZMod p} (hc_eq : (fun i => bf.coord i z) = c0 • ε) :
    t = w * s * w⁻¹ := by
  have hc0 : c0 ≠ 0 := by
    intro h0
    have hzero : (fun i => bf.coord i z) = 0 := by rw [hc_eq, h0, zero_smul]
    exact hc 0 (by rw [congrFun hzero 0]; rfl)
  have hz0 : z = c0 • (w u) := by
    rw [hz, hwu, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hci : bf.coord i z = c0 * ε i := congrFun hc_eq i
    rw [hci, smul_smul]
  have hχβ : χ = c0⁻¹ • β := by
    apply bf.ext
    intro i
    rw [LinearMap.smul_apply, smul_eq_mul, hχc i, hβeq, LinearMap.comp_apply, hsymm]
    change (2 * bf.coord i z)⁻¹ = c0⁻¹ * ψ (w (bf i))
    rw [hw i, map_smul, smul_eq_mul, hψf i]
    have hci : bf.coord i z = c0 * ε i := congrFun hc_eq i
    rw [hci]
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    rcases hε i with h | h <;> rw [h] <;> field_simp [hc0, h2]
  have heq : reflection hχz = reflection hβ :=
    zff_reflection_eq_of_smul hβ hχz hc0 hz0 hχβ
  rw [ht, hsE]
  exact heq

omit [Module.Finite (ZMod p) U] in
private lemma zff_conj_data (_hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {bf : Basis (Fin 4) (ZMod p) U} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrdiag : ∀ i, r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (hrA : ∀ i, r i ∈ A) {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U}
    (hψ : ψ u = 2) (hs : s = reflection hψ) (hsA : s ∈ A)
    (hu : u = ∑ i, bf i) {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ (w : U ≃ₗ[ZMod p] U) (β : Dual (ZMod p) U) (hβ : β (w u) = 2),
      w = diagMap p bf (fun i => zff_signUnit (ε i) (hε i)) ∧
      (∀ i, w (bf i) = ε i • bf i) ∧
      β = ψ.comp (w.symm : U →ₗ[ZMod p] U) ∧ w ∈ A ∧
      w * s * w⁻¹ ∈ A ∧ w * w = 1 ∧ w.symm = w ∧
      w * s * w⁻¹ = reflection hβ ∧ w u = ∑ i, ε i • bf i := by
  let w : U ≃ₗ[ZMod p] U := diagMap p bf (fun i => zff_signUnit (ε i) (hε i))
  let β : Dual (ZMod p) U := ψ.comp (w.symm : U →ₗ[ZMod p] U)
  have hw : ∀ i, w (bf i) = ε i • bf i := fun i => zff_wEps_apply hε i
  have hwA : w ∈ A := zff_wEps_mem hrA hrdiag hε
  have hww : w * w = 1 := zff_wEps_mul_self hε
  have hsymm : w.symm = w := zff_wEps_inv hε
  have hwwu : w (w u) = u := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hww
    simpa [LinearEquiv.mul_apply] using this
  have hβ : β (w u) = 2 := by
    dsimp only [β]
    rw [LinearMap.comp_apply, hsymm]
    change ψ (w (w u)) = 2
    rw [hwwu, hψ]
  have hsE : w * s * w⁻¹ = reflection hβ := by
    rw [hs]
    exact conj_reflection w hψ hβ
  have hwui : w u = ∑ i, ε i • bf i := by
    rw [hu, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [zff_wEps_apply (b := bf) hε i]
  exact ⟨w, β, hβ, rfl, hw, rfl, hwA, A.mul_mem (A.mul_mem hwA hsA) (A.inv_mem hwA),
    hww, hsymm, hsE, hwui⟩

private lemma zff_classify_refl (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {bf : Basis (Fin 4) (ZMod p) U} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrdiag : ∀ i, r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (hrA : ∀ i, r i ∈ A) {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U}
    (hψ : ψ u = 2) (hs : s = reflection hψ) (hsA : s ∈ A)
    (hu : u = ∑ i, bf i) (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹)
    {t : U ≃ₗ[ZMod p] U} {z : U} {χ : Dual (ZMod p) U}
    (hχz : χ z = 2) (ht : t = reflection hχz) (htA : t ∈ A) (hrefl_t : IsRefl p t)
    (hz : z = ∑ i, bf.coord i z • bf i) (hc : ∀ i, bf.coord i z ≠ 0)
    (hχc : ∀ i, χ (bf i) = (2 * bf.coord i z)⁻¹) :
    ∃ (ε : Fin 4 → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1),
      t = diagMap p bf (fun i => zff_signUnit (ε i) (hε i)) * s *
        (diagMap p bf (fun i => zff_signUnit (ε i) (hε i)))⁻¹ := by
  have hstub : ∀ (ε : Fin 4 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) →
      (∃ c0 : ZMod p, (fun i => bf.coord i z) = c0 • ε) ∨
        ((∑ i, ε i * bf.coord i z) = 0 ∧ (∑ i, ε i / bf.coord i z) = 0) ∨
        (∑ i, ε i * bf.coord i z) * (∑ i, ε i / bf.coord i z) = 4 := by
    intro ε hε
    obtain ⟨w, β, hβ, hwdef, hw, hβeq, hwA, hsEA, hww, hsymm, hsE, hwu⟩ :=
      zff_conj_data hp hrdiag hrA hψ hs hsA hu hε
    have hsErefl : IsRefl p (w * s * w⁻¹) := by
      rw [hsE]
      exact isRefl_reflection hp hβ
    have hle : orderOf (t * (w * s * w⁻¹)) ≤ 3 := h3 t htA _ hsEA hrefl_t hsErefl
    have hle' : orderOf (reflection hχz * reflection hβ) ≤ 3 := by
      rw [ht, hsE] at hle
      exact hle
    have hres := eq_or_pairings_of_orderOf_le_three hp hχz hβ hle'
    obtain ⟨hwu', hwz, hχw, hβz⟩ :=
      zff_wEps_pairing hp hε hc hu hz hχc hψf w β hw hβeq hsymm
    exact zff_stub_condition hp hε hc hu hz hχz hψ hψf hχc w β hwu' hχw hβz hβ hres
  obtain ⟨c0, ε, hε, hc_eq⟩ :=
    exists_eq_smul_sign_of_pairings (K := ZMod p) (ZMod.prime_ne_zero p 2 hp) hc hstub
  obtain ⟨w, β, hβ, hwdef, hw, hβeq, hwA, hsEA, hww, hsymm, hsE, hwu⟩ :=
    zff_conj_data hp hrdiag hrA hψ hs hsA hu hε
  refine ⟨ε, hε, ?_⟩
  rw [← hwdef]
  exact zff_eq_sEps_of_coords hp hψ hs hχz ht hz hc hχc hψf hε hβ hsE hwu
    hw hβeq hsymm hc_eq

private noncomputable def zff_lineVec (bf : Basis (Fin 4) (ZMod p) U) : Fin 4 → U :=
  ![bf 0 + bf 1, bf 0 - bf 1, bf 2 + bf 3, bf 2 - bf 3]

private noncomputable def zff_line (bf : Basis (Fin 4) (ZMod p) U) (j : Fin 4) :
    Submodule (ZMod p) U :=
  Submodule.span (ZMod p) {zff_lineVec bf j}

omit [Module.Finite (ZMod p) U] in
private lemma zff_map_line_of_smul {g : U ≃ₗ[ZMod p] U} {v w : U} {c : ZMod p} (hc : c ≠ 0)
    (h : g v = c • w) :
    (Submodule.span (ZMod p) {v}).map (g : U →ₗ[ZMod p] U) =
      Submodule.span (ZMod p) {w} := by
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span (ZMod p) {g v} = Submodule.span (ZMod p) {w}
  rw [h]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) w

private def zff_linePerm (L : Fin 4 → Submodule (ZMod p) U) (g : U ≃ₗ[ZMod p] U) : Prop :=
  (∀ i, ∃ j, (L i).map (g : U →ₗ[ZMod p] U) = L j) ∧
    (∀ j, ∃ i, (L i).map (g : U →ₗ[ZMod p] U) = L j)

private def zff_lineStab (L : Fin 4 → Submodule (ZMod p) U) :
    Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {g | zff_linePerm L g}
  one_mem' := by
    refine ⟨fun i => ⟨i, ?_⟩, fun j => ⟨j, ?_⟩⟩
    · simp
    · simp
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    have hcomp : ((g * h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        (g : U →ₗ[ZMod p] U).comp (h : U →ₗ[ZMod p] U) := by
      ext x
      simp
    refine ⟨fun i => ?_, fun j => ?_⟩
    · obtain ⟨j, hj⟩ := hh1 i
      obtain ⟨k, hk⟩ := hg1 j
      refine ⟨k, ?_⟩
      rw [hcomp, Submodule.map_comp, hj, hk]
    · obtain ⟨j, hj⟩ := hg2 j
      obtain ⟨i, hi⟩ := hh2 j
      refine ⟨i, ?_⟩
      rw [hcomp, Submodule.map_comp, hi, hj]
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := hg
    have h2 : ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∘ₗ
        (g : U →ₗ[ZMod p] U) = LinearMap.id := by
      ext x
      simp
    refine ⟨fun i => ?_, fun j => ?_⟩
    · obtain ⟨j, hj⟩ := hg2 i
      refine ⟨j, ?_⟩
      calc (L i).map ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
          = ((L j).map (g : U →ₗ[ZMod p] U)).map
              ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by rw [hj]
        _ = (L j).map (((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∘ₗ
              (g : U →ₗ[ZMod p] U)) := by rw [← Submodule.map_comp]
        _ = (L j).map LinearMap.id := by rw [h2]
        _ = L j := Submodule.map_id _
    · obtain ⟨i, hi⟩ := hg1 j
      refine ⟨i, ?_⟩
      calc (L i).map ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
          = ((L j).map (g : U →ₗ[ZMod p] U)).map
              ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by rw [hi]
        _ = (L j).map (((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∘ₗ
              (g : U →ₗ[ZMod p] U)) := by rw [← Submodule.map_comp]
        _ = (L j).map LinearMap.id := by rw [h2]
        _ = L j := Submodule.map_id _

omit [Module.Finite (ZMod p) U] in
private lemma zff_linePerm_of_involution {L : Fin 4 → Submodule (ZMod p) U}
    {g : U ≃ₗ[ZMod p] U} (hgg : g * g = 1)
    (h : ∀ i, ∃ j, (L i).map (g : U →ₗ[ZMod p] U) = L j) : zff_linePerm L g := by
  have hcomp : ((g * g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (g : U →ₗ[ZMod p] U).comp (g : U →ₗ[ZMod p] U) := by
    ext x
    simp
  refine ⟨h, fun j => ?_⟩
  obtain ⟨k, hk⟩ := h j
  refine ⟨k, ?_⟩
  calc (L k).map (g : U →ₗ[ZMod p] U)
      = ((L j).map (g : U →ₗ[ZMod p] U)).map (g : U →ₗ[ZMod p] U) := by rw [hk]
    _ = (L j).map (((g * g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) := by
          rw [hcomp, Submodule.map_comp]
    _ = (L j).map ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by rw [hgg]
    _ = L j := by simp

omit [Module.Finite (ZMod p) U] in
private lemma zff_map_add_sub_of_smul {w : U ≃ₗ[ZMod p] U} {x y : U} {a b : ZMod p}
    (hx : w x = a • x) (hy : w y = b • y) (h : b = a ∨ b = -a) :
    (w (x + y) = a • (x + y) ∨ w (x + y) = a • (x - y)) ∧
      (w (x - y) = a • (x - y) ∨ w (x - y) = a • (x + y)) := by
  rcases h with rfl | h
  · constructor
    · left; rw [map_add, hx, hy, smul_add]
    · left; rw [map_sub, hx, hy, smul_sub]
  · constructor
    · right; rw [map_add, hx, hy, h, neg_smul, smul_sub, sub_eq_add_neg]
    · right; rw [map_sub, hx, hy, h, neg_smul, sub_neg_eq_add, smul_add]

omit [Module.Finite (ZMod p) U] in
private lemma zff_wEps_linePerm {bf : Basis (Fin 4) (ZMod p) U} {ε : Fin 4 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) {w : U ≃ₗ[ZMod p] U}
    (hw : ∀ i, w (bf i) = ε i • bf i) (hww : w * w = 1) :
    zff_linePerm (zff_line bf) w := by
  have hε0 : ε 0 ≠ 0 := by
    rcases hε 0 with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hε2 : ε 2 ≠ 0 := by
    rcases hε 2 with h | h
    · rw [h]; exact one_ne_zero
    · rw [h]; exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)
  have h01 : ε 1 = ε 0 ∨ ε 1 = -ε 0 := zff_sign_eq_or_neg (hε 0) (hε 1)
  have h23 : ε 3 = ε 2 ∨ ε 3 = -ε 2 := zff_sign_eq_or_neg (hε 2) (hε 3)
  obtain ⟨hv0, hv1⟩ := zff_map_add_sub_of_smul (w := w) (x := bf 0) (y := bf 1)
    (a := ε 0) (b := ε 1) (hw 0) (hw 1) h01
  obtain ⟨hv2, hv3⟩ := zff_map_add_sub_of_smul (w := w) (x := bf 2) (y := bf 3)
    (a := ε 2) (b := ε 3) (hw 2) (hw 3) h23
  have hfwd : ∀ j, ∃ k, (zff_line bf j).map (w : U →ₗ[ZMod p] U) = zff_line bf k := by
    intro j
    fin_cases j
    · rcases hv0 with hv | hv
      · exact ⟨0, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε0 hv⟩
      · exact ⟨1, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε0 hv⟩
    · rcases hv1 with hv | hv
      · exact ⟨1, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε0 hv⟩
      · exact ⟨0, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε0 hv⟩
    · rcases hv2 with hv | hv
      · exact ⟨2, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε2 hv⟩
      · exact ⟨3, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε2 hv⟩
    · rcases hv3 with hv | hv
      · exact ⟨3, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε2 hv⟩
      · exact ⟨2, by simpa [zff_line, zff_lineVec] using zff_map_line_of_smul hε2 hv⟩
  exact zff_linePerm_of_involution hww hfwd

omit [Module.Finite (ZMod p) U] in
private lemma zff_refl_mul_self {a : U} {φ : Dual (ZMod p) U} (hφ : φ a = 2) :
    reflection hφ * reflection hφ = 1 := by
  simpa [Module.reflection_inv] using mul_inv_cancel (reflection hφ)

omit [Module.Finite (ZMod p) U] in
private lemma zff_eq_zero_of_add_sub (hp : p ≠ 2) {x y : ZMod p}
    (h1 : x + y = 0) (h2 : x - y = 0) : x = 0 ∧ y = 0 := by
  have hx2 : (2 : ZMod p) * x = 0 := by linear_combination h1 + h2
  have hx : x = 0 := (mul_eq_zero.mp hx2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  subst hx
  exact ⟨rfl, by simpa using h1⟩

omit [Module.Finite (ZMod p) U] in
private lemma zff_lineVec_linearIndependent (hp : p ≠ 2)
    (bf : Basis (Fin 4) (ZMod p) U) :
    LinearIndependent (ZMod p) (zff_lineVec bf) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcoord : ∀ k : Fin 4, bf.coord k (∑ j, c j • zff_lineVec bf j) = 0 := by
    intro k
    rw [hc, map_zero]
  have h0 : c 0 + c 1 = 0 := by
    have h := hcoord 0
    simpa [Fin.sum_univ_four, zff_lineVec, map_add, map_smul, Basis.coord_apply,
      Basis.repr_self, smul_eq_mul] using h
  have h1 : c 0 - c 1 = 0 := by
    have h := hcoord 1
    simpa [Fin.sum_univ_four, zff_lineVec, map_add, map_sub, sub_eq_add_neg, map_smul,
      Basis.coord_apply, Basis.repr_self, smul_eq_mul] using h
  have h2 : c 2 + c 3 = 0 := by
    have h := hcoord 2
    simpa [Fin.sum_univ_four, zff_lineVec, map_add, map_smul, Basis.coord_apply,
      Basis.repr_self, smul_eq_mul] using h
  have h3 : c 2 - c 3 = 0 := by
    have h := hcoord 3
    simpa [Fin.sum_univ_four, zff_lineVec, map_add, map_sub, sub_eq_add_neg, map_smul,
      Basis.coord_apply, Basis.repr_self, smul_eq_mul] using h
  obtain ⟨hc0, hc1⟩ := zff_eq_zero_of_add_sub hp h0 h1
  obtain ⟨hc2, hc3⟩ := zff_eq_zero_of_add_sub hp h2 h3
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

omit [Module.Finite (ZMod p) U] in
private lemma zff_line_ne_bot (hp : p ≠ 2) (bf : Basis (Fin 4) (ZMod p) U) (j : Fin 4) :
    zff_line bf j ≠ ⊥ := by
  have hLI := zff_lineVec_linearIndependent hp bf
  intro hbot
  have hmem : zff_lineVec bf j ∈ zff_line bf j :=
    Submodule.subset_span (Set.mem_singleton (zff_lineVec bf j))
  rw [hbot] at hmem
  exact hLI.ne_zero j (by simpa using hmem)

omit [Module.Finite (ZMod p) U] in
private lemma zff_line_iSupIndep (hp : p ≠ 2) (bf : Basis (Fin 4) (ZMod p) U) :
    iSupIndep (zff_line bf) := by
  have h : iSupIndep (fun i => Submodule.span (ZMod p) {zff_lineVec bf i}) :=
    (zff_lineVec_linearIndependent hp bf).iSupIndep_span_singleton
  exact h

omit [Module.Finite (ZMod p) U] in
private lemma zff_line_iSup_eq_top (hp : p ≠ 2) (hn : Module.finrank (ZMod p) U = 4)
    (bf : Basis (Fin 4) (ZMod p) U) :
    (⨆ j, zff_line bf j) = ⊤ := by
  have hspan := (zff_lineVec_linearIndependent hp bf).span_eq_top_of_card_eq_finrank
    (by rw [Fintype.card_fin, hn])
  simpa [zff_line, Submodule.span_range_eq_iSup] using hspan

omit [Module.Finite (ZMod p) U] in
private lemma zff_isImprimitive_of_le_lineStab (hp : p ≠ 2)
    (hn : Module.finrank (ZMod p) U = 4) {bf : Basis (Fin 4) (ZMod p) U}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A ≤ zff_lineStab (zff_line bf)) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  refine ⟨4, zff_line bf, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i
    exact zff_line_ne_bot hp bf i
  · exact zff_line_iSupIndep hp bf
  · exact zff_line_iSup_eq_top hp hn bf
  · intro g hg i
    exact (hA hg).1 i

omit [Module.Finite (ZMod p) U] in
private lemma zff_r_linePerm {bf : Basis (Fin 4) (ZMod p) U}
    {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrdiag : ∀ i, r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (i : Fin 4) : zff_linePerm (zff_line bf) (r i) := by
  let ε : Fin 4 → ZMod p := fun k => if k = i then -1 else 1
  have hε : ∀ k, ε k = 1 ∨ ε k = -1 := by
    intro k
    by_cases hki : k = i
    · right; simp [ε, hki]
    · left; simp [ε, hki]
  have hw : ∀ k, r i (bf k) = ε k • bf k := by
    intro k
    rw [hrdiag i, diagMap_apply_basis]
    by_cases hki : k = i <;> simp [ε, hki]
  have hww : r i * r i = 1 := by
    rw [hrdiag i, diagMap_mul]
    have hu : (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) *
        (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) = 1 := by
      funext k
      by_cases hki : k = i <;> simp [hki, Pi.mul_apply]
    rw [hu, diagMap_one]
  exact zff_wEps_linePerm hε hw hww

omit [Module.Finite (ZMod p) U] in
private lemma zff_s_apply_lineVec (hp : p ≠ 2) {bf : Basis (Fin 4) (ZMod p) U}
    {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2) (hu : u = ∑ i, bf i)
    (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹) :
    (reflection hψ) (zff_lineVec bf 0) = -(zff_lineVec bf 2) ∧
      (reflection hψ) (zff_lineVec bf 1) = zff_lineVec bf 1 ∧
      (reflection hψ) (zff_lineVec bf 2) = -(zff_lineVec bf 0) ∧
      (reflection hψ) (zff_lineVec bf 3) = zff_lineVec bf 3 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hA : ψ (bf 0 + bf 1) = 1 := by
    rw [map_add, hψf 0, hψf 1, ← two_mul, mul_inv_cancel₀ h2]
  have hB : ψ (bf 0 - bf 1) = 0 := by
    rw [map_sub, hψf 0, hψf 1, sub_self]
  have hC : ψ (bf 2 + bf 3) = 1 := by
    rw [map_add, hψf 2, hψf 3, ← two_mul, mul_inv_cancel₀ h2]
  have hD : ψ (bf 2 - bf 3) = 0 := by
    rw [map_sub, hψf 2, hψf 3, sub_self]
  have hu' : u = bf 0 + bf 1 + bf 2 + bf 3 := by rw [hu, Fin.sum_univ_four]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (reflection hψ) (bf 0 + bf 1) = -(bf 2 + bf 3)
    rw [reflection_apply, hA, hu', one_smul]
    abel
  · change (reflection hψ) (bf 0 - bf 1) = bf 0 - bf 1
    rw [reflection_apply, hB, zero_smul, sub_zero]
  · change (reflection hψ) (bf 2 + bf 3) = -(bf 0 + bf 1)
    rw [reflection_apply, hC, hu', one_smul]
    abel
  · change (reflection hψ) (bf 2 - bf 3) = bf 2 - bf 3
    rw [reflection_apply, hD, zero_smul, sub_zero]

omit [Module.Finite (ZMod p) U] in
private lemma zff_s_linePerm (hp : p ≠ 2) {bf : Basis (Fin 4) (ZMod p) U}
    {u : U} {ψ : Dual (ZMod p) U} (hψ : ψ u = 2) (hu : u = ∑ i, bf i)
    (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹) :
    zff_linePerm (zff_line bf) (reflection hψ) := by
  have hact := zff_s_apply_lineVec hp hψ hu hψf
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)
  have h0 : (zff_line bf 0).map ((reflection hψ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) = zff_line bf 2 := by
    have h := zff_map_line_of_smul (g := reflection hψ) (v := zff_lineVec bf 0)
      (w := zff_lineVec bf 2) (c := -1) hneg (by simpa using hact.1)
    simpa [zff_line] using h
  have h1 : (zff_line bf 1).map ((reflection hψ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) = zff_line bf 1 := by
    have h := zff_map_line_of_smul (g := reflection hψ) (v := zff_lineVec bf 1)
      (w := zff_lineVec bf 1) (c := 1) one_ne_zero (by simpa using hact.2.1)
    simpa [zff_line] using h
  have h2 : (zff_line bf 2).map ((reflection hψ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) = zff_line bf 0 := by
    have h := zff_map_line_of_smul (g := reflection hψ) (v := zff_lineVec bf 2)
      (w := zff_lineVec bf 0) (c := -1) hneg (by simpa using hact.2.2.1)
    simpa [zff_line] using h
  have h3 : (zff_line bf 3).map ((reflection hψ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) = zff_line bf 3 := by
    have h := zff_map_line_of_smul (g := reflection hψ) (v := zff_lineVec bf 3)
      (w := zff_lineVec bf 3) (c := 1) one_ne_zero (by simpa using hact.2.2.2)
    simpa [zff_line] using h
  have hfwd : ∀ j, ∃ k, (zff_line bf j).map
      ((reflection hψ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = zff_line bf k := by
    intro j
    fin_cases j
    · exact ⟨2, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h2⟩
    · exact ⟨3, h3⟩
  exact zff_linePerm_of_involution (zff_refl_mul_self hψ) hfwd

private lemma zff_refl_mem_lineStab (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {bf : Basis (Fin 4) (ZMod p) U} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrdiag : ∀ i, r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (hrA : ∀ i, r i ∈ A) (hrr : ∀ i, IsRefl p (r i))
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U}
    (hψ : ψ u = 2) (hs : s = reflection hψ) (hsA : s ∈ A)
    (hu : u = ∑ i, bf i) (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹)
    {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (hrefl_t : IsRefl p t) :
    t ∈ zff_lineStab (zff_line bf) := by
  let φ : Fin 4 → Dual (ZMod p) U := fun i => zff_coordPhi bf i
  have hφ : ∀ i, φ i (bf i) = 2 := fun i => zff_coordPhi_self bf i
  have hφeq : ∀ i, φ i = (2 : ZMod p) • bf.coord i := fun _ => rfl
  have hr' : ∀ i, r i = reflection (hφ i) := by
    intro i
    rw [hrdiag i, zff_diagMap_sign_eq_coordRefl]
    rfl
  by_cases hcov : ∃ i, t = r i
  · obtain ⟨i, rfl⟩ := hcov
    exact zff_r_linePerm hrdiag i
  · obtain ⟨z, χ, hχz, ht⟩ := (isRefl_iff hp t).mp hrefl_t
    have htne : ∀ i, t ≠ r i := fun i hit => hcov ⟨i, hit⟩
    have hc : ∀ i, bf.coord i z ≠ 0 :=
      zff_coords_ne_zero hp hφ hφeq hr' hχz ht hrA htA hrr hrefl_t h3 htne
    have halt : ∀ i, (bf.coord i z = 0 ∧ χ (bf i) = 0) ∨
        (2 * bf.coord i z) * χ (bf i) = 1 :=
      zff_pairing_alt hp hφ hφeq hr' hχz ht hrA htA hrr hrefl_t h3 htne
    have hχc : ∀ i, χ (bf i) = (2 * bf.coord i z)⁻¹ := zff_psi_coords hc halt
    have hz : z = ∑ i, bf.coord i z • bf i := by
      simp [Basis.coord_apply]
    obtain ⟨ε, hε, htε⟩ := zff_classify_refl hp h3 hrdiag hrA hψ hs hsA hu hψf
      hχz ht htA hrefl_t hz hc hχc
    let w : U ≃ₗ[ZMod p] U := diagMap p bf (fun i => zff_signUnit (ε i) (hε i))
    have hw : ∀ i, w (bf i) = ε i • bf i := fun i => zff_wEps_apply hε i
    have hwL : w ∈ zff_lineStab (zff_line bf) :=
      zff_wEps_linePerm hε hw (zff_wEps_mul_self hε)
    have hsL : s ∈ zff_lineStab (zff_line bf) := by
      rw [hs]
      exact zff_s_linePerm hp hψ hu hψf
    have hmul : w * s * w⁻¹ ∈ zff_lineStab (zff_line bf) :=
      (zff_lineStab (zff_line bf)).mul_mem
        ((zff_lineStab (zff_line bf)).mul_mem hwL hsL)
        ((zff_lineStab (zff_line bf)).inv_mem hwL)
    exact htε ▸ hmul

private lemma zff_le_lineStab_of_extra (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : ReflGen p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {bf : Basis (Fin 4) (ZMod p) U} {r : Fin 4 → U ≃ₗ[ZMod p] U}
    (hrdiag : ∀ i, r i = diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1))
    (hrA : ∀ i, r i ∈ A) (hrr : ∀ i, IsRefl p (r i))
    {s : U ≃ₗ[ZMod p] U} {u : U} {ψ : Dual (ZMod p) U}
    (hψ : ψ u = 2) (hs : s = reflection hψ) (hsA : s ∈ A)
    (hu : u = ∑ i, bf i) (hψf : ∀ i, ψ (bf i) = (2 : ZMod p)⁻¹) :
    A ≤ zff_lineStab (zff_line bf) := by
  rw [hgen, Subgroup.closure_le]
  intro t ht
  exact zff_refl_mem_lineStab hp h3 hrdiag hrA hrr hψ hs hsA hu hψf ht.1 ht.2

private lemma zff_isImprimitive_of_extra (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hn : Module.finrank (ZMod p) U = 4)
    (hgen : ReflGen p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hrA : ∀ i, r i ∈ A) (hr : ∀ i, IsRefl p (r i))
    (hcomm : Pairwise fun i j => Commute (r i) (r j)) (hinj : Function.Injective r)
    {s : U ≃ₗ[ZMod p] U} (hsA : s ∈ A) (hrefl_s : IsRefl p s)
    (hsne : ∀ i, s ≠ r i) : CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  obtain ⟨b, φ, hφ, hr_eq, hφzero, hφeq⟩ := zff_exists_frame hp hn hr hcomm hinj
  obtain ⟨u, ψ, hψ, hs⟩ := (isRefl_iff hp s).mp hrefl_s
  have halt : ∀ i, (b.coord i u = 0 ∧ ψ (b i) = 0) ∨
      (2 * b.coord i u) * ψ (b i) = 1 :=
    zff_pairing_alt hp hφ hφeq hr_eq hψ hs hrA hsA hr hrefl_s h3 hsne
  have hc : ∀ i, b.coord i u ≠ 0 :=
    zff_coords_ne_zero hp hφ hφeq hr_eq hψ hs hrA hsA hr hrefl_s h3 hsne
  have hy : ∀ i, ψ (b i) = (2 * b.coord i u)⁻¹ := zff_psi_coords hc halt
  obtain ⟨bf, hbf, hcoord, hψf, hu⟩ := zff_rescaled_basis hp hn hc hy
  have hrdiag : ∀ i, r i =
      diagMap p bf (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) :=
    fun i => zff_r_eq_diagMap_bf hφ hφzero hr_eq hc hbf i
  have hA : A ≤ zff_lineStab (zff_line bf) :=
    zff_le_lineStab_of_extra hp hgen h3 hrdiag hrA hr hψ hs hsA hu hψf
  exact zff_isImprimitive_of_le_lineStab hp hn hA

theorem isImprimitiveOnV_of_frame (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hn : Module.finrank (ZMod p) U = 4) (hgen : ReflGen p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {r : Fin 4 → U ≃ₗ[ZMod p] U} (hrA : ∀ i, r i ∈ A) (hr : ∀ i, IsRefl p (r i))
    (hcomm : Pairwise fun i j => Commute (r i) (r j)) (hinj : Function.Injective r) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  by_cases hcase : ∃ s ∈ A, IsRefl p s ∧ ∀ i, s ≠ r i
  · obtain ⟨s, hsA, hrefl_s, hsne⟩ := hcase
    exact zff_isImprimitive_of_extra hp hn hgen h3 hrA hr hcomm hinj hsA hrefl_s hsne
  · obtain ⟨b, φ, hφ, hr_eq, hφzero, hφeq⟩ := zff_exists_frame hp hn hr hcomm hinj
    have hrdiag : ∀ i, r i = diagMap p b (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) :=
      fun i => zff_r_eq_diagMap hφ hφzero hr_eq i
    have hcover : ∀ t ∈ A, IsRefl p t → ∃ i, t = r i := by
      intro t htA hrefl_t
      by_contra h
      exact hcase ⟨t, htA, hrefl_t, fun i hit => h ⟨i, hit⟩⟩
    have hA : A ≤ zff_lineStab (zff_line b) := by
      rw [hgen, Subgroup.closure_le]
      intro t ht
      obtain ⟨i, rfl⟩ := hcover t ht.1 ht.2
      exact zff_r_linePerm hrdiag i
    exact zff_isImprimitive_of_le_lineStab hp hn hA

end CFSG.StandardType.ZS
