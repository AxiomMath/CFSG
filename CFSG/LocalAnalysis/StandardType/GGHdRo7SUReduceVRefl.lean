module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs
public import CFSG.RankThree.PartOne.S12.Sec138LocLinear
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUReduceVAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide +revert

theorem hdRo7SUReduceVAux_neg_one_ne_zero : (-1 : ZMod 3) ≠ 0 := by decide +revert

theorem hdRo7SUReduceVAux_neg_two_ne_zero : (-2 : ZMod 3) ≠ 0 := by decide +revert

theorem hdRo7SUReduceVAux_reflData {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] [Module.Finite (ZMod 3) V] (r : V ≃ₗ[ZMod 3] V)
    (hr : GGLinRefl (p := 3) r) : ∃ (u : V) (φ : V →ₗ[ZMod 3] ZMod 3), ReflData r u φ := by
  have h2 : (2 : ZMod 3) ≠ 0 := hdRo7SUReduceVAux_two_ne_zero
  have hrank : Module.finrank (ZMod 3) (LinearMap.range (Nop r)) = 1 := by
    have h : Nop r = -(r.toLinearMap - LinearMap.id) := by
      ext x; simp [Nop]
    rw [h, LinearMap.range_neg]
    exact hr.2
  exact CFSG.RankThree.PartOne.Sec138Loc.exists_reflData_field h2 r hr.1 hrank

theorem hdRo7SUReduceVAux_coord_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (k l : Fin m) :
    b.coord k (b l) = (if k = l then 1 else 0 : ZMod 3) := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : k = l <;> simp [h]

theorem hdRo7SUReduceVAux_swap_reflData {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {i j : Fin m} (hij : i ≠ j) :
    ReflData (b.equiv b (Equiv.swap i j)) (b i - b j) (b.coord i - b.coord j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hij (b.injective (sub_eq_zero.mp h))
  · rw [LinearMap.sub_apply, map_sub, map_sub, hdRo7SUReduceVAux_coord_basis b i i,
      hdRo7SUReduceVAux_coord_basis b i j, hdRo7SUReduceVAux_coord_basis b j i,
      hdRo7SUReduceVAux_coord_basis b j j,
      if_pos rfl, if_neg hij, if_neg hij.symm, if_pos rfl]
    norm_num
  · intro v
    have hlin : ((b.equiv b (Equiv.swap i j) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
        LinearMap.id - (b.coord i - b.coord j).smulRight (b i - b j) := by
      apply b.ext
      intro p
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.sub_apply]
      simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      by_cases hpi : p = i
      · rw [hpi, Equiv.swap_apply_left]
        rw [hdRo7SUReduceVAux_coord_basis b i i, hdRo7SUReduceVAux_coord_basis b j i,
          if_pos rfl, if_neg hij.symm, sub_zero, one_smul]
        module
      · by_cases hpj : p = j
        · rw [hpj, Equiv.swap_apply_right]
          rw [hdRo7SUReduceVAux_coord_basis b i j, hdRo7SUReduceVAux_coord_basis b j j,
            if_pos rfl, if_neg hij, zero_sub, neg_smul, one_smul]
          module
        · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]
          rw [hdRo7SUReduceVAux_coord_basis b i p, hdRo7SUReduceVAux_coord_basis b j p,
            if_neg (fun h => hpi h.symm), if_neg (fun h => hpj h.symm), sub_self, zero_smul,
            sub_zero]
    have h := congrArg (fun L : V →ₗ[ZMod 3] V => L v) hlin
    simpa [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply] using h

theorem hdRo7SUReduceVAux_mul_sq_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {r t : V ≃ₗ[ZMod 3] V} {u k : V}
    {φ ψ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ) (ht : ReflData t k ψ)
    (h0 : φ k = 0) (w : V) :
    (t * r) ((t * r) w) = w - (ψ u * φ w) • k := by
  conv_lhs => rw [ht.mul_apply hr w]
  simp only [map_sub, map_add, map_smul]
  rw [ht.mul_apply hr u, ht.mul_apply hr k, ht.mul_apply hr w, hr.pair, ht.pair, h0]
  module

theorem hdRo7SUReduceVAux_range_smul_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {L : V →ₗ[ZMod 3] V} {c : ZMod 3} (hc : c ≠ 0) :
    LinearMap.range (c • L) = LinearMap.range L := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    exact ⟨c • v, by rw [LinearMap.smul_apply, map_smul]⟩
  · rintro w ⟨v, rfl⟩
    exact ⟨c⁻¹ • v, by
      rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

theorem hdRo7SUReduceVAux_range_smulRight {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {k : V} (hk : k ≠ 0) {φ : V →ₗ[ZMod 3] ZMod 3}
    (hφ : φ ≠ 0) : LinearMap.range (φ.smulRight k) = Submodule.span (ZMod 3) {k} := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton k))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (by ext v; exact h v)
    refine ⟨(φ v)⁻¹ • v, ?_⟩
    rw [LinearMap.smulRight_apply, map_smul, smul_eq_mul, inv_mul_cancel₀ hv, one_smul]

theorem hdRo7SUReduceVAux_sq_transv {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {r t : V ≃ₗ[ZMod 3] V} {u k : V}
    {φ ψ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ) (ht : ReflData t k ψ)
    (h0 : φ k = 0) (hc : ψ u ≠ 0) : C2Transv (p := 3) ((t * r) ^ 2) := by
  have hkey : ∀ w, (t * r) ((t * r) w) = w - (ψ u * φ w) • k :=
    hdRo7SUReduceVAux_mul_sq_apply hr ht h0
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h] at hr
    exact hdRo7SUReduceVAux_two_ne_zero hr.pair.symm
  constructor
  · have hmap : ((t * r) ^ 2 : V ≃ₗ[ZMod 3] V).toLinearMap - LinearMap.id =
        (-(ψ u)) • φ.smulRight k := by
      ext w
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, pow_two,
        LinearEquiv.mul_apply, hkey w, LinearMap.smul_apply, LinearMap.smulRight_apply,
        smul_smul]
      module
    rw [ggLinMove, hmap, hdRo7SUReduceVAux_range_smul_eq (neg_ne_zero.mpr hc),
      hdRo7SUReduceVAux_range_smulRight ht.ne hφ0]
    exact finrank_span_singleton ht.ne
  · intro w
    have h1 : ((t * r) ^ 2) w = w - (ψ u * φ w) • k := by rw [pow_two]; exact hkey w
    have h2 : ((t * r) ^ 2) k = k := by
      rw [pow_two, LinearEquiv.mul_apply, hkey k, h0, mul_zero, zero_smul, sub_zero]
    have hx : ((t * r) ^ 2) w - w = -((ψ u * φ w)) • k := by
      rw [h1, show w - (ψ u * φ w) • k - w = -((ψ u * φ w) • k) by abel, neg_smul]
    rw [hx, map_smul, h2]

theorem hdRo7SUReduceVAux_zero_pair {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    {r t : V ≃ₗ[ZMod 3] V} {u k : V} {φ ψ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (ht : ReflData t k ψ) (hrA : r ∈ A) (htA : t ∈ A)
    (h0 : φ k = 0) : ψ u = 0 := by
  by_contra hc
  have hmem : (t * r) ^ 2 ∈ A := by
    simpa [pow_two] using A.mul_mem (A.mul_mem htA hrA) (A.mul_mem htA hrA)
  exact hNoT ((t * r) ^ 2) hmem (hdRo7SUReduceVAux_sq_transv hr ht h0 hc)

theorem hdRo7SUReduceVAux_zero_pair_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    {r t : V ≃ₗ[ZMod 3] V} {u k : V} {φ ψ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (ht : ReflData t k ψ) (hrA : r ∈ A) (htA : t ∈ A) :
    φ k = 0 ↔ ψ u = 0 :=
  ⟨hdRo7SUReduceVAux_zero_pair hNoT hr ht hrA htA,
    hdRo7SUReduceVAux_zero_pair hNoT ht hr htA hrA⟩

theorem hdRo7SUReduceVAux_coord_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    (hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ)
    (hrA : r ∈ A) {i j : Fin m} (hij : i ≠ j) :
    φ (b i - b j) = 0 ↔ b.coord i u - b.coord j u = 0 := by
  have hiff := hdRo7SUReduceVAux_zero_pair_iff hNoT hr (hdRo7SUReduceVAux_swap_reflData b hij)
    hrA (hsA i j hij)
  simpa using hiff

theorem hdRo7SUReduceVAux_root_const_of_phi_const {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    (hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ)
    (hrA : r ∈ A) (hφ : ∀ i j, φ (b i) = φ (b j)) :
    ∀ i j, b.coord i u = b.coord j u := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have h0 : φ (b i - b j) = 0 := by rw [map_sub, hφ i j, sub_self]
    exact sub_eq_zero.mp ((hdRo7SUReduceVAux_coord_iff b hNoT hsA hr hrA hij).mp h0)

theorem hdRo7SUReduceVAux_coord_ones {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (k : Fin m) :
    b.coord k (SUOnes 3 b) = 1 := by
  rw [SUOnes, map_sum]
  simp [Module.Basis.coord_apply, Module.Basis.repr_self]

theorem hdRo7SUReduceVAux_exists_notMem {m : ℕ} {s : Finset (Fin m)} (h : s.card < m) :
    ∃ k, k ∉ s := by
  by_contra hc
  push Not at hc
  have hs : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
  rw [hs, Finset.card_univ, Fintype.card_fin] at h
  exact absurd h (lt_irrefl m)

theorem hdRo7SUReduceVAux_indep_of_two_coords {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod 3) V)
    {w0 wl : V} {k : Fin m} (hk : k ≠ 0) {A0 B0 c : ZMod 3}
    (hA0 : b.coord 0 w0 = A0) (hB0 : b.coord 0 wl = B0)
    (hAk : b.coord k w0 = c) (hBk : b.coord k wl = c)
    (hAB : A0 - B0 ≠ 0) (hc : c ≠ 0) :
    ∀ α β : ZMod 3, α • w0 + β • wl = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have e1 : c * (α + β) = 0 := by
    have h1 := congrArg (b.coord k) h
    simp only [map_add, map_smul, map_zero, hAk, hBk, smul_eq_mul] at h1
    rw [mul_add, mul_comm c α, mul_comm c β]
    exact h1
  have hsum : α + β = 0 := (mul_eq_zero.mp e1).resolve_left hc
  have e2 : (A0 - B0) * α = 0 := by
    have h1 := congrArg (b.coord 0) h
    simp only [map_add, map_smul, map_zero, hA0, hB0, smul_eq_mul] at h1
    linear_combination h1 - B0 * hsum
  have hα : α = 0 := (mul_eq_zero.mp e2).resolve_left hAB
  refine ⟨hα, ?_⟩
  rw [hα, zero_add] at hsum
  exact hsum

theorem hdRo7SUReduceVAux_coord_move {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) (ZMod 3) V)
    {r : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin m)} {c : ZMod 3}
    (hform : ∀ i, r (b i) = -b (σ i) + c • SUOnes 3 b) (i t : Fin m) :
    b.coord t ((r.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b i)) =
      c - (if t = σ i then 1 else 0) - (if t = i then 1 else 0) := by
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hform i]
  rw [map_sub, map_add, map_neg, map_smul, hdRo7SUReduceVAux_coord_basis b t (σ i),
    hdRo7SUReduceVAux_coord_basis b t i, hdRo7SUReduceVAux_coord_ones]
  ring_nf

theorem hdRo7SUReduceVAux_card_three {m : ℕ} [NeZero m] (a b d : Fin m) :
    ({a, b, d} : Finset (Fin m)).card ≤ 3 := by
  have h1 := Finset.card_insert_le a ({b, d} : Finset (Fin m))
  have h2 := Finset.card_insert_le b ({d} : Finset (Fin m))
  have h3 : ({d} : Finset (Fin m)).card ≤ 1 := by simp
  omega

theorem hdRo7SUReduceVAux_card_four {m : ℕ} [NeZero m] (a b d e : Fin m) :
    ({a, b, d, e} : Finset (Fin m)).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, d, e} : Finset (Fin m))
  have h2 := hdRo7SUReduceVAux_card_three b d e
  omega

theorem hdRo7SUReduceVAux_second_form_not_refl {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (hm : 5 ≤ m) (hm3 : ¬ 3 ∣ m) {σ : Equiv.Perm (Fin m)} {r : V ≃ₗ[ZMod 3] V}
    (hform : ∀ i, r (b i) = -b (σ i) + (2 / (m : ZMod 3)) • SUOnes 3 b)
    (hr : GGLinRefl (p := 3) r) : False := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  have hm_ne : (m : ZMod 3) ≠ 0 := by
    intro h
    exact hm3 ((CharP.cast_eq_zero_iff (ZMod 3) 3 m).mp h)
  have hc : (2 / (m : ZMod 3)) ≠ 0 :=
    div_ne_zero hdRo7SUReduceVAux_two_ne_zero hm_ne
  have hcm : (m : ZMod 3) * (2 / (m : ZMod 3)) = 2 := by
    rw [mul_comm]; exact div_mul_cancel₀ 2 hm_ne
  have hcx : r (SUOnes 3 b) = SUOnes 3 b := by
    rw [SUOnes, map_sum]
    simp_rw [hform]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have h1 : (∑ i, b (σ i)) = SUOnes 3 b := by rw [Equiv.sum_comp]; rfl
    have h2 : (∑ _i : Fin m, (2 / (m : ZMod 3)) • SUOnes 3 b) =
        (2 : ZMod 3) • SUOnes 3 b := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul (ZMod 3) m ((2 / (m : ZMod 3)) • SUOnes 3 b),
        smul_smul, hcm]
    rw [h1, h2]
    simp only [SUOnes]
    module
  have hσ2 : σ * σ = 1 := by
    apply Equiv.ext
    intro i
    have h1 : (r * r) (b i) = b i := by rw [hr.1]; rfl
    have h2 : (r * r) (b i) = b (σ (σ i)) := by
      calc (r * r) (b i) = r (r (b i)) := rfl
        _ = r (-b (σ i) + (2 / (m : ZMod 3)) • SUOnes 3 b) := by rw [hform i]
        _ = -r (b (σ i)) + (2 / (m : ZMod 3)) • r (SUOnes 3 b) := by
              rw [map_add, map_neg, map_smul]
        _ = -(-b (σ (σ i)) + (2 / (m : ZMod 3)) • SUOnes 3 b) +
              (2 / (m : ZMod 3)) • SUOnes 3 b := by rw [hform (σ i), hcx]
        _ = b (σ (σ i)) := by module
    exact b.injective (h2.symm.trans h1)
  let z : Fin m := 0
  let o : Fin m := ⟨1, by omega⟩
  have hz_ne_o : z ≠ o := by
    intro h
    have hh := congrArg Fin.val h
    simp [z, o] at hh
  let w : Fin m → V := fun i => (r.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b i)
  have hw : ∀ i t : Fin m, b.coord t (w i) =
      (2 / (m : ZMod 3)) - (if t = σ i then 1 else 0) - (if t = i then 1 else 0) :=
    fun i t => hdRo7SUReduceVAux_coord_move b hform i t
  have hmem : ∀ i, w i ∈ ggLinMove (p := 3) r := fun i => ⟨b i, rfl⟩
  have contra : ∀ w0 wl : V, (∀ α β : ZMod 3, α • w0 + β • wl = 0 → α = 0 ∧ β = 0) →
      w0 ∈ ggLinMove (p := 3) r → wl ∈ ggLinMove (p := 3) r → False := by
    intro w0 wl hind h0 hl
    have hw0ne : w0 ≠ 0 := by
      intro h
      exact one_ne_zero (hind 1 0 (by rw [h]; simp)).1
    have hspan : ggLinMove (p := 3) r = Submodule.span (ZMod 3) {w0} := by
      have hle : Submodule.span (ZMod 3) {w0} ≤ ggLinMove (p := 3) r := by
        rw [Submodule.span_singleton_le_iff_mem]; exact h0
      have hfr : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {w0}) =
          Module.finrank (ZMod 3) (ggLinMove (p := 3) r) := by
        rw [finrank_span_singleton hw0ne, hr.2]
      exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (by rw [← hspan]; exact hl)
    exact one_ne_zero (hind (-lam) 1 (by rw [← hlam]; module)).2
  by_cases hσ0 : σ z = z
  · have hcard : ({z, o, σ o} : Finset (Fin m)).card < m := by
      have := hdRo7SUReduceVAux_card_three z o (σ o)
      omega
    obtain ⟨k, hk⟩ := hdRo7SUReduceVAux_exists_notMem hcard
    have hkz : k ≠ z := fun h => hk (by rw [h]; simp)
    have hko : k ≠ o := fun h => hk (by rw [h]; simp)
    have hkσo : k ≠ σ o := fun h => hk (by rw [h]; simp)
    have hσ2o : σ (σ o) = o := by
      have := congrArg (fun τ : Equiv.Perm (Fin m) => τ o) hσ2
      simpa [Equiv.Perm.mul_apply] using this
    have hzσo : z ≠ σ o := by
      intro h
      have ho : o = z := by
        calc o = σ (σ o) := hσ2o.symm
          _ = σ z := by rw [h]
          _ = z := hσ0
      exact hz_ne_o ho.symm
    have hind := hdRo7SUReduceVAux_indep_of_two_coords b hkz
      (A0 := (2 / (m : ZMod 3)) - 2) (B0 := 2 / (m : ZMod 3))
      (c := 2 / (m : ZMod 3))
      (by rw [hw z z, hσ0]; simp; ring)
      (by rw [hw o z, if_neg hzσo, if_neg hz_ne_o]; ring)
      (by rw [hw z k, if_neg (fun h : k = σ z => hkz (h.trans hσ0)), if_neg hkz]; ring)
      (by rw [hw o k, if_neg hkσo, if_neg hko]; ring)
      (by have : (2 / (m : ZMod 3)) - 2 - 2 / (m : ZMod 3) = -2 := by ring
          rw [this]; exact hdRo7SUReduceVAux_neg_two_ne_zero) hc
    exact contra (w z) (w o) hind (hmem z) (hmem o)
  · have hcard : ({z, σ z} : Finset (Fin m)).card < m := by
      have h1 := Finset.card_insert_le z ({σ z} : Finset (Fin m))
      have h2 : ({σ z} : Finset (Fin m)).card ≤ 1 := by simp
      omega
    obtain ⟨l, hl⟩ := hdRo7SUReduceVAux_exists_notMem hcard
    have hlz : l ≠ z := fun h => hl (by rw [h]; simp)
    have hlσz : l ≠ σ z := fun h => hl (by rw [h]; simp)
    have hcard2 : ({z, σ z, l, σ l} : Finset (Fin m)).card < m := by
      have := hdRo7SUReduceVAux_card_four z (σ z) l (σ l)
      omega
    obtain ⟨k, hk⟩ := hdRo7SUReduceVAux_exists_notMem hcard2
    have hkz : k ≠ z := fun h => hk (by rw [h]; simp)
    have hkj : k ≠ σ z := fun h => hk (by rw [h]; simp)
    have hkl : k ≠ l := fun h => hk (by rw [h]; simp)
    have hkσl : k ≠ σ l := fun h => hk (by rw [h]; simp)
    have hzσl : z ≠ σ l := by
      intro h
      have : l = σ z := by
        have hσ2l : σ (σ l) = l := by
          have := congrArg (fun τ : Equiv.Perm (Fin m) => τ l) hσ2
          simpa [Equiv.Perm.mul_apply] using this
        calc l = σ (σ l) := hσ2l.symm
          _ = σ z := by rw [h]
      exact hlσz this
    have hind := hdRo7SUReduceVAux_indep_of_two_coords b hkz
      (A0 := (2 / (m : ZMod 3)) - 1) (B0 := 2 / (m : ZMod 3))
      (c := 2 / (m : ZMod 3))
      (by rw [hw z z, if_neg (fun h : z = σ z => hσ0 h.symm), if_pos rfl]; ring)
      (by rw [hw l z, if_neg hzσl, if_neg (fun h : z = l => hlz h.symm)]; ring)
      (by rw [hw z k, if_neg hkj, if_neg hkz]; ring)
      (by rw [hw l k, if_neg hkσl, if_neg hkl]; ring)
      (by have : (2 / (m : ZMod 3)) - 1 - 2 / (m : ZMod 3) = -1 := by ring
          rw [this]; exact hdRo7SUReduceVAux_neg_one_ne_zero) hc
    exact contra (w z) (w l) hind (hmem z) (hmem l)

theorem hdRo7SUReduceVAux_phi_const_of_root_const {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    (hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ)
    (hrA : r ∈ A) (hu : ∀ i j, b.coord i u = b.coord j u) :
    ∀ i j, φ (b i) = φ (b j) := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have h0 : b.coord i u - b.coord j u = 0 := by rw [hu i j, sub_self]
    have h1 := (hdRo7SUReduceVAux_coord_iff b hNoT hsA hr hrA hij).mpr h0
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1

end CFSG.StandardType.HdRo7SU
