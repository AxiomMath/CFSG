module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVRefl
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUReduceVAux_move_eq_span {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) :
    ggLinMove (p := 3) r = Submodule.span (ZMod 3) {u} := by
  rw [ggLinMove]
  have h : r.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V) = -(Nop r) := by
    ext x; simp [Nop]
  rw [h, LinearMap.range_neg]
  exact ReflData.range_nop hdRo7SUReduceVAux_two_ne_zero hr

theorem hdRo7SUReduceVAux_sum_coord_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (i : Fin m) :
    (∑ k, b.coord k) (b i) = 1 := by
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [hdRo7SUReduceVAux_coord_basis b i i, if_pos rfl]
  · intro k _ hk
    rw [hdRo7SUReduceVAux_coord_basis b k i, if_neg (fun h : k = i => hk h)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem hdRo7SUReduceVAux_diff_mem_aug {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) :
    b i - b j ∈ SUAug 3 b := by
  rw [SUAug, LinearMap.mem_ker, map_sub, hdRo7SUReduceVAux_sum_coord_basis,
    hdRo7SUReduceVAux_sum_coord_basis, sub_self]

theorem hdRo7SUReduceVAux_superm_move_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {a : V ≃ₗ[ZMod 3] V} (ha : SUPerm 3 b a) : ggLinMove (p := 3) a ≤ SUAug 3 b := by
  obtain ⟨σ, hσ⟩ := ha
  rintro w ⟨v, rfl⟩
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
  have hv : a v - v = ∑ i, b.coord i v • (b (σ i) - b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hσ i, smul_sub, Module.Basis.coord_apply]
  rw [hv]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (hdRo7SUReduceVAux_diff_mem_aug b (σ i) i))

theorem hdRo7SUReduceVAux_const_refl_action {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) (ZMod 3) V) (hm3 : ¬ 3 ∣ m)
    {r : V ≃ₗ[ZMod 3] V} {u : V} {φ : V →ₗ[ZMod 3] ZMod 3} (hr : ReflData r u φ)
    (hu : ∀ i j, b.coord i u = b.coord j u) (hφ : ∀ i j, φ (b i) = φ (b j)) (v : V) :
    r v = v - ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b := by
  have hφv : ∀ v, φ v = φ (b 0) * (∑ i, b.coord i v) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hφ i 0, Module.Basis.coord_apply]
    ring
  have hu_eq : u = (b.coord 0 u) • SUOnes 3 b := by
    apply b.repr.injective
    ext k
    rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, map_smul,
      hdRo7SUReduceVAux_coord_ones, smul_eq_mul, mul_one, hu k 0]
  have hsumu : (∑ i, b.coord i u) = (m : ZMod 3) * b.coord 0 u := by
    have hconst : ∀ i ∈ (Finset.univ : Finset (Fin m)), b.coord i u = b.coord 0 u :=
      fun i _ => hu i 0
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hm_ne : (m : ZMod 3) ≠ 0 := by
    intro h
    exact hm3 ((CharP.cast_eq_zero_iff (ZMod 3) 3 m).mp h)
  have hkey : φ (b 0) * (b.coord 0 u) * (m : ZMod 3) = 2 := by
    have h := hr.pair
    rw [hφv u, hsumu] at h
    ring_nf at h ⊢
    exact h
  have hdc : φ (b 0) * (b.coord 0 u) = 2 / (m : ZMod 3) := by
    rw [eq_div_iff hm_ne]
    exact hkey
  calc r v = v - φ v • u := hr.apply v
    _ = v - (φ (b 0) * (∑ i, b.coord i v)) • u := by rw [hφv v]
    _ = v - (φ (b 0) * (b.coord 0 u) * (∑ i, b.coord i v)) • SUOnes 3 b := by
          conv_lhs => rw [hu_eq]
          rw [smul_smul]
          congr 1
          ring_nf
    _ = v - ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b := by rw [hdc]

theorem hdRo7SUReduceVAux_const_refl_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) (ZMod 3) V) (hm3 : ¬ 3 ∣ m)
    {r r' : V ≃ₗ[ZMod 3] V} {u u' : V} {φ φ' : V →ₗ[ZMod 3] ZMod 3}
    (hr : ReflData r u φ) (hr' : ReflData r' u' φ')
    (hu : ∀ i j, b.coord i u = b.coord j u) (hu' : ∀ i j, b.coord i u' = b.coord j u')
    (hφ : ∀ i j, φ (b i) = φ (b j)) (hφ' : ∀ i j, φ' (b i) = φ' (b j)) :
    r = r' := by
  ext v
  rw [hdRo7SUReduceVAux_const_refl_action b hm3 hr hu hφ v,
    hdRo7SUReduceVAux_const_refl_action b hm3 hr' hu' hφ' v]

theorem hdRo7SUReduceVAux_const_commute {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a)
    {s t : V ≃ₗ[ZMod 3] V} {u k : V} {φ ψ : V →ₗ[ZMod 3] ZMod 3}
    (hs : ReflData s u φ) (ht : ReflData t k ψ) (hsA : s ∈ A) (htA : t ∈ A)
    (hφU : ∀ w ∈ SUAug 3 b, φ w = 0) (hkU : k ∈ SUAug 3 b) : s * t = t * s := by
  have hφk : φ k = 0 := hφU k hkU
  have hψu : ψ u = 0 := hdRo7SUReduceVAux_zero_pair hNoT hs ht hsA htA hφk
  have hsk : s k = k := by rw [hs.apply k, hφk, zero_smul, sub_zero]
  have hsinv : s⁻¹ = s := by
    rw [← mul_one s⁻¹, ← hs.mul_self, ← mul_assoc, inv_mul_cancel, one_mul]
  have hψs : (ψ ∘ₗ (s.symm : V →ₗ[ZMod 3] V)) = ψ := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hv : s.symm v = s v := by rw [show s.symm = s⁻¹ from rfl, hsinv]
    rw [hv, hs.apply v, map_sub, map_smul, hψu, smul_zero, sub_zero]
  have hconj : ReflData (s * t * s⁻¹) k ψ := by
    have h := ht.conj s
    rwa [hsk, hψs] at h
  have heq : s * t * s⁻¹ = t := by
    ext v
    rw [hconj.apply v, ht.apply v]
  calc s * t = (s * t * s⁻¹) * s := by group
    _ = t * s := by rw [heq]

theorem hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge {α : Type*} (R : α → α → Prop) {a : α}
    (h : ∀ b, R a b → False) {b : α} (hab : Relation.ReflTransGen R a b) : b = a := by
  induction hab with
  | refl => rfl
  | tail _ hbc ih => exact (h _ (ih ▸ hbc)).elim

theorem hdRo7SUReduceVAux_move_le_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (a : V ≃ₗ[ZMod 3] V) :
    ggLinMove (p := 3) a ≤ SUAug 3 b ↔ ∀ v, a v - v ∈ SUAug 3 b := by
  rw [ggLinMove]
  constructor
  · intro h v; exact h ⟨v, rfl⟩
  · rintro h w ⟨v, rfl⟩; exact h v

theorem hdRo7SUReduceVAux_map_aug_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    {x : V ≃ₗ[ZMod 3] V} (hx : ∀ v, x v - v ∈ SUAug 3 b) :
    (SUAug 3 b).map x.toLinearMap = SUAug 3 b := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  have hle : (SUAug 3 b).map x.toLinearMap ≤ SUAug 3 b := by
    rintro _ ⟨w, hw, rfl⟩
    have hxw := hx w
    have hsplit : x w = w + (x w - w) := by abel
    change x w ∈ SUAug 3 b
    rw [hsplit]
    exact Submodule.add_mem _ hw hxw
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective x.toLinearMap x.injective _)).symm

@[expose] def hdRo7SUReduceVAux_augStab {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) :
    Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {x | ∀ v, x v - v ∈ SUAug 3 b}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro x y hx hy v
    have hxy : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [hxy]
    exact Submodule.add_mem _ (hx (y v)) (hy v)
  inv_mem' := by
    intro x hx v
    have heq : (SUAug 3 b).map x.toLinearMap = SUAug 3 b :=
      hdRo7SUReduceVAux_map_aug_eq b hx
    have hsub : x v - v ∈ (SUAug 3 b).map x.toLinearMap := by rw [heq]; exact hx v
    obtain ⟨w, hw, hwx⟩ := hsub
    have hxinv : x⁻¹ v - v = -(x⁻¹ (x v - v)) := by
      rw [map_sub, show x⁻¹ (x v) = v by simp]; abel
    rw [hxinv]
    exact Submodule.neg_mem _ (by rw [← hwx]; simpa using hw)

theorem hdRo7SUReduceVAux_const_of_preserves_aug {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (H A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hD : SULinData 3 m V b H A)
    (hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A)
    (hHU : ∀ a ∈ H, ∀ w ∈ SUAug 3 b, a w ∈ SUAug 3 b)
    {s : V ≃ₗ[ZMod 3] V} (hsH : s ∈ H) (hsrefl : GGLinRefl (p := 3) s)
    (hsmove : ¬ ggLinMove (p := 3) s ≤ SUAug 3 b) :
    ∃ (u : V) (φ : V →ₗ[ZMod 3] ZMod 3), ReflData s u φ ∧
      (∀ i j, b.coord i u = b.coord j u) ∧ (∀ i j, φ (b i) = φ (b j)) ∧
      u ∉ SUAug 3 b := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨u, φ, hrd⟩ := hdRo7SUReduceVAux_reflData s hsrefl
  have hu_not : u ∉ SUAug 3 b := by
    intro hu
    apply hsmove
    rw [hdRo7SUReduceVAux_move_eq_span hrd, Submodule.span_le, Set.singleton_subset_iff]
    exact hu
  have hφU : ∀ w ∈ SUAug 3 b, φ w = 0 := by
    intro w hw
    have hsw : s w - w ∈ SUAug 3 b := Submodule.sub_mem _ (hHU s hsH w hw) hw
    rw [hrd.apply w] at hsw
    have hstep : w - φ w • u - w = (-(φ w)) • u := by module
    rw [hstep] at hsw
    by_contra hφ
    apply hu_not
    have hc : -(φ w) ≠ 0 := neg_ne_zero.mpr hφ
    have : u = (-(φ w))⁻¹ • ((-(φ w)) • u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsw
  have hφconst : ∀ i j, φ (b i) = φ (b j) := by
    intro i j
    have h0 : φ (b i - b j) = 0 := hφU _ (hdRo7SUReduceVAux_diff_mem_aug b i j)
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  have hsuA : s ∈ A := hD.hHA hsH
  have huconst : ∀ i j, b.coord i u = b.coord j u :=
    hdRo7SUReduceVAux_root_const_of_phi_const b hD.hNoT hsA hrd hsuA hφconst
  exact ⟨u, φ, hrd, huconst, hφconst, hu_not⟩

theorem hdRo7SUReduceVAux_not_preserves_aug {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)) (hD : SULinData 3 m V b H A)
    (hV : ∃ r ∈ H, GGLinRefl (p := 3) r ∧ ¬ ggLinMove (p := 3) r ≤ SUAug 3 b) :
    ¬ (∀ a ∈ H, ∀ w ∈ SUAug 3 b, a w ∈ SUAug 3 b) := by
  intro hHU
  have hm7 : 7 ≤ m := hD.hm
  haveI : NeZero m := ⟨by omega⟩
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨S, hS, hHcl, hSconn⟩ := hD.hgen
  have hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A := by
    intro i j hij
    exact hD.hHA (hD.hPH _ ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩)
  have hex : ∃ s ∈ S, ¬ ggLinMove (p := 3) s ≤ SUAug 3 b := by
    by_contra h
    push Not at h
    have hKH : H ≤ hdRo7SUReduceVAux_augStab b := by
      rw [hHcl]
      refine (Subgroup.closure_le _).mpr ?_
      intro s hs
      exact (hdRo7SUReduceVAux_move_le_iff b s).mp (h s hs)
    obtain ⟨r, hrH, _hrrefl, hrmove⟩ := hV
    exact hrmove ((hdRo7SUReduceVAux_move_le_iff b r).mpr (hKH hrH))
  obtain ⟨s0, hs0S, hs0move⟩ := hex
  obtain ⟨hs0H, hs0refl⟩ := hS s0 hs0S
  obtain ⟨u0, φ0, hrd0, hu0const, hφ0const, _hu0not⟩ :=
    hdRo7SUReduceVAux_const_of_preserves_aug b H A hD hsA hHU hs0H hs0refl hs0move
  have hs0A : s0 ∈ A := hD.hHA hs0H
  have hφ0U : ∀ w ∈ SUAug 3 b, φ0 w = 0 := by
    intro w hw
    have hsw : s0 w - w ∈ SUAug 3 b := Submodule.sub_mem _ (hHU s0 hs0H w hw) hw
    rw [hrd0.apply w] at hsw
    have hstep : w - φ0 w • u0 - w = (-(φ0 w)) • u0 := by module
    rw [hstep] at hsw
    by_contra hφ
    have hc : -(φ0 w) ≠ 0 := neg_ne_zero.mpr hφ
    have hu0not' : u0 ∉ SUAug 3 b := by
      intro hu
      apply hs0move
      rw [hdRo7SUReduceVAux_move_eq_span hrd0, Submodule.span_le, Set.singleton_subset_iff]
      exact hu
    apply hu0not'
    have : u0 = (-(φ0 w))⁻¹ • ((-(φ0 w)) • u0) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsw
  have hcomm : ∀ t ∈ S, Commute s0 t := by
    intro t htS
    have htH : t ∈ H := (hS t htS).1
    have htA : t ∈ A := hD.hHA htH
    by_cases htmove : ggLinMove (p := 3) t ≤ SUAug 3 b
    · obtain ⟨u1, φ1, hrd1⟩ := hdRo7SUReduceVAux_reflData t (hS t htS).2
      have hu1U : u1 ∈ SUAug 3 b := by
        rw [hdRo7SUReduceVAux_move_eq_span hrd1] at htmove
        exact htmove (Submodule.mem_span_singleton_self u1)
      exact hdRo7SUReduceVAux_const_commute b hD.hNoT hrd0 hrd1 hs0A htA hφ0U hu1U
    · obtain ⟨u1, φ1, hrd1, hu1const, hφ1const, _⟩ :=
        hdRo7SUReduceVAux_const_of_preserves_aug b H A hD hsA hHU htH (hS t htS).2 htmove
      have heq : t = s0 :=
        hdRo7SUReduceVAux_const_refl_unique b hD.h3 hrd1 hrd0 hu1const hu0const hφ1const hφ0const
      rw [heq]
  have hSsing : S = {s0} := by
    ext t
    constructor
    · intro ht
      have := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
        (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) (fun b hb => hb.2.2 (hcomm b hb.2.1))
        (hSconn s0 hs0S t ht)
      rw [Set.mem_singleton_iff]; exact this
    · intro ht
      rw [Set.mem_singleton_iff] at ht; subst ht; exact hs0S
  have hs0sq : s0 * s0 = 1 := hs0refl.1
  have hsinv0 : s0⁻¹ = s0 := by
    rw [← mul_one s0⁻¹, ← hs0sq, ← mul_assoc, inv_mul_cancel, one_mul]
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let τ : V ≃ₗ[ZMod 3] V := b.equiv b (Equiv.swap i j)
  have hτH : τ ∈ H := hD.hPH τ ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩
  have hτclos : τ ∈ Subgroup.closure ({s0} : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [← hSsing, ← hHcl]; exact hτH
  have hτcases : τ = 1 ∨ τ = s0 := by
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s0) ?_ ?_ ?_ ?_ hτclos
    · intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · left; rw [one_mul]
      · right; rw [one_mul]
      · right; rw [mul_one]
      · left; rw [hs0sq]
    · intro x _ hx
      rcases hx with rfl | rfl
      · left; rw [inv_one]
      · right; rw [hsinv0]
  have hτne1 : τ ≠ 1 := by
    intro h
    have h1 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (b i)) h
    simp only [τ, Module.Basis.equiv_apply, Equiv.swap_apply_left, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_apply] at h1
    exact hij (b.injective h1).symm
  have hτmoveU : ggLinMove (p := 3) τ ≤ SUAug 3 b :=
    hdRo7SUReduceVAux_superm_move_le b ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩
  rcases hτcases with h | h
  · exact hτne1 h
  · exact hs0move (h ▸ hτmoveU)

end CFSG.StandardType.HdRo7SU
