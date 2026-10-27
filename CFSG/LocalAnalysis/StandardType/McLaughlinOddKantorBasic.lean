module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOdd
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith commutatorElement_apply_of_transvection)

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def NoNormalExpP (T : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ T → (∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    (∀ n ∈ N, n ^ p = 1) → N = ⊥

@[expose] def unipSub (T : Subgroup (V ≃ₗ[ZMod p] V)) (X : Submodule (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | g ∈ T ∧ (∀ x, g x - x ∈ X) ∧ ∀ x ∈ X, g x = x}
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨T.mul_mem ha hb, fun x => ?_, fun x hx => ?_⟩
    · have : (a * b) x - x = (a (b x) - b x) + (b x - x) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [this]
      exact X.add_mem (ha1 _) (hb1 x)
    · rw [LinearEquiv.mul_apply, hb2 x hx, ha2 x hx]
  one_mem' := ⟨T.one_mem, fun x => by simp, fun x _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    have hinv : ∀ y, a⁻¹ y = a.symm y := fun _ => rfl
    refine ⟨T.inv_mem ha, fun x => ?_, fun x hx => ?_⟩
    · have h := ha1 (a.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      have : a⁻¹ x - x = -(x - a.symm x) := by rw [hinv]; abel
      rw [this]
      exact X.neg_mem h
    · rw [hinv, LinearEquiv.symm_apply_eq, ha2 x hx]

theorem unip_pow_apply {X : Submodule (ZMod p) V} {g : V ≃ₗ[ZMod p] V}
    (h1 : ∀ x, g x - x ∈ X) (h2 : ∀ x ∈ X, g x = x) (k : ℕ) (x : V) :
    (g ^ k) x = x + k • (g x - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, h2 _ (h1 x), succ_nsmul]
    abel

theorem eq_one_of_unip {T : Subgroup (V ≃ₗ[ZMod p] V)} (hT : NoNormalExpP T)
    {X : Submodule (ZMod p) V} (hX : ∀ g ∈ T, ∀ x ∈ X, g x ∈ X) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ T) (h1 : ∀ x, g x - x ∈ X) (h2 : ∀ x ∈ X, g x = x) : g = 1 := by
  have hN : unipSub T X = ⊥ := by
    refine hT _ (fun n hn => hn.1) (fun a ha n hn => ?_) (fun n hn => ?_)
    · obtain ⟨hnT, hn1, hn2⟩ := hn
      have hainv : ∀ y, a⁻¹ y = a.symm y := fun _ => rfl
      refine ⟨T.mul_mem (T.mul_mem ha hnT) (T.inv_mem ha), fun x => ?_, fun x hx => ?_⟩
      · have : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hainv, map_sub,
            LinearEquiv.apply_symm_apply]
        rw [this]
        exact hX a ha _ (hn1 _)
      · have hx' : a.symm x ∈ X := hX a⁻¹ (T.inv_mem ha) x hx
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hainv, hn2 _ hx',
          LinearEquiv.apply_symm_apply]
    · obtain ⟨-, hn1, hn2⟩ := hn
      refine LinearEquiv.ext fun x => ?_
      rw [unip_pow_apply hn1 hn2, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self,
        zero_smul, add_zero]
      rfl
  have : g ∈ unipSub T X := ⟨hg, h1, h2⟩
  rw [hN, Subgroup.mem_bot] at this
  exact this

theorem transvection_ne_one {t : V ≃ₗ[ZMod p] V} {v : V} {f : Module.Dual (ZMod p) V}
    (h : IsTransvectionWith t v f) : t ≠ 1 := by
  rintro rfl
  apply h.2.1
  refine LinearMap.ext fun x => ?_
  have hx := h.2.2.2 x
  change x = x + f x • v at hx
  have h0 : f x • v = 0 := by
    have := congrArg (fun y => y - x) hx
    simpa using this.symm
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h0).resolve_right h.1

theorem transvection_center_mem_span {t : V ≃ₗ[ZMod p] V} {v v' : V}
    {f f' : Module.Dual (ZMod p) V} (h : IsTransvectionWith t v f)
    (h' : IsTransvectionWith t v' f') : v' ∈ Submodule.span (ZMod p) {v} := by
  obtain ⟨x, hx⟩ : ∃ x, f' x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact h'.2.1 (LinearMap.ext hno)
  have e : f' x • v' = f x • v := by
    have h1 := h.2.2.2 x
    have h2 := h'.2.2.2 x
    rw [h1] at h2
    exact (add_left_cancel h2).symm
  refine Submodule.mem_span_singleton.mpr ⟨(f' x)⁻¹ * f x, ?_⟩
  rw [mul_smul, ← e, smul_smul, inv_mul_cancel₀ hx, one_smul]

theorem transvection_axis_vanish {t : V ≃ₗ[ZMod p] V} {v : V}
    {f : Module.Dual (ZMod p) V} (h : IsTransvectionWith t v f) {X : Submodule (ZMod p) V}
    (hv : v ∉ X) (hX : ∀ x ∈ X, t x ∈ X) : ∀ x ∈ X, f x = 0 := by
  intro x hx
  by_contra hfx
  apply hv
  have h1 : f x • v ∈ X := by
    have := X.sub_mem (hX x hx) hx
    rwa [h.2.2.2 x, add_sub_cancel_left] at this
  have := X.smul_mem (f x)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hfx, one_smul] at this

theorem commute_of_isTransvectionWith {t s : V ≃ₗ[ZMod p] V} {v w : V}
    {f g : Module.Dual (ZMod p) V} (ht : IsTransvectionWith t v f) (hs : IsTransvectionWith s w g)
    (hfw : f w = 0) (hgv : g v = 0) : Commute t s := by
  refine LinearEquiv.ext fun x => ?_
  change t (s x) = s (t x)
  rw [ht.2.2.2, hs.2.2.2, hs.2.2.2, ht.2.2.2, map_add, map_add, map_smul, map_smul, hfw, hgv,
    smul_zero, smul_zero, add_zero, add_zero]
  abel

theorem apply_eq_zero_of_commute {t s : V ≃ₗ[ZMod p] V} {v w : V}
    {f g : Module.Dual (ZMod p) V} (ht : IsTransvectionWith t v f) (hs : IsTransvectionWith s w g)
    (hc : Commute t s) : f w = 0 ∧ g v = 0 := by
  have key : ∀ x, (g x * f w) • v = (f x * g v) • w := by
    intro x
    have h := LinearEquiv.congr_fun hc.eq x
    change t (s x) = s (t x) at h
    rw [ht.2.2.2, hs.2.2.2, hs.2.2.2, ht.2.2.2, map_add, map_add, map_smul, map_smul] at h
    have h' : (g x * f w) • v - (f x * g v) • w =
        (x + g x • w + (f x + g x • f w) • v) - (x + f x • v + (g x + f x • g v) • w) := by
      simp only [smul_eq_mul]
      module
    rw [h, sub_self] at h'
    exact sub_eq_zero.mp h'
  obtain ⟨x₁, hx₁⟩ : ∃ x, f x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact ht.2.1 (LinearMap.ext hno)
  obtain ⟨x₂, hx₂⟩ : ∃ x, g x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hs.2.1 (LinearMap.ext hno)
  by_cases hdep : w ∈ Submodule.span (ZMod p) {v}
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hdep
    have hc0 : c ≠ 0 := by rintro rfl; exact hs.1 (zero_smul _ v)
    refine ⟨by rw [map_smul, ht.2.2.1, smul_zero], ?_⟩
    have := hs.2.2.1
    rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hc0
  · have hzero : ∀ x, f x * g v = 0 := by
      intro x
      by_contra hne
      apply hdep
      refine Submodule.mem_span_singleton.mpr ⟨(f x * g v)⁻¹ * (g x * f w), ?_⟩
      rw [mul_smul, key x, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hgv : g v = 0 := (mul_eq_zero.mp (hzero x₁)).resolve_left hx₁
    refine ⟨?_, hgv⟩
    have h2 := key x₂
    rw [hgv, mul_zero, zero_smul] at h2
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right ht.1)).resolve_left hx₂

@[expose] def cenSet (D : Set (V ≃ₗ[ZMod p] V)) : Set V :=
  {v | ∃ t ∈ D, ∃ f, IsTransvectionWith t v f}

@[expose] noncomputable def cenSpan (D : Set (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V :=
  Submodule.span (ZMod p) (cenSet D)

@[expose] def fixSub (T : Subgroup (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V where
  carrier := {x | ∀ g ∈ T, g x = x}
  add_mem' := fun {x y} hx hy g hg => by rw [map_add, hx g hg, hy g hg]
  zero_mem' := fun g _ => map_zero g
  smul_mem' := fun c x hx g hg => by rw [map_smul, hx g hg]

theorem center_mem_cenSpan {D : Set (V ≃ₗ[ZMod p] V)} {t : V ≃ₗ[ZMod p] V} (ht : t ∈ D) {v : V}
    {f : Module.Dual (ZMod p) V} (h : IsTransvectionWith t v f) : v ∈ cenSpan D :=
  Submodule.subset_span ⟨t, ht, f, h⟩

variable {D : Set (V ≃ₗ[ZMod p] V)}

theorem mem_fixSub_closure (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) {x : V} :
    x ∈ fixSub (Subgroup.closure D) ↔ ∀ t ∈ D, ∀ v f, IsTransvectionWith t v f → f x = 0 := by
  constructor
  · intro hx t ht v f h
    have := hx t (Subgroup.subset_closure ht)
    rw [h.2.2.2] at this
    have h0 : f x • v = 0 := by simpa using this
    exact (smul_eq_zero.mp h0).resolve_right h.1
  · intro hx g hg
    refine Subgroup.closure_induction (p := fun g _ => g x = x) (fun t ht => ?_) rfl
      (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) hg
    · obtain ⟨v, f, h⟩ := hD t ht
      rw [h.2.2.2, hx t ht v f h, zero_smul, add_zero]
    · rw [LinearEquiv.mul_apply, hb, ha]
    · change a.symm x = x
      rw [LinearEquiv.symm_apply_eq, ha]

theorem sub_mem_cenSpan (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ Subgroup.closure D) (x : V) : g x - x ∈ cenSpan D := by
  refine Subgroup.closure_induction (p := fun g _ => ∀ x, g x - x ∈ cenSpan D)
    (fun t ht x => ?_) (fun x => by simp) (fun a b _ _ ha hb x => ?_) (fun a _ ha x => ?_) hg x
  · obtain ⟨v, f, h⟩ := hD t ht
    rw [h.2.2.2, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (center_mem_cenSpan ht h)
  · have : (a * b) x - x = (a (b x) - b x) + (b x - x) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [this]
    exact Submodule.add_mem _ (ha _) (hb x)
  · have h := ha (a.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    have : a⁻¹ x - x = -(x - a.symm x) := by
      change a.symm x - x = _
      abel
    rw [this]
    exact Submodule.neg_mem _ h

theorem cenSpan_invariant (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Subgroup.closure D) {x : V} (hx : x ∈ cenSpan D) :
    g x ∈ cenSpan D := by
  have := Submodule.add_mem _ (sub_mem_cenSpan hD hg x) hx
  rwa [sub_add_cancel] at this

@[expose] def IsConnTr (D : Set (V ≃ₗ[ZMod p] V)) : Prop :=
  ∀ P ⊆ D, (∀ t ∈ P, ∀ s ∈ D, s ∉ P → Commute t s) → P = ∅ ∨ P = D

theorem irreducible_of_isConnTr (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hconn : IsConnTr D) (hT : NoNormalExpP (Subgroup.closure D)) (hU : cenSpan D = ⊤)
    (hC : fixSub (Subgroup.closure D) = ⊥) :
    ∀ X : Submodule (ZMod p) V, (∀ h ∈ Subgroup.closure D, ∀ x ∈ X, h x ∈ X) →
      X = ⊥ ∨ X = ⊤ := by
  intro X hX
  set P : Set (V ≃ₗ[ZMod p] V) := {t | t ∈ D ∧ ∃ v f, IsTransvectionWith t v f ∧ v ∈ X}
    with hPdef
  have hPD : P ⊆ D := fun t ht => ht.1
  have hout : ∀ s ∈ D, s ∉ P → ∀ w g, IsTransvectionWith s w g → w ∉ X :=
    fun s hs hsP w g hw hwX => hsP ⟨hs, w, g, hw, hwX⟩
  have hcomm : ∀ t ∈ P, ∀ s ∈ D, s ∉ P → Commute t s := by
    rintro t ⟨htD, v, f, ht, hvX⟩ s hs hsP
    obtain ⟨w, g, hsw⟩ := hD s hs
    have hgX : ∀ x ∈ X, g x = 0 :=
      transvection_axis_vanish hsw (hout s hs hsP w g hsw) (hX s (Subgroup.subset_closure hs))
    have hgv : g v = 0 := hgX v hvX
    refine commute_of_isTransvectionWith ht hsw ?_ hgv
    by_contra hfw
    have hc := commutatorElement_apply_of_transvection ht hsw hgv
    have hmem : ⁅t, s⁆ ∈ Subgroup.closure D := by
      rw [commutatorElement_def]
      have h1 := Subgroup.subset_closure (k := D) htD
      have h2 := Subgroup.subset_closure (k := D) hs
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    have h1 := eq_one_of_unip hT hX hmem
      (fun x => by rw [hc x, add_sub_cancel_left]; exact X.smul_mem _ hvX)
      (fun x hx => by rw [hc x, hgX x hx, mul_zero, zero_smul, add_zero])
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hsw.2.1 (LinearMap.ext hno)
    have h2 := hc x
    rw [h1] at h2
    change x = x + (f w * g x) • v at h2
    have h3 : (f w * g x) • v = 0 := by
      have := congrArg (fun y => y - x) h2
      simpa using this.symm
    exact mul_ne_zero hfw hx ((smul_eq_zero.mp h3).resolve_right ht.1)
  rcases hconn P hPD hcomm with h | h
  · left
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [mem_fixSub_closure hD]
    intro t ht v f hvf
    have htP : t ∉ P := by rw [h]; exact Set.notMem_empty t
    exact transvection_axis_vanish hvf (hout t ht htP v f hvf)
      (hX t (Subgroup.subset_closure ht)) x hx
  · right
    rw [eq_top_iff, ← hU, cenSpan, Submodule.span_le]
    rintro v ⟨t, ht, f, hvf⟩
    have htP : t ∈ P := by rw [h]; exact ht
    obtain ⟨-, v', f', hv'f', hv'X⟩ := htP
    have hv := transvection_center_mem_span hv'f' hvf
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv'X)) hv

end CFSG.StandardType.McLaughlinOdd
