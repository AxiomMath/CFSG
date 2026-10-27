module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUO
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace NoOffOm

open Module Matrix MulAction

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Form

variable {p : ℕ}

@[expose] noncomputable def dotB (p : ℕ) : LinearMap.BilinForm (ZMod p) (Fin 4 → ZMod p) :=
  LinearMap.mk₂ (ZMod p) (fun x y => x ⬝ᵥ y) add_dotProduct smul_dotProduct dotProduct_add
    dotProduct_smul

theorem dotB_apply (x y : Fin 4 → ZMod p) : dotB p x y = x ⬝ᵥ y := rfl

theorem dotB_comm (x y : Fin 4 → ZMod p) : dotB p x y = dotB p y x := dotProduct_comm x y

theorem dotB_nondegenerate : (dotB p).Nondegenerate := by
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · have := hx (Pi.single i 1)
    rwa [dotB_apply, dotProduct_single, mul_one] at this
  · have := hy (Pi.single i 1)
    rwa [dotB_apply, single_dotProduct, one_mul] at this

theorem eq_zero_of_dotB {x : Fin 4 → ZMod p} (hx : ∀ y, dotB p x y = 0) : x = 0 :=
  dotB_nondegenerate.1 x hx

theorem exists_dotB_eq_one [Fact p.Prime] {c : Fin 4 → ZMod p} (hc : c ≠ 0) :
    ∃ v₀, dotB p c v₀ = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  exact ⟨Pi.single i (c i)⁻¹, by rw [dotB_apply, dotProduct_single, mul_inv_cancel₀ hi]⟩

theorem mem_span_of_forall_dotB [Fact p.Prime] {c u : Fin 4 → ZMod p} (hc : c ≠ 0)
    (hu : ∀ y, dotB p c y = 0 → dotB p u y = 0) : u ∈ (ZMod p) ∙ c := by
  obtain ⟨v₀, hv₀⟩ := exists_dotB_eq_one hc
  have h1 : u - dotB p u v₀ • c = 0 := by
    refine eq_zero_of_dotB fun y => ?_
    have h2 := hu (y - dotB p c y • v₀) (by rw [map_sub, map_smul, hv₀, smul_eq_mul, mul_one,
      sub_self])
    rw [map_sub, map_smul, smul_eq_mul, dotB_comm u v₀] at h2
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      dotB_comm u v₀]
    linear_combination h2
  rw [sub_eq_zero] at h1
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)

theorem neg_inv_mul_smul_eq [Fact p.Prime] {a b : ZMod p} {y z : Fin 4 → ZMod p} (ha : a ≠ 0)
    (h : b • y + a • z = 0) : (-(a⁻¹ * b)) • y = z := by
  have h1 : b • y = -(a • z) := eq_neg_iff_add_eq_zero.mpr h
  rw [neg_smul, mul_smul, h1, smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem mem_span_triple [Fact p.Prime] {W : Submodule (ZMod p) (Fin 4 → ZMod p)}
    (hW : finrank (ZMod p) W = 3) {c u x w : Fin 4 → ZMod p} (hc : c ∈ W) (hu : u ∈ W)
    (hx : x ∈ W) (hw : w ∈ W) (hc0 : c ≠ 0) (hu' : u ∉ (ZMod p) ∙ c)
    (hx' : x ∉ Submodule.span (ZMod p) {c, u}) :
    ∃ a b d : ZMod p, w = a • c + b • u + d • x := by
  classical
  set v : Fin 4 → W := ![⟨c, hc⟩, ⟨u, hu⟩, ⟨x, hx⟩, ⟨w, hw⟩] with hv
  have hnli : ¬ LinearIndependent (ZMod p) v := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hW] at this
    omega
  rw [Fintype.linearIndependent_iff] at hnli
  push Not at hnli
  obtain ⟨g, hg, i, hi⟩ := hnli
  have hg' : g 0 • c + g 1 • u + g 2 • x + g 3 • w = 0 := by
    have := congrArg Subtype.val hg
    simpa [Fin.sum_univ_four, hv] using this
  by_cases h3 : g 3 = 0
  · exfalso
    rw [h3, zero_smul, add_zero] at hg'
    by_cases h2 : g 2 = 0
    · rw [h2, zero_smul, add_zero] at hg'
      by_cases h1 : g 1 = 0
      · rw [h1, zero_smul, add_zero, smul_eq_zero] at hg'
        have h0 : g 0 = 0 := hg'.resolve_right hc0
        fin_cases i <;> simp_all
      · apply hu'
        rw [Submodule.mem_span_singleton]
        exact ⟨_, neg_inv_mul_smul_eq h1 hg'⟩
    · apply hx'
      have hx2 : (-((g 2)⁻¹ * 1)) • (g 0 • c + g 1 • u) = x :=
        neg_inv_mul_smul_eq h2 (by rw [one_smul]; exact hg')
      rw [← hx2]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · refine ⟨-(g 3)⁻¹ * g 0, -(g 3)⁻¹ * g 1, -(g 3)⁻¹ * g 2, ?_⟩
    have hw3 : (-((g 3)⁻¹ * 1)) • (g 0 • c + g 1 • u + g 2 • x) = w :=
      neg_inv_mul_smul_eq h3 (by rw [one_smul]; exact hg')
    rw [← hw3, mul_one, smul_add, smul_add, smul_smul, smul_smul, smul_smul, neg_mul, neg_mul,
      neg_mul]

theorem two_ne_zero_of_ne_two [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h1)

theorem exists_smul_add_of_fix [Fact p.Prime] (hp2 : p ≠ 2)
    {T : Module.End (ZMod p) (Fin 4 → ZMod p)} (hTp : T ^ p = 1)
    (hTβ : ∀ x y, dotB p (T x) (T y) = dotB p x y) {c : Fin 4 → ZMod p} (hc0 : c ≠ 0)
    (hcc : dotB p c c = 0) (hTc : T c = c) {w : Fin 4 → ZMod p} (hw : dotB p c w = 0) :
    ∃ μ : ZMod p, T w = w + μ • c := by
  classical
  have hpp : p.Prime := Fact.out
  set W : Submodule (ZMod p) (Fin 4 → ZMod p) := LinearMap.ker (dotB p c) with hWdef
  have hmemW : ∀ y, y ∈ W ↔ dotB p c y = 0 := fun y => LinearMap.mem_ker
  have hW3 : finrank (ZMod p) W = 3 := by
    obtain ⟨v₀, hv₀⟩ := exists_dotB_eq_one hc0
    have hsurj : LinearMap.range (dotB p c) = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun a => ⟨a • v₀, ?_⟩
      rw [map_smul, hv₀, smul_eq_mul, mul_one]
    have h1 := LinearMap.finrank_range_add_finrank_ker (dotB p c)
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun, ← hWdef] at h1
    omega
  have hTW : ∀ y ∈ W, T y ∈ W := fun y hy => by
    have hy' : dotB p c y = 0 := (hmemW y).mp hy
    refine (hmemW (T y)).mpr ?_
    rw [← hTc, hTβ]
    exact hy'
  set N : Module.End (ZMod p) (Fin 4 → ZMod p) := T - 1 with hN
  have hNapply : ∀ y, N y = T y - y := fun y => rfl
  have hNW : ∀ y ∈ W, N y ∈ W := fun y hy => W.sub_mem (hTW y hy) hy
  have hNp : N ^ p = 0 := by
    have hinj :
        Function.Injective (algebraMap (ZMod p) (Module.End (ZMod p) (Fin 4 → ZMod p))) := by
      refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
      have h1 := LinearMap.congr_fun ha (Pi.single 0 1)
      rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
      have h2 := congrFun h1 0
      simpa using h2
    have : CharP (Module.End (ZMod p) (Fin 4 → ZMod p)) p := charP_of_injective_algebraMap hinj p
    rw [hN, sub_pow_char_of_commute p (Commute.one_right T), hTp, one_pow, sub_self]
  obtain ⟨y, hyW, hyc⟩ : ∃ y ∈ W, y ∉ (ZMod p) ∙ c := by
    by_contra hcon
    push Not at hcon
    have h1 := Submodule.finrank_mono (show W ≤ (ZMod p) ∙ c from hcon)
    rw [hW3, finrank_span_singleton hc0] at h1
    omega
  have hex : ∃ k : ℕ, (N ^ (k + 1)) y ∈ (ZMod p) ∙ c :=
    ⟨p - 1, by rw [Nat.sub_add_cancel hpp.one_lt.le, hNp, LinearMap.zero_apply]; exact zero_mem _⟩
  have hNkW : ∀ j : ℕ, (N ^ j) y ∈ W := by
    intro j
    induction j with
    | zero => exact hyW
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hNW _ ih
  set u := (N ^ Nat.find hex) y with hu
  have huW : u ∈ W := hNkW _
  have huc : u ∉ (ZMod p) ∙ c := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hk0
    · rw [hu, hk0, pow_zero, Module.End.one_apply]
      exact hyc
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      rw [hu, hj]
      exact this
  have hNu : N u ∈ (ZMod p) ∙ c := by
    have := Nat.find_spec hex
    rwa [pow_succ', Module.End.mul_apply] at this
  obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hNu
  have hTu : T u = u + ν • c := by
    rw [hν, hNapply]
    abel
  have hβuc : dotB p u c = 0 := by rw [dotB_comm]; exact (hmemW u).mp huW
  have hβcu : dotB p c u = 0 := (hmemW u).mp huW
  have hβwc : dotB p w c = 0 := by rw [dotB_comm]; exact hw
  by_cases hwu : w ∈ Submodule.span (ZMod p) {c, u}
  · obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hwu
    refine ⟨b * ν, ?_⟩
    rw [← hab, map_add, map_smul, map_smul, hTc, hTu, smul_add, smul_smul]
    abel
  have hwW : w ∈ W := (hmemW w).mpr hw
  obtain ⟨l, t, s, hTw⟩ := mem_span_triple hW3 ((hmemW c).mpr hcc) huW hwW (hTW w hwW) hc0 huc
    hwu
  have hpow : ∀ j : ℕ, ∃ a b : ZMod p, (T ^ j) w = a • c + b • u + s ^ j • w := by
    intro j
    induction j with
    | zero => exact ⟨0, 0, by simp⟩
    | succ j ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨a + b * ν + s ^ j * l, b + s ^ j * t, ?_⟩
      rw [pow_succ', Module.End.mul_apply, hab, map_add, map_add, map_smul, map_smul, map_smul,
        hTc, hTu, hTw]
      module
  have hs1 : s = 1 := by
    obtain ⟨a, b, hab⟩ := hpow p
    rw [hTp, Module.End.one_apply, ZMod.pow_card] at hab
    by_contra hs
    apply hwu
    have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have h1 : (1 - s) • w = a • c + b • u := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [hab]
      abel
    have h2 : w = (1 - s)⁻¹ • (a • c + b • u) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ h1s, one_smul]
    rw [h2]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have ht0 : t = 0 := by
    by_contra ht
    have e1 := hTβ u w
    rw [hTu, hTw, hs1, one_smul] at e1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hcc, hβuc, hβcu, hw] at e1
    have huu : dotB p u u = 0 := by
      have : t * dotB p u u = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left ht
    have e2 := hTβ w w
    rw [hTw, hs1, one_smul] at e2
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hcc, hβuc, hβcu, hw, hβwc, huu, dotB_comm w u] at e2
    have huw : dotB p u w = 0 := by
      have : (2 * t) * dotB p u w = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (two_ne_zero_of_ne_two hp2) ht)
    apply huc
    refine mem_span_of_forall_dotB hc0 fun z hz => ?_
    obtain ⟨a, b, d, rfl⟩ := mem_span_triple hW3 ((hmemW c).mpr hcc) huW hwW ((hmemW z).mpr hz)
      hc0 huc hwu
    simp only [map_add, map_smul, smul_eq_mul, hβuc, huu, huw, mul_zero, add_zero]
  refine ⟨l, ?_⟩
  rw [hTw, ht0, hs1, zero_smul, add_zero, one_smul, add_comm]

theorem card_fixedPoints_mul_card_lt [Fact p.Prime] {E : Type*} [Group E] [Finite E]
    [MulAction E (Fin 4 → ZMod p)] (hp2 : p ≠ 2) (hEp : ∀ e : E, e ^ p = 1)
    (hadd : ∀ (e : E) (x y : Fin 4 → ZMod p), e • (x + y) = e • x + e • y)
    (hQ : ∀ (e : E) (x : Fin 4 → ZMod p), dotB p (e • x) (e • x) = dotB p x x)
    (hne : ∃ (e : E) (x : Fin 4 → ZMod p), e • x ≠ x) :
    Nat.card (fixedPoints E (Fin 4 → ZMod p)) * Nat.card E <
      p ^ 4 * Nat.card {e : E // ∀ x : Fin 4 → ZMod p, e • x = x} := by
  classical
  have hpp : p.Prime := Fact.out
  have h2 := two_ne_zero_of_ne_two hp2
  have hzero : ∀ e : E, e • (0 : Fin 4 → ZMod p) = 0 := fun e => by
    simpa using hadd e 0 0
  have hnsmul : ∀ (e : E) (k : ℕ) (x : Fin 4 → ZMod p), e • (k • x) = k • (e • x) := by
    intro e k x
    induction k with
    | zero => rw [zero_smul, zero_smul, hzero]
    | succ k ih => rw [succ_nsmul, hadd, ih, succ_nsmul]
  have hsmul : ∀ (e : E) (a : ZMod p) (x : Fin 4 → ZMod p), e • (a • x) = a • (e • x) := by
    intro e a x
    have h1 : ∀ y : Fin 4 → ZMod p, a • y = a.val • y := fun y => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [h1, hnsmul, ← h1]
  let L : E → Module.End (ZMod p) (Fin 4 → ZMod p) := fun e =>
    { toFun := fun x => e • x, map_add' := hadd e, map_smul' := hsmul e }
  have hL : ∀ e x, L e x = e • x := fun e x => rfl
  have hLpow : ∀ (e : E) (k : ℕ) x, (L e ^ k) x = (e ^ k) • x := by
    intro e k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, ih, hL, ← mul_smul, ← pow_succ']
  have hLp : ∀ e, L e ^ p = 1 := fun e => LinearMap.ext fun x => by
    rw [hLpow, hEp, one_smul]
    rfl
  have hβ : ∀ (e : E) x y, dotB p (e • x) (e • y) = dotB p x y := by
    intro e x y
    have h1 := hQ e (x + y)
    rw [hadd] at h1
    simp only [map_add, LinearMap.add_apply, hQ e x, hQ e y] at h1
    rw [dotB_comm (e • y) (e • x), dotB_comm y x] at h1
    have : 2 * dotB p (e • x) (e • y) = 2 * dotB p x y := by linear_combination h1
    exact mul_left_cancel₀ h2 this
  have hpg : IsPGroup p E := fun e => ⟨1, by rw [pow_one]; exact hEp e⟩
  let C : Submodule (ZMod p) (Fin 4 → ZMod p) :=
    { carrier := {x | ∀ e : E, e • x = x}
      add_mem' := fun {x y} hx hy e => by rw [hadd, hx e, hy e]
      zero_mem' := fun e => hzero e
      smul_mem' := fun a x hx e => by rw [hsmul, hx e] }
  have hmemC : ∀ x, x ∈ C ↔ ∀ e : E, e • x = x := fun x => Iff.rfl
  set P := (dotB p).orthogonal C with hP
  have hmemP : ∀ t, t ∈ P ↔ ∀ s ∈ C, dotB p s t = 0 := fun t =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hfr := LinearMap.BilinForm.finrank_orthogonal dotB_nondegenerate C
  rw [← hP, Module.finrank_fin_fun] at hfr
  have hfrC := Submodule.finrank_le C
  rw [Module.finrank_fin_fun] at hfrC
  have : Module.Finite (ZMod p) C := Module.Finite.of_injective C.subtype C.injective_subtype
  have : Module.Finite (ZMod p) P := Module.Finite.of_injective P.subtype P.injective_subtype
  have hcardC : Nat.card C = p ^ finrank (ZMod p) C := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := C), Nat.card_zmod]
  have hcardP : Nat.card P = p ^ finrank (ZMod p) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := P), Nat.card_zmod]
  have hcard : Nat.card C * Nat.card P = p ^ 4 := by
    rw [hcardC, hcardP, ← pow_add, hfr]
    congr 1
    omega
  have hPinv : ∀ (e : E) t, t ∈ P → e • t ∈ P := by
    intro e t ht
    rw [hmemP] at ht ⊢
    intro s hs
    have := hβ e s t
    rw [(hmemC s).mp hs e] at this
    rw [this]
    exact ht s hs
  obtain ⟨c, hcC, hcP, hc0⟩ : ∃ c, c ∈ C ∧ c ∈ P ∧ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let act : MulAction E ↥P :=
      { smul := fun e t => ⟨e • (t : Fin 4 → ZMod p), hPinv e t t.2⟩
        one_smul := fun t => Subtype.ext (one_smul E (t : Fin 4 → ZMod p))
        mul_smul := fun e e' t => Subtype.ext (mul_smul e e' (t : Fin 4 → ZMod p)) }
    have hmod := hpg.card_modEq_card_fixedPoints ↥P
    have hPne : finrank (ZMod p) P ≠ 0 := by
      intro h0
      have hCtop : C = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
      obtain ⟨e, x, hx⟩ := hne
      exact hx ((hmemC x).mp (hCtop ▸ Submodule.mem_top) e)
    have hdvd : p ∣ Nat.card (fixedPoints E ↥P) := by
      apply Nat.dvd_of_mod_eq_zero
      rw [← hmod, hcardP]
      obtain ⟨k, hk⟩ : ∃ k, finrank (ZMod p) P = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_ne_zero hPne).symm⟩
      rw [hk, pow_succ, Nat.mul_mod_left]
    have h0fix : (0 : ↥P) ∈ fixedPoints E ↥P := fun e => Subtype.ext (hzero e)
    have hpos : 0 < Nat.card (fixedPoints E ↥P) := Nat.card_pos_iff.mpr ⟨⟨_, h0fix⟩, inferInstance⟩
    have hge : 2 ≤ Nat.card (fixedPoints E ↥P) :=
      le_trans hpp.two_le (Nat.le_of_dvd hpos hdvd)
    have : Nontrivial (fixedPoints E ↥P) := Finite.one_lt_card_iff_nontrivial.mp hge
    obtain ⟨⟨t, ht⟩, hne0⟩ := exists_ne (⟨0, h0fix⟩ : fixedPoints E ↥P)
    have htC : (t : Fin 4 → ZMod p) ∈ C := fun e => congrArg Subtype.val (ht e)
    have h1 := hcon t htC t.2
    exact hne0 (Subtype.ext (Subtype.ext h1))
  have hcc : dotB p c c = 0 := (hmemP c).mp hcP c hcC
  obtain ⟨v₀, hv₀⟩ := exists_dotB_eq_one hc0
  have hE : ∀ (e : E) (w : Fin 4 → ZMod p), dotB p c w = 0 → ∃ μ : ZMod p, e • w = w + μ • c := by
    intro e w hw
    exact exists_smul_add_of_fix hp2 (hLp e) (fun x y => hβ e x y) hc0 hcc ((hmemC c).mp hcC e)
      hw
  have hinj : ∀ (f : E) (ν : ZMod p), f • v₀ = v₀ + ν • c →
      ∀ x : Fin 4 → ZMod p, f • x = x := by
    intro f ν hf x
    have hW : ∀ w : Fin 4 → ZMod p, dotB p c w = 0 → f • w = w := by
      intro w hw
      obtain ⟨μ, hμ⟩ := hE f w hw
      have e1 := hβ f w v₀
      rw [hμ, hf] at e1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hcc,
        hv₀, dotB_comm w c, hw] at e1
      have hμ0 : μ = 0 := by linear_combination e1
      rw [hμ, hμ0, zero_smul, add_zero]
    have hν0 : ν = 0 := by
      have e2 := hβ f v₀ v₀
      rw [hf] at e2
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hcc,
        hv₀, dotB_comm v₀ c] at e2
      have : 2 * ν = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_left h2
    have hx : x = (x - dotB p c x • v₀) + dotB p c x • v₀ := by abel
    have hw : dotB p c (x - dotB p c x • v₀) = 0 := by
      rw [map_sub, map_smul, hv₀, smul_eq_mul, mul_one, sub_self]
    rw [hx, hadd, hsmul, hW _ hw, hf, hν0, zero_smul, add_zero]
  have horb : Nat.card (orbit E v₀) * p ≤ Nat.card P := by
    have hmem : ∀ y : orbit E v₀, ∀ l : ZMod p, (y : Fin 4 → ZMod p) - v₀ + l • c ∈ P := by
      rintro ⟨y, e, rfl⟩ l
      rw [hmemP]
      intro s hs
      have h1 := hβ e s v₀
      rw [(hmemC s).mp hs e] at h1
      have h2 := (hmemP c).mp hcP s hs
      simp only [map_add, map_sub, map_smul, smul_eq_mul, h2, mul_zero, add_zero]
      rw [h1, sub_self]
    let F : orbit E v₀ × ZMod p → P := fun yl => ⟨_, hmem yl.1 yl.2⟩
    have hF : Function.Injective F := by
      rintro ⟨⟨y, e, rfl⟩, l⟩ ⟨⟨y', e', rfl⟩, l'⟩ hyy
      have h1 : e • v₀ - v₀ + l • c = e' • v₀ - v₀ + l' • c := congrArg Subtype.val hyy
      have h2 : e • v₀ = e' • v₀ + (l' - l) • c := by
        have h3 : e • v₀ = e' • v₀ - v₀ + l' • c - l • c + v₀ := by rw [← h1]; abel
        rw [h3, sub_smul]
        abel
      have h3 : (e'⁻¹ * e) • v₀ = v₀ + (l' - l) • c := by
        rw [mul_smul, h2, hadd, hsmul, inv_smul_smul, (hmemC c).mp hcC e'⁻¹]
      have h4 := hinj _ _ h3 v₀
      have h5 : e • v₀ = e' • v₀ := by
        rw [mul_smul, inv_smul_eq_iff] at h4
        exact h4
      have h6 : l = l' := by
        rw [h5] at h1
        exact smul_left_injective (ZMod p) hc0 (add_left_cancel h1)
      exact Prod.ext (Subtype.ext h5) h6
    calc Nat.card (orbit E v₀) * p = Nat.card (orbit E v₀ × ZMod p) := by
          rw [Nat.card_prod, Nat.card_zmod]
      _ ≤ Nat.card P := Nat.card_le_card_of_injective F hF
  have hstab : Nat.card (stabilizer E v₀) =
      Nat.card {e : E // ∀ x : Fin 4 → ZMod p, e • x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    rw [mem_stabilizer_iff]
    exact ⟨fun he => hinj e 0 (by rw [zero_smul, add_zero]; exact he), fun he => he v₀⟩
  have hos : Nat.card (orbit E v₀) * Nat.card (stabilizer E v₀) = Nat.card E := by
    have := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    convert card_orbit_mul_card_stabilizer_eq_card_group E v₀
  have hfix : Nat.card (fixedPoints E (Fin 4 → ZMod p)) = Nat.card C :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hstabpos : 0 < Nat.card (stabilizer E v₀) := Nat.card_pos
  have h5 : Nat.card C * Nat.card (orbit E v₀) < p ^ 4 := by
    have h4 : Nat.card C * Nat.card (orbit E v₀) * p ≤ p ^ 3 * p := by
      calc Nat.card C * Nat.card (orbit E v₀) * p = Nat.card C * (Nat.card (orbit E v₀) * p) := by
            ring
        _ ≤ Nat.card C * Nat.card P := Nat.mul_le_mul_left _ horb
        _ = p ^ 3 * p := by rw [hcard]; ring
    have h6 := Nat.le_of_mul_le_mul_right h4 hpp.pos
    calc _ ≤ p ^ 3 := h6
      _ < p ^ 4 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  rw [hfix, ← hos, ← hstab, ← mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right h5 hstabpos

end Form

section Group

open Multiplicative

theorem noOffender_of_orthAct {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ι : Multiplicative (Fin 4 → ZMod p) →* G} (hinj : Function.Injective ι)
    {N Bs : Subgroup G} (hrange : ι.range = Bs)
    (horth : ∀ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      ∀ s s' : Fin 4 → ZMod p, g⁻¹ * ι (ofAdd s) * g = ι (ofAdd s') →
        ∑ i, s' i ^ 2 = ∑ i, s i ^ 2) :
    GGNoOffender p N Bs := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro E hEN hEB hE
  by_cases hcent : E ≤ Subgroup.centralizer (Bs : Set G)
  · exact Or.inl hcent
  right
  have hmem : ∀ (e : E) (s : Fin 4 → ZMod p), ∃ t : Fin 4 → ZMod p,
      ι (ofAdd t) = (e : G) * ι (ofAdd s) * (e : G)⁻¹ := by
    intro e s
    have h1 : ι (ofAdd s) ∈ Bs := hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (hEB e.2) _).mp h1
    rw [← hrange] at h2
    obtain ⟨t, ht⟩ := h2
    exact ⟨toAdd t, ht⟩
  choose φ hφ using hmem
  have hφinj : ∀ {t t' : Fin 4 → ZMod p}, ι (ofAdd t) = ι (ofAdd t') → t = t' := fun h =>
    ofAdd.injective (hinj h)
  let act : MulAction E (Fin 4 → ZMod p) :=
    { smul := φ
      one_smul := fun s => hφinj (by
        change ι (ofAdd (φ 1 s)) = ι (ofAdd s)
        rw [hφ]
        simp)
      mul_smul := fun e e' s => hφinj (by
        change ι (ofAdd (φ (e * e') s)) = ι (ofAdd (φ e (φ e' s)))
        rw [hφ, hφ, hφ, Subgroup.coe_mul]
        group) }
  have hsmul_def : ∀ (e : E) s, e • s = φ e s := fun e s => rfl
  have hEp : ∀ e : E, e ^ p = 1 := fun e => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE.2 e e.2)
  have hadd : ∀ (e : E) (s s' : Fin 4 → ZMod p), e • (s + s') = e • s + e • s' := by
    intro e s s'
    apply hφinj
    rw [hsmul_def, hsmul_def, hsmul_def, hφ, ofAdd_add, map_mul, ofAdd_add, map_mul, hφ, hφ]
    group
  have hQ : ∀ (e : E) (s : Fin 4 → ZMod p), dotB p (e • s) (e • s) = dotB p s s := by
    intro e s
    have h1 := horth (e : G)⁻¹ (N.inv_mem (hEN e.2))
      ((Subgroup.normalizer (Bs : Set G)).inv_mem (hEB e.2))
      (by rw [inv_pow, hE.2 e e.2, inv_one]) s (φ e s) (by rw [hφ, inv_inv])
    simp only [dotB_apply, dotProduct, ← sq]
    rw [hsmul_def]
    exact h1
  have hkerchar : ∀ e : E, (∀ s : Fin 4 → ZMod p, e • s = s) ↔
      (e : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    intro e
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro he b hb
      rw [← hrange] at hb
      obtain ⟨s, rfl⟩ := hb
      have h1 := hφ e (toAdd s)
      rw [show φ e (toAdd s) = toAdd s from he (toAdd s), ofAdd_toAdd] at h1
      calc ι s * e = e * ι s * (e : G)⁻¹ * e := by rw [← h1]
        _ = e * ι s := by group
    · intro he s
      apply hφinj
      change ι (ofAdd (φ e s)) = ι (ofAdd s)
      rw [hφ]
      have h2 := he (ι (ofAdd s)) (hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      calc (e : G) * ι (ofAdd s) * (e : G)⁻¹ = ι (ofAdd s) * e * (e : G)⁻¹ := by rw [h2]
        _ = ι (ofAdd s) := by group
  have hne : ∃ (e : E) (s : Fin 4 → ZMod p), e • s ≠ s := by
    by_contra hcon
    push Not at hcon
    apply hcent
    intro e he
    exact (hkerchar ⟨e, he⟩).mp (hcon ⟨e, he⟩)
  have hcount := card_fixedPoints_mul_card_lt hp2 hEp hadd hQ hne
  have hcentι : ∀ s : Fin 4 → ZMod p, s ∈ fixedPoints E (Fin 4 → ZMod p) →
      ι (ofAdd s) ∈ Bs ⊓ Subgroup.centralizer (E : Set G) := by
    intro s hs
    refine Subgroup.mem_inf.mpr ⟨hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 : ι (ofAdd s) = e * ι (ofAdd s) * e⁻¹ := by
      have h2 := hφ ⟨e, he⟩ s
      rwa [show φ ⟨e, he⟩ s = s from hs ⟨e, he⟩] at h2
    calc e * ι (ofAdd s) = e * ι (ofAdd s) * e⁻¹ * e := by group
      _ = ι (ofAdd s) * e := by rw [← h1]
  have hfixι : ∀ b ∈ Bs ⊓ Subgroup.centralizer (E : Set G),
      ∃ s ∈ fixedPoints E (Fin 4 → ZMod p), ι (ofAdd s) = b := by
    intro b hb
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
    rw [← hrange] at hbB
    obtain ⟨s, rfl⟩ := hbB
    refine ⟨toAdd s, fun e => hφinj ?_, rfl⟩
    change ι (ofAdd (φ e (toAdd s))) = ι (ofAdd (toAdd s))
    rw [hφ, ofAdd_toAdd]
    have h2 := (Subgroup.mem_centralizer_iff.mp hbC) e e.2
    calc (e : G) * ι s * (e : G)⁻¹ = ι s * e * (e : G)⁻¹ := by rw [h2]
      _ = ι s := by group
  have hfix : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) =
      Nat.card (fixedPoints E (Fin 4 → ZMod p)) := by
    symm
    refine Nat.card_eq_of_bijective (fun s => ⟨ι (ofAdd s.1), hcentι s.1 s.2⟩) ⟨?_, ?_⟩
    · intro s t hst
      exact Subtype.ext (hφinj (congrArg Subtype.val hst))
    · intro b
      obtain ⟨s, hs, hsb⟩ := hfixι b.1 b.2
      exact ⟨⟨s, hs⟩, Subtype.ext hsb⟩
  have hker : Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) =
      Nat.card {e : E // ∀ s : Fin 4 → ZMod p, e • s = s} := by
    refine Nat.card_eq_of_bijective (fun e => ⟨⟨e.1, (Subgroup.mem_inf.mp e.2).1⟩,
      (hkerchar _).mpr (Subgroup.mem_inf.mp e.2).2⟩) ⟨?_, ?_⟩
    · intro e e' hee'
      exact Subtype.ext (congrArg (fun z : {e : E // ∀ s : Fin 4 → ZMod p, e • s = s} =>
        ((z.1 : E) : G)) hee')
    · intro e
      exact ⟨⟨e.1.1, Subgroup.mem_inf.mpr ⟨e.1.2, (hkerchar e.1).mp e.2⟩⟩, rfl⟩
  have hBs : Nat.card Bs = p ^ 4 := by
    have : NeZero p := ⟨hp.ne_zero⟩
    rw [← hrange]
    exact NoOffUO.card_range_eq hinj
  rw [hfix, hker, hBs]
  exact hcount

end Group

end NoOffOm

section Inputs

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Multiplicative

@[expose] def GGSixBstarOrthFrameOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    ∃ ι : Multiplicative (Fin 4 → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
        ∀ s s' : Fin 4 → ZMod p, g⁻¹ * ι (ofAdd s) * g = ι (ofAdd s') →
          ∑ i, s' i ^ 2 = ∑ i, s i ^ 2

theorem ggNoOffender_of_orthFrameOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarOrthFrameOn P) : GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨ι, hinj, hrange, horth⟩ := h G p B Bs x L D J t n f ψ hP hctx hC
  exact NoOffOm.noOffender_of_orthAct hctx.1.2.2.2.2.2.1.1 hctx.1.2.2.2.2.2.1.2.1 hinj hrange
    horth

theorem ggSixBstarNoOffenderAt_POmegaPlus_of_orthFrame
    (hM : GGSixBstarMonoFrameOn GGPOmegaPlusNotD4Three)
    (hD4 : GGSixBstarOrthFrameOn GGPOmegaPlusD4Three) : GGSixBstarNoOffenderAt .POmegaPlus :=
  ggSixBstarNoOffenderAt_POmegaPlus_of_frame hM (ggNoOffender_of_orthFrameOn hD4)

end Inputs

end CFSG.StandardType
