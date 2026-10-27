module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseBGlue2
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseAG

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseBGlue3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs CFSG.Quasithin.H13.L827X.LBCaseAGBase
  CFSG.Quasithin.H13.L827X.LBCaseBGlue2 CFSG.Quasithin.H13.L827X.LBCaseAG
open scoped commutatorElement

variable {G : Type} [Group G]

theorem tau_eq_one_of_mem_XiY_glue3 {Λ O W₀ W₁ X : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : ChiefRepProps Λ O W₀ W₁ τ π) (hΛW1 : Λ ≤ Subgroup.normalizer (W₁ : Set G))
    (hW0W1 : W₀ ≤ W₁) (hB : ⁅W₁, XiY X⁆ ≤ W₀) {y : Λ} (hy : (y : G) ∈ XiY X) :
    τ y = 1 := by
  obtain ⟨-, hsurj, hadd, hzero, hequiv, -, -⟩ := hR
  apply LinearEquiv.ext
  intro m
  obtain ⟨w, rfl⟩ := hsurj m
  have hw1 : (y : G) * (w : G) * (y : G)⁻¹ ∈ W₁ :=
    (Subgroup.mem_normalizer_iff.mp (hΛW1 y.2) (w : G)).mp w.2
  have hc : ⁅(w : G), (y : G)⁆ ∈ W₀ := hB (Subgroup.commutator_mem_commutator w.2 hy)
  have hc' : (⁅(w : G), (y : G)⁆)⁻¹ ∈ W₀ := W₀.inv_mem hc
  have hcW1 : (⁅(w : G), (y : G)⁆)⁻¹ ∈ W₁ := hW0W1 hc'
  have hpc : π ⟨(⁅(w : G), (y : G)⁆)⁻¹, hcW1⟩ = 0 := (hzero _).mpr hc'
  have hprod : (⟨(y : G) * (w : G) * (y : G)⁻¹, hw1⟩ : W₁) =
      ⟨(⁅(w : G), (y : G)⁆)⁻¹, hcW1⟩ * w := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_def]
    group
  have h1 : τ y (π w) = π ⟨(y : G) * (w : G) * (y : G)⁻¹, hw1⟩ :=
    hequiv y w ⟨(y : G) * (w : G) * (y : G)⁻¹, hw1⟩ rfl
  rw [LinearEquiv.coe_one, id_eq, h1, hprod, hadd, hpc, zero_add]

theorem q_one_glue3 {X : Subgroup G} {E : Type} [AddCommGroup E] {q : X → E}
    (hq_add : ∀ x y : X, q (x * y) = q x + q y) : q 1 = 0 := by
  have h := hq_add 1 1
  rw [mul_one] at h
  simpa using h

section Rep

variable {X Λ : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Λ →* (W ≃ₗ[ZMod 2] W)} {E : Type} [AddCommGroup E] {q : X → E}

theorem tau_eq_of_q_eq_glue3 (hXΛ : X ≤ Λ)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hτY : ∀ y : Λ, (y : G) ∈ XiY X → τ y = 1) (x x' : X) (h : q x' = q x) :
    (τ ⟨(x' : G), hXΛ x'.2⟩ : W ≃ₗ[ZMod 2] W) = τ ⟨(x : G), hXΛ x.2⟩ := by
  have hmem : (x' : G)⁻¹ * (x : G) ∈ XiY X := (hker x' x).mp h
  have hz : (x' : G)⁻¹ * (x : G) ∈ Λ := hXΛ (X.mul_mem (X.inv_mem x'.2) x.2)
  have hτz : τ ⟨(x' : G)⁻¹ * (x : G), hz⟩ = 1 := hτY ⟨(x' : G)⁻¹ * (x : G), hz⟩ hmem
  have hsplit : (⟨(x : G), hXΛ x.2⟩ : Λ) =
      ⟨(x' : G), hXΛ x'.2⟩ * ⟨(x' : G)⁻¹ * (x : G), hz⟩ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul]
      group)
  rw [hsplit, map_mul, hτz, mul_one]

@[expose] noncomputable def rhoGlue3 (τ : Λ →* (W ≃ₗ[ZMod 2] W)) (hXΛ : X ≤ Λ)
    (hq : Function.Surjective q) (e : E) : Module.End (ZMod 2) W :=
  (τ ⟨((liftGlue2 hq e : X) : G), hXΛ (liftGlue2 hq e).2⟩ : W ≃ₗ[ZMod 2] W).toLinearMap

theorem rhoGlue3_q (hXΛ : X ≤ Λ) (hq : Function.Surjective q)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hτY : ∀ y : Λ, (y : G) ∈ XiY X → τ y = 1) (x : X) :
    rhoGlue3 τ hXΛ hq (q x) = (τ ⟨(x : G), hXΛ x.2⟩ : W ≃ₗ[ZMod 2] W).toLinearMap := by
  unfold rhoGlue3
  rw [tau_eq_of_q_eq_glue3 hXΛ hker hτY x (liftGlue2 hq (q x)) (q_liftGlue2 hq (q x))]

theorem rhoGlue3_zero (hXΛ : X ≤ Λ) (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hτY : ∀ y : Λ, (y : G) ∈ XiY X → τ y = 1) : rhoGlue3 τ hXΛ hq 0 = 1 := by
  rw [← q_one_glue3 hq_add, rhoGlue3_q hXΛ hq hker hτY 1]
  have h1 : (⟨((1 : X) : G), hXΛ (1 : X).2⟩ : Λ) = 1 := Subtype.ext rfl
  rw [h1, map_one]
  rfl

theorem rhoGlue3_add (hXΛ : X ≤ Λ) (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hτY : ∀ y : Λ, (y : G) ∈ XiY X → τ y = 1) (e₁ e₂ : E) :
    rhoGlue3 τ hXΛ hq (e₁ + e₂) = rhoGlue3 τ hXΛ hq e₁ * rhoGlue3 τ hXΛ hq e₂ := by
  obtain ⟨a, rfl⟩ := hq e₁
  obtain ⟨b, rfl⟩ := hq e₂
  rw [← hq_add, rhoGlue3_q hXΛ hq hker hτY, rhoGlue3_q hXΛ hq hker hτY,
    rhoGlue3_q hXΛ hq hker hτY]
  have e : (⟨((a * b : X) : G), hXΛ (a * b).2⟩ : Λ) =
      ⟨(a : G), hXΛ a.2⟩ * ⟨(b : G), hXΛ b.2⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul])
  rw [e, rep_mul_caseAG τ]

theorem rhoGlue3_conj (hXΛ : X ≤ Λ) (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hτY : ∀ y : Λ, (y : G) ∈ XiY X → τ y = 1)
    {γ : G} (hγΛ : γ ∈ Λ) (hγN : γ ∈ Subgroup.normalizer (X : Set G))
    (s : E → E) (hs : ∀ x : X, s (q x) = q (conjXEquiv X hγN x)) (e : E) :
    (τ ⟨γ, hγΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap * rhoGlue3 τ hXΛ hq e =
      rhoGlue3 τ hXΛ hq (s e) * (τ ⟨γ, hγΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap := by
  obtain ⟨x, rfl⟩ := hq e
  rw [hs x, rhoGlue3_q hXΛ hq hker hτY, rhoGlue3_q hXΛ hq hker hτY]
  rw [← rep_mul_caseAG τ, ← rep_mul_caseAG τ]
  have e : (⟨γ, hγΛ⟩ * ⟨(x : G), hXΛ x.2⟩ : Λ) =
      ⟨((conjXEquiv X hγN x : X) : G), hXΛ (conjXEquiv X hγN x).2⟩ * ⟨γ, hγΛ⟩ := by
    apply Subtype.ext
    show γ * (x : G) = ((conjXEquiv X hγN x : X) : G) * γ
    rw [conjXEquiv_coe]
    group
  rw [e]

theorem fixed_zero_glue3 {Λ' O W₀ W₁ X X₁ : Subgroup G} {W' : Type} [AddCommGroup W']
    [Module (ZMod 2) W'] {τ' : Λ' →* (W' ≃ₗ[ZMod 2] W')} {π' : W₁ → W'}
    (hR : ChiefRepProps Λ' O W₀ W₁ τ' π') (hXΛ : X ≤ Λ')
    (hΛN : Λ' ≤ Subgroup.normalizer (X : Set G)) (hΛW1 : Λ' ≤ Subgroup.normalizer (W₁ : Set G))
    (hX1X : X₁ ≤ X) (hWX : ¬ ⁅W₁, X₁⁆ ≤ W₀) :
    ∀ w : W', (∀ x : X, (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') w = w) → w = 0 := by
  classical
  have hirr := hR.2.2.2.2.2.2
  let S : Submodule (ZMod 2) W' :=
    { carrier := {w | ∀ x : X, (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') w = w}
      add_mem' := fun {a b} ha hb x => by
        show (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') (a + b) = a + b
        rw [map_add, ha x, hb x]
      zero_mem' := fun x => map_zero _
      smul_mem' := fun c a ha x => by
        show (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') (c • a) = c • a
        rw [LinearEquiv.map_smul, ha x] }
  have hSmem : ∀ w, w ∈ S ↔ ∀ x : X, (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') w = w :=
    fun w => Iff.rfl
  have hSinv : ∀ l : Λ', ∀ w ∈ S, τ' l w ∈ S := by
    intro l w hw
    rw [hSmem] at hw ⊢
    intro x
    have hl' : ((l⁻¹ : Λ') : G) ∈ Subgroup.normalizer (X : Set G) :=
      hΛN (Subgroup.inv_mem _ l.2)
    have hx' : (l : G)⁻¹ * (x : G) * (l : G) ∈ X := by
      have h := (Subgroup.mem_normalizer_iff.mp hl' (x : G)).mp x.2
      rwa [Subgroup.coe_inv, inv_inv] at h
    have e : (⟨(x : G), hXΛ x.2⟩ : Λ') * l = l * ⟨(l : G)⁻¹ * (x : G) * (l : G), hXΛ hx'⟩ :=
      Subtype.ext (by
        show (x : G) * (l : G) = (l : G) * ((l : G)⁻¹ * (x : G) * (l : G))
        group)
    have hwx := hw ⟨(l : G)⁻¹ * (x : G) * (l : G), hx'⟩
    calc (τ' ⟨(x : G), hXΛ x.2⟩ : W' ≃ₗ[ZMod 2] W') (τ' l w)
        = (τ' (⟨(x : G), hXΛ x.2⟩ * l) : W' ≃ₗ[ZMod 2] W') w := by
          rw [map_mul, LinearEquiv.mul_apply]
      _ = (τ' (l * ⟨(l : G)⁻¹ * (x : G) * (l : G), hXΛ hx'⟩) : W' ≃ₗ[ZMod 2] W') w := by
          rw [e]
      _ = τ' l ((τ' ⟨(l : G)⁻¹ * (x : G) * (l : G), hXΛ hx'⟩ : W' ≃ₗ[ZMod 2] W') w) := by
          rw [map_mul, LinearEquiv.mul_apply]
      _ = τ' l w := by rw [hwx]
  have hSne : S ≠ ⊤ := by
    have hex : ¬ (∀ w₁ ∈ W₁, ∀ x₁ ∈ X₁, ⁅w₁, x₁⁆ ∈ W₀) :=
      fun hh => hWX (Subgroup.commutator_le.mpr hh)
    push Not at hex
    obtain ⟨w₁, hw₁, x₁, hx₁, hnot⟩ := hex
    intro htop
    have hmem : π' ⟨w₁, hw₁⟩ ∈ S := by
      rw [htop]
      exact Submodule.mem_top
    have h1 := (hSmem _).mp hmem ⟨x₁, hX1X hx₁⟩
    exact moves_of_comm_not_mem_caseAG hR hΛW1 (hXΛ (hX1X hx₁)) hw₁ hnot h1
  have hSbot : S = ⊥ := (hirr S hSinv).resolve_right hSne
  intro w hw
  have hwS : w ∈ S := (hSmem w).mpr hw
  rw [hSbot] at hwS
  exact (Submodule.mem_bot _).mp hwS

end Rep

theorem conj_mul_inv_mem_glue3 {X : Subgroup G} {v : G} (hvN : v ∈ Subgroup.normalizer (X : Set G))
    {E : Type} [AddCommGroup E] {q : X → E}
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    (hfix : ∀ x : X, q (conjXEquiv X hvN x) = q x) (x : X) :
    conjXEquiv X hvN x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X) := by
  rw [mem_Yof_iff, Subgroup.coe_mul, Subgroup.coe_inv]
  have h1 : (x : G)⁻¹ * ((conjXEquiv X hvN x : X) : G) ∈ XiY X :=
    (hker x (conjXEquiv X hvN x)).mp (hfix x).symm
  have h2 := conj_mem_XiY (Subgroup.le_normalizer x.2) h1
  have e : (x : G) * ((x : G)⁻¹ * ((conjXEquiv X hvN x : X) : G)) * (x : G)⁻¹ =
      ((conjXEquiv X hvN x : X) : G) * (x : G)⁻¹ := by
    group
  rw [e] at h2
  exact h2

theorem comm_zpowers_le_glue3 {X X₁ : Subgroup G} [Finite G] {v : G} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hvN : v ∈ Subgroup.normalizer (X : Set G)) (hvv : v * v = 1)
    (hX1X : X₁ ≤ X) (hS : IsXiShape p ((pCoreOf 2 X).subgroupOf X))
    (hcon : ∀ x : ↥X, conjXEquiv X hvN x * x⁻¹ ∈ Yof ((pCoreOf 2 X).subgroupOf X)) :
    ⁅X₁, Subgroup.zpowers v⁆ ≤ pCoreOf 2 X := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hα2 : (conjXEquiv X hvN) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [sq, MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    show v * (v * (x : G) * v⁻¹) * v⁻¹ = x
    rw [hvinv]
    calc v * (v * (x : G) * v) * v = (v * v) * (x : G) * (v * v) := by group
      _ = x := by rw [hvv, one_mul, mul_one]
  have hzpow : ∀ k : ℤ, v ^ k = 1 ∨ v ^ k = v := by
    intro k
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul]
      simp [pow_two, hvv]
    · right
      rw [zpow_add_one, zpow_mul]
      simp [pow_two, hvv]
  rw [Subgroup.commutator_le]
  intro x hx g hg
  have hxX : x ∈ X := hX1X hx
  have hfix : ∀ x' : ↥X, conjXEquiv X hvN x' * x'⁻¹ ∈ (pCoreOf 2 X).subgroupOf X :=
    fun x' => invol_fix_mod hS hp2 hα2 (fun x'' => LBCaseAGK.N_conj_iff X hvN x'') hcon x'
  have hxv : ⁅x, v⁆ ∈ pCoreOf 2 X := by
    have h1 := hfix ⟨x, hxX⟩
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((conjXEquiv X hvN ⟨x, hxX⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ : ↥X) : G) =
        v * x * v⁻¹ * x⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjXEquiv_coe]
    rw [h2] at h1
    rw [← commutatorElement_inv]
    exact (pCoreOf 2 X).inv_mem h1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases hzpow k with h1 | h1
  · rw [h1, commutatorElement_one_right]
    exact (pCoreOf 2 X).one_mem
  · rw [h1]
    exact hxv

theorem conjLEGlue2_sq_glue3 {X : Subgroup G} {E : Type} [AddCommGroup E] {q : X → E} (p : ℕ)
    [Module (ZMod p) E] (hq : Function.Surjective q)
    (hq_add : ∀ x y : X, q (x * y) = q x + q y)
    (hker : ∀ x y : X, q x = q y ↔ (x : G)⁻¹ * (y : G) ∈ XiY X)
    {v : G} (hvN : v ∈ Subgroup.normalizer (X : Set G)) (hvv : v * v = 1) (e : E) :
    conjLEGlue2 p hq hq_add hker hvN (conjLEGlue2 p hq hq_add hker hvN e) = e := by
  have h := conjLEGlue2_mul p hq hq_add hker hvN hvN (Subgroup.mul_mem _ hvN hvN)
  rw [conjLEGlue2_one p hq hq_add hker (Subgroup.mul_mem _ hvN hvN) hvv] at h
  have h2 : (conjLEGlue2 p hq hq_add hker hvN * conjLEGlue2 p hq hq_add hker hvN) e = e := by
    rw [← h]
    simp only [LinearEquiv.coe_one, id_eq]
  rw [LinearEquiv.mul_apply] at h2
  exact h2

end CFSG.Quasithin.H13.L827X.LBCaseBGlue3

end
