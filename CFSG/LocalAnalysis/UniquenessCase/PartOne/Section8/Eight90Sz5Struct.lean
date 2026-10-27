module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs
import CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Weights
import CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Basic
import CFSG.GroupTheory.SteinbergCBFTCritical
import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem sz5e1_perm_trivial {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {Ω : Type} [Finite Ω] (hΩ : Nat.card Ω ≤ 12) (φ : D →* Equiv.Perm Ω) :
    φ = 1 := by
  by_contra hφ
  have hd : ∃ d : D, φ d ≠ 1 := by
    by_contra h
    apply hφ
    apply MonoidHom.ext
    intro d
    by_contra hne
    exact h ⟨d, hne⟩
  have hker : φ.ker ≤ P := ker_le_of_nontrivial P hD φ hd
  have h13P : 13 ∣ P.index := by
    rw [Subgroup.index_eq_card]
    exact sz5e1_sz8_thirteen_dvd hD.2.2
  have h13ker : 13 ∣ φ.ker.index := h13P.trans (Subgroup.index_dvd_of_le hker)
  have hcardker : φ.ker.index = Nat.card (D ⧸ φ.ker) := Subgroup.index_eq_card φ.ker
  have hcardrange : Nat.card (D ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hdiv : Nat.card φ.range ∣ Nat.card (Equiv.Perm Ω) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have h13fact : 13 ∣ Nat.factorial (Nat.card Ω) := by
    have h13r : 13 ∣ Nat.card φ.range := by
      rw [← hcardrange, ← hcardker]
      exact h13ker
    rw [← Nat.card_perm]
    exact h13r.trans hdiv
  have hle : 13 ≤ Nat.card Ω :=
    (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 13)).mp h13fact
  omega

private noncomputable def sz5e1_nsc_conj {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D) : E.map ρ ≃* E.map ρ where
  toFun x :=
    ⟨ρ d * (x : V ≃ₗ[F] V) * (ρ d)⁻¹, by
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp x.2
      exact ⟨d * e * d⁻¹, hE.conj_mem e he d, by
        rw [← heq]
        simp only [map_mul, map_inv]⟩⟩
  invFun x :=
    ⟨(ρ d)⁻¹ * (x : V ≃ₗ[F] V) * ρ d, by
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp x.2
      exact ⟨d⁻¹ * e * d, by simpa using hE.conj_mem e he d⁻¹, by
        rw [← heq]
        simp only [map_mul, map_inv]⟩⟩
  left_inv x := by
    apply Subtype.ext
    group
  right_inv x := by
    apply Subtype.ext
    group
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[simp] private lemma sz5e1_nsc_conj_apply {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D) (x : E.map ρ) :
    ((sz5e1_nsc_conj ρ E hE d x : E.map ρ) : V ≃ₗ[F] V) =
      ρ d * (x : V ≃ₗ[F] V) * (ρ d)⁻¹ := rfl

@[simp] private lemma sz5e1_nsc_conj_symm_apply {D : Type*} [Group D] {F : Type} [Field F]
    {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D) (x : E.map ρ) :
    (((sz5e1_nsc_conj ρ E hE d).symm x : E.map ρ) : V ≃ₗ[F] V) =
      (ρ d)⁻¹ * (x : V ≃ₗ[F] V) * ρ d := rfl

private lemma sz5e1_nsc_conj_mul {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d₁ d₂ : D) :
    sz5e1_nsc_conj ρ E hE (d₁ * d₂) =
      sz5e1_nsc_conj ρ E hE d₁ * sz5e1_nsc_conj ρ E hE d₂ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [sz5e1_nsc_conj_apply, MulAut.mul_apply, sz5e1_nsc_conj_apply, sz5e1_nsc_conj_apply]
  simp only [map_mul]
  group

private lemma sz5e1_nsc_conj_inv {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D) :
    sz5e1_nsc_conj ρ E hE d⁻¹ = (sz5e1_nsc_conj ρ E hE d).symm := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [sz5e1_nsc_conj_apply, sz5e1_nsc_conj_symm_apply]
  simp only [map_inv, inv_inv]

private noncomputable def sz5e1_nsc_charPerm {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V]
    (E' : Subgroup (V ≃ₗ[F] V)) (c : E' ≃* E') :
    Equiv.Perm (↥E' →* Fˣ) where
  toFun χ := χ.comp (c.symm : ↥E' →* ↥E')
  invFun χ := χ.comp (c : ↥E' →* ↥E')
  left_inv χ := by
    ext x
    simp
  right_inv χ := by
    ext x
    simp

@[simp] private lemma sz5e1_nsc_charPerm_apply {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V]
    (E' : Subgroup (V ≃ₗ[F] V)) (c : E' ≃* E')
    (χ : ↥E' →* Fˣ) (x : ↥E') :
    sz5e1_nsc_charPerm E' c χ x = χ (c.symm x) := rfl

@[simp] private lemma sz5e1_nsc_charPerm_symm {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V]
    (E' : Subgroup (V ≃ₗ[F] V)) (c : E' ≃* E') :
    (sz5e1_nsc_charPerm E' c).symm = sz5e1_nsc_charPerm E' c.symm := rfl

private lemma sz5e1_nsc_charPerm_mul {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (E' : Subgroup (V ≃ₗ[F] V)) (c₁ c₂ : E' ≃* E') :
    sz5e1_nsc_charPerm E' (c₁ * c₂) =
      sz5e1_nsc_charPerm E' c₁ * sz5e1_nsc_charPerm E' c₂ := by
  ext χ x
  simp only [sz5e1_nsc_charPerm_apply, Equiv.Perm.mul_apply]
  congr 1

private noncomputable def sz5e1_nsc_permHom {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) :
    D →* Equiv.Perm (↥(E.map ρ) →* Fˣ) :=
  MonoidHom.mk'
    (fun d => sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d))
    (by
      intro d₁ d₂
      rw [sz5e1_nsc_conj_mul, sz5e1_nsc_charPerm_mul])

private lemma sz5e1_nsc_wt_smul {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D)
    (χ : ↥(E.map ρ) →* Fˣ) {v : V} (hv : v ∈ wt (E.map ρ) χ) :
    ρ d v ∈ wt (E.map ρ)
      (sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) := by
  rw [mem_wt] at hv ⊢
  intro e
  have hmul : (e : V ≃ₗ[F] V) * ρ d =
      ρ d * ((sz5e1_nsc_conj ρ E hE d).symm e : V ≃ₗ[F] V) := by
    rw [sz5e1_nsc_conj_symm_apply]
    group
  calc (e : V ≃ₗ[F] V) (ρ d v)
      = ((e : V ≃ₗ[F] V) * ρ d) v := rfl
    _ = (ρ d * ((sz5e1_nsc_conj ρ E hE d).symm e : V ≃ₗ[F] V)) v := by rw [hmul]
    _ = ρ d (((sz5e1_nsc_conj ρ E hE d).symm e : V ≃ₗ[F] V) v) := rfl
    _ = ρ d ((χ ((sz5e1_nsc_conj ρ E hE d).symm e) : F) • v) := by
          rw [hv ((sz5e1_nsc_conj ρ E hE d).symm e)]
    _ = (χ ((sz5e1_nsc_conj ρ E hE d).symm e) : F) • ρ d v := by rw [map_smul]
    _ = ((sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) e : F) •
          ρ d v := rfl

private lemma sz5e1_nsc_wt_charPerm_eq {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D)
    (χ : ↥(E.map ρ) →* Fˣ) :
    wt (E.map ρ) (sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) =
      (wt (E.map ρ) χ).map (ρ d : V →ₗ[F] V) := by
  apply le_antisymm
  · intro x hx
    refine ⟨ρ d⁻¹ x, ?_, ?_⟩
    · have h := sz5e1_nsc_wt_smul ρ E hE d⁻¹
        (sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) hx
      have hcomp : sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d⁻¹)
          (sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) = χ := by
        rw [sz5e1_nsc_conj_inv, ← sz5e1_nsc_charPerm_symm]
        exact Equiv.symm_apply_apply _ χ
      rwa [hcomp] at h
    · simp [map_inv]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact sz5e1_nsc_wt_smul ρ E hE d χ hv

private lemma sz5e1_nsc_wt_ne_bot_iff {D : Type*} [Group D] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] (ρ : D →* (V ≃ₗ[F] V))
    (E : Subgroup D) (hE : E.Normal) (d : D)
    (χ : ↥(E.map ρ) →* Fˣ) :
    wt (E.map ρ) (sz5e1_nsc_permHom ρ E hE d χ) ≠ ⊥ ↔ wt (E.map ρ) χ ≠ ⊥ := by
  change wt (E.map ρ)
      (sz5e1_nsc_charPerm (E.map ρ) (sz5e1_nsc_conj ρ E hE d) χ) ≠ ⊥ ↔
    wt (E.map ρ) χ ≠ ⊥
  rw [sz5e1_nsc_wt_charPerm_eq, Submodule.map_ne_bot_iff]

theorem sz5e1_normal_elem_scalar {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P) {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (hF : ringChar F ≠ 2) (ρ : D →* (V ≃ₗ[F] V))
    (hirr : IsIrreducibleRep ρ) (hdim : Module.finrank F V ≤ 12) (E : Subgroup D)
    [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    ∀ e ∈ E, ρ e = 1 ∨ ρ e = negOne F V := by
  have hEn : E.Normal := inferInstance
  have hE'c : ∀ a ∈ E.map ρ, ∀ b ∈ E.map ρ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ea, hea, heqa⟩ := Subgroup.mem_map.mp ha
    obtain ⟨eb, heb, heqb⟩ := Subgroup.mem_map.mp hb
    rw [← heqa, ← heqb, ← map_mul, ← map_mul, hEc ea hea eb heb]
  have hE'2 : ∀ a ∈ E.map ρ, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨ea, hea, heqa⟩ := Subgroup.mem_map.mp ha
    rw [← heqa, ← map_pow, hE2 ea hea, map_one]
  obtain ⟨hind, htop⟩ := sz5e1_weight_decomp hF (E.map ρ) hE'c hE'2
  let Ω := {χ : ↥(E.map ρ) →* Fˣ // wt (E.map ρ) χ ≠ ⊥}
  have : Fintype Ω := hind.fintypeNeBotOfFiniteDimensional
  have hΩ12 : Nat.card Ω ≤ 12 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card Ω ≤ Module.finrank F V := hind.subtype_ne_bot_le_finrank
      _ ≤ 12 := hdim
  let φ : D →* Equiv.Perm Ω :=
    MonoidHom.mk'
      (fun d => (sz5e1_nsc_permHom ρ E hEn d).subtypePerm
        (fun χ => sz5e1_nsc_wt_ne_bot_iff ρ E hEn d χ))
      (by
        intro d₁ d₂
        apply Equiv.ext
        intro χ
        apply Subtype.ext
        simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.mul_apply, map_mul])
  have hφ1 : φ = 1 := sz5e1_perm_trivial P hD hΩ12 φ
  have hfix : ∀ (d : D) (χ : Ω), φ d χ = χ := by
    intro d χ
    rw [hφ1]
    rfl
  by_cases hbot : (⊤ : Submodule F V) = ⊥
  · intro e he
    left
    ext v
    have hv : v ∈ (⊥ : Submodule F V) := hbot ▸ Submodule.mem_top
    have hv0 : v = 0 := by simpa using hv
    rw [hv0]
    simp
  · have hex : ∃ χ : ↥(E.map ρ) →* Fˣ, wt (E.map ρ) χ ≠ ⊥ := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      have hb : (⨆ χ, wt (E.map ρ) χ) = ⊥ := iSup_eq_bot.mpr h
      rw [htop] at hb
      exact hbot hb
    obtain ⟨χ₀, hχ₀⟩ := hex
    have hwt_top : wt (E.map ρ) χ₀ = ⊤ := by
      rcases hirr (wt (E.map ρ) χ₀) (fun k w hw => by
        have hle : ρ k w ∈ wt (E.map ρ) (sz5e1_nsc_permHom ρ E hEn k χ₀) :=
          sz5e1_nsc_wt_smul ρ E hEn k χ₀ hw
        have hfixk : sz5e1_nsc_permHom ρ E hEn k χ₀ = χ₀ := by
          have h : ((sz5e1_nsc_permHom ρ E hEn k).subtypePerm
              (fun χ => sz5e1_nsc_wt_ne_bot_iff ρ E hEn k χ) ⟨χ₀, hχ₀⟩) = ⟨χ₀, hχ₀⟩ :=
            hfix k ⟨χ₀, hχ₀⟩
          have h2 := congrArg Subtype.val h
          simpa [Equiv.Perm.subtypePerm_apply] using h2
        rwa [hfixk] at hle) with h | h
      · exact absurd h hχ₀
      · exact h
    intro e he
    let e' : ↥(E.map ρ) := ⟨ρ e, Subgroup.mem_map.mpr ⟨e, he, rfl⟩⟩
    have he'2 : e' * e' = 1 := by
      apply Subtype.ext
      show ρ e * ρ e = 1
      rw [← map_mul, ← pow_two, hE2 e he, map_one]
    have hunit : χ₀ e' * χ₀ e' = 1 := by
      rw [← map_mul, he'2, map_one]
    have hc : (((χ₀ e' : Fˣ) : F)) * (((χ₀ e' : Fˣ) : F)) = 1 := by
      have h := congrArg (fun u : Fˣ => (u : F)) hunit
      simpa using h
    have hval : ∀ v : V, ρ e v = (((χ₀ e' : Fˣ) : F)) • v := by
      intro v
      have hv : v ∈ wt (E.map ρ) χ₀ := by rw [hwt_top]; trivial
      exact (mem_wt (E.map ρ) χ₀ v).mp hv e'
    rcases mul_self_eq_one_iff.mp hc with hc1 | hcneg
    · left
      ext v
      rw [hval v, hc1]
      simp
    · right
      ext v
      rw [hval v, hcneg]
      simp [negOne_apply]

theorem sz5e1_heisenberg {Q : Type} {F : Type} [Field F] {V : Type} [Group Q] [Finite Q]
    [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V] (ρ : Q →* (V ≃ₗ[F] V))
    (hρ : Function.Injective ρ) (hc : ∀ x y : Q, ρ ⁅x, y⁆ = 1 ∨ ρ ⁅x, y⁆ = negOne F V) :
    (Subgroup.center Q).index ≤ (Module.finrank F V) ^ 2 := by
  classical
  let ρu : Q →* (Module.End F V)ˣ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm.toMonoidHom.comp ρ
  have hcoe : ∀ q : Q, (ρu q : Module.End F V) = (ρ q : V →ₗ[F] V) := by
    intro q
    change (LinearMap.GeneralLinearGroup.ofLinearEquiv (ρ q) : Module.End F V) =
      (ρ q : V →ₗ[F] V)
    rfl
  have hρu_ne : ∀ q : Q, (ρu q : Module.End F V) ≠ 0 := by
    intro q h
    have h1 : (1 : Module.End F V) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      intro hh
      apply hv
      simpa using congrArg (fun f : Module.End F V => f v) hh
    have hu : ((ρu q : (Module.End F V)ˣ) : Module.End F V) *
        (((ρu q)⁻¹ : (Module.End F V)ˣ) : Module.End F V) = 1 := by simp
    rw [h, zero_mul] at hu
    exact h1 hu.symm
  have hcancel : ∀ q : Q,
      Function.Injective (fun a : F => a • (ρu q : Module.End F V)) := by
    intro q
    exact smul_left_injective F (hρu_ne q)
  let AdFun : Q → (Module.End F V →ₗ[F] Module.End F V) := fun w =>
    (LinearMap.mulLeft F (ρu w : Module.End F V)).comp
      (LinearMap.mulRight F
        (((ρu w)⁻¹ : (Module.End F V)ˣ) : Module.End F V))
  have hAdFun_mul : ∀ w w' : Q, AdFun (w * w') = (AdFun w).comp (AdFun w') := by
    intro w w'
    ext X
    simp only [AdFun, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    simp [map_mul, mul_assoc]
  let Ad : Q →* (Module.End F V →ₗ[F] Module.End F V) :=
    { toFun := AdFun
      map_one' := by
        change AdFun 1 = 1
        ext X
        simp [AdFun]
      map_mul' := hAdFun_mul }
  have hAd_apply : ∀ (w : Q) (X : Module.End F V),
      Ad w X = (ρu w : Module.End F V) * X *
        (((ρu w)⁻¹ : (Module.End F V)ˣ) : Module.End F V) := by
    intro w X
    change AdFun w X = _
    simp [AdFun, mul_assoc]
  have hAd_mulEnd : ∀ (w : Q) (X Y : Module.End F V),
      Ad w (X * Y) = Ad w X * Ad w Y := by
    intro w X Y
    rw [hAd_apply, hAd_apply, hAd_apply]
    simp [mul_assoc]
  have hnegOne : ((negOne F V : Module.End F V)) =
      (-1 : F) • (1 : Module.End F V) := by
    rw [show ((negOne F V : V →ₗ[F] V) :
      Module.End F V) = -LinearMap.id from rfl]
    exact (neg_one_smul F (1 : Module.End F V)).symm
  have hAd_rho : ∀ w q : Q, Ad w (ρu q) = ρu ⁅w, q⁆ * ρu q := by
    intro w q
    have hgrp : ⁅w, q⁆ * q = w * q * w⁻¹ := by group
    calc
      Ad w (ρu q) = (ρu w : Module.End F V) * (ρu q : Module.End F V) *
          (((ρu w)⁻¹ : (Module.End F V)ˣ) : Module.End F V) := hAd_apply w _
      _ = (ρu (w * q * w⁻¹) : Module.End F V) := by
        rw [map_mul, map_mul, map_inv]
        simp [mul_assoc]
      _ = (ρu (⁅w, q⁆ * q) : Module.End F V) := by rw [hgrp]
      _ = (ρu ⁅w, q⁆ : Module.End F V) * (ρu q : Module.End F V) := by
        simp [map_mul]
  let eps : Q → Q → Fˣ := fun q w =>
    if ρ ⁅w, q⁆ = 1 then 1 else if ρ ⁅w, q⁆ = negOne F V then -1 else 1
  have hAd_eps : ∀ q w : Q, Ad w (ρu q) =
      ((eps q w : F)) • (ρu q : Module.End F V) := by
    intro q w
    rw [hAd_rho]
    by_cases h1 : ρ ⁅w, q⁆ = 1
    · have h1u : (ρu ⁅w, q⁆ : Module.End F V) = 1 := by rw [hcoe, h1]; rfl
      have h1' : ⁅ρ w, ρ q⁆ = 1 := by rw [← map_commutatorElement ρ w q, h1]
      rw [h1u]
      simp [eps, h1']
    · by_cases h2 : ρ ⁅w, q⁆ = negOne F V
      · have h2u : (ρu ⁅w, q⁆ : Module.End F V) =
            (negOne F V : Module.End F V) := by rw [hcoe, h2]
        have h1' : ⁅ρ w, ρ q⁆ ≠ 1 := by
          intro hh
          rw [← map_commutatorElement ρ w q] at hh
          exact h1 hh
        have h2' : ⁅ρ w, ρ q⁆ = negOne F V := by rw [← map_commutatorElement ρ w q, h2]
        have hneg_ne : negOne F V ≠ 1 := by
          intro hh
          exact h1' (by rw [h2', hh])
        rw [h2u, hnegOne]
        simp only [eps, h2, hneg_ne, if_false, if_true, smul_mul_assoc, one_mul, Units.coe_neg_one]
      · rcases hc w q with h | h
        · exact absurd h h1
        · exact absurd h h2
  have hEps_mul_w : ∀ q w w' : Q, eps q (w * w') = eps q w * eps q w' := by
    intro q w w'
    have h1 : Ad (w * w') (ρu q) = (Ad w) (Ad w' (ρu q)) := by
      rw [map_mul]
      rfl
    rw [hAd_eps q (w * w')] at h1
    rw [hAd_eps q w'] at h1
    rw [map_smul] at h1
    rw [hAd_eps q w] at h1
    rw [smul_smul] at h1
    have h2 : ((eps q (w * w') : F)) =
        (eps q w' : F) * (eps q w : F) := by
      apply hcancel q
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1
    exact Units.ext (by simpa [Units.val_mul, mul_comm] using h2)
  have hEps_mul_q : ∀ q q' w : Q, eps (q * q') w = eps q w * eps q' w := by
    intro q q' w
    have hcoe_mul : (ρu (q * q') : Module.End F V) =
        (ρu q : Module.End F V) * (ρu q' : Module.End F V) := by
      simp [map_mul]
    have h1 : Ad w (ρu (q * q')) =
        Ad w (ρu q) * Ad w (ρu q') := by
      rw [hcoe_mul]
      exact hAd_mulEnd w (ρu q : Module.End F V) (ρu q' : Module.End F V)
    have h2 : (eps (q * q') w : F) =
        (eps q w : F) * (eps q' w : F) := by
      apply hcancel (q * q')
      calc
        (eps (q * q') w : F) • ((ρu (q * q') : Module.End F V)) =
            Ad w (ρu (q * q')) := (hAd_eps (q * q') w).symm
        _ = Ad w (ρu q) * Ad w (ρu q') := h1
        _ = ((eps q w : F) • (ρu q : Module.End F V)) *
            ((eps q' w : F) • (ρu q' : Module.End F V)) := by
          rw [hAd_eps q w, hAd_eps q' w]
        _ = ((eps q w : F) * (eps q' w : F)) •
            ((ρu q : Module.End F V) * (ρu q' : Module.End F V)) := by
          rw [smul_mul_smul]
        _ = ((eps q w : F) * (eps q' w : F)) •
            (ρu (q * q') : Module.End F V) := by rw [← hcoe_mul]
    exact Units.ext (by simpa [Units.val_mul] using h2)
  have heps_one : ∀ w : Q, eps 1 w = 1 := by
    intro w
    simp [eps]
  have heps_inv : ∀ q w : Q, eps q⁻¹ w = (eps q w)⁻¹ := by
    intro q w
    have h : eps (q * q⁻¹) w = eps q w * eps q⁻¹ w := hEps_mul_q q q⁻¹ w
    rw [mul_inv_cancel, heps_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let T : Type := Q ⧸ Subgroup.center Q
  let s : T → Q := fun t => Quotient.out t
  let χ : T → (Q →* Fˣ) := fun t =>
    MonoidHom.mk' (eps (s t)) (hEps_mul_w (s t))
  have hχ : Function.Injective χ := by
    intro i j hij
    have hpt : ∀ w : Q, eps (s i) w = eps (s j) w := by
      intro w
      exact congrArg (fun f : Q →* Fˣ => f w) hij
    let r : Q := (s j)⁻¹ * s i
    have hrw : ∀ w : Q, eps r w = 1 := by
      intro w
      calc
        eps r w = eps (s j)⁻¹ w * eps (s i) w := hEps_mul_q (s j)⁻¹ (s i) w
        _ = (eps (s j) w)⁻¹ * eps (s i) w := by rw [heps_inv]
        _ = 1 := by rw [hpt w, inv_mul_cancel]
    have hAdr : ∀ w : Q, Ad w (ρu r) = (ρu r : Module.End F V) := by
      intro w
      calc
        Ad w (ρu r) = ((eps r w : F)) • (ρu r : Module.End F V) := hAd_eps r w
        _ = (1 : F) • (ρu r : Module.End F V) := by rw [hrw w]; simp
        _ = (ρu r : Module.End F V) := one_smul _ _
    have hcomm : ∀ w : Q, ⁅w, r⁆ = 1 := by
      intro w
      have h1 : (ρu ⁅w, r⁆ : Module.End F V) *
          (ρu r : Module.End F V) = 1 * (ρu r : Module.End F V) := by
        rw [← hAd_rho w r, hAdr w]
        simp
      have h1u : ρu ⁅w, r⁆ * ρu r = 1 * ρu r := by
        apply Units.ext
        simpa using h1
      have h2u : ρu ⁅w, r⁆ = 1 := mul_right_cancel h1u
      have h4 : ρ ⁅w, r⁆ = 1 := by
        have := congrArg (fun u : (Module.End F V)ˣ =>
          (LinearMap.GeneralLinearGroup.generalLinearEquiv F V) u) h2u
        simpa [ρu] using this
      exact hρ (by simpa using h4)
    have hmem : r ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw : w * r * w⁻¹ = r := by
        calc
          w * r * w⁻¹ = ⁅w, r⁆ * r := by group
          _ = 1 * r := by rw [hcomm w]
          _ = r := one_mul r
      calc
        w * r = (w * r * w⁻¹) * w := by group
        _ = r * w := by rw [hw]
    have hmk : (QuotientGroup.mk (s i) : T) = QuotientGroup.mk (s j) := by
      have h : (QuotientGroup.mk' (Subgroup.center Q) (s j) : Q ⧸ Subgroup.center Q) =
          QuotientGroup.mk' (Subgroup.center Q) (s i) := by
        rw [QuotientGroup.mk'_eq_mk']
        exact ⟨r, hmem, by simp [r]⟩
      exact h.symm
    calc
      i = Quotient.mk _ (Quotient.out i) := (Quotient.out_eq' i).symm
      _ = Quotient.mk _ (s i) := rfl
      _ = Quotient.mk _ (s j) := hmk
      _ = Quotient.mk _ (Quotient.out j) := rfl
      _ = j := Quotient.out_eq' j
  let v : T → Module.End F V := fun t => (ρu (s t) : Module.End F V)
  have hv : ∀ t : T, v t ≠ 0 := fun t => hρu_ne (s t)
  have hEigen : ∀ (t : T) (g : Q),
      Ad g (v t) = (χ t g : F) • v t := by
    intro t g
    exact hAd_eps (s t) g
  have hli : LinearIndependent F v :=
    CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent.linearIndependent
      Ad χ v hv hEigen hχ
  have hcard : (Nat.card T : Cardinal) ≤
      (Module.finrank F (Module.End F V) : Cardinal) := by
    rw [Nat.cast_card]
    exact hli.cardinalMk_le_finrank
  rw [Module.finrank_linearMap] at hcard
  have hcardnat : Nat.card T ≤
      Module.finrank F V * Module.finrank F V :=
    Nat.cast_le.mp hcard
  have hindex : (Subgroup.center Q).index = Nat.card T := by
    rw [Subgroup.index_eq_card]
  rw [hindex]
  simpa [sq, pow_two] using hcardnat

private theorem sz5e1_a13_orderOf_two_zmod_13 : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

private theorem sz5e1_a13_eq_one_of_pow_thirteen_eq_one {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (g : W ≃ₗ[ZMod 2] W)
    (hg : g ^ 13 = 1) (hfin : Module.finrank (ZMod 2) W ≤ 7) : g = 1 := by
  by_contra hne
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hle :=
    CFSG.LinearAlgebra.CoprimeActions.PrimeOrderBinaryLinearDimensionBound.order_le_finrank
      13 (by norm_num) g hg hne
  rw [sz5e1_a13_orderOf_two_zmod_13] at hle
  omega

private noncomputable def sz5e1_a13_addEquivLinear {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod 2) A] [Module (ZMod 2) B] (e : A ≃+ B) : A ≃ₗ[ZMod 2] B where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := fun c x => ZMod.map_smul (f := (e : A →+ B)) c x

theorem sz5e1_aut13_trivial {Q : Type} [Group Q] [Finite Q]
    (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) (hsq : ∀ x : Q, x ^ 2 ∈ Subgroup.center Q)
    (hZc : IsCyclic (Subgroup.center Q)) (hZ2 : IsPGroup 2 (Subgroup.center Q))
    (hidx : (Subgroup.center Q).index ≤ 144) (α : MulAut Q) (hα : α ^ 13 = 1) : α = 1 := by
  classical
  let Z : Subgroup Q := Subgroup.center Q
  have hZ2Z : IsPGroup 2 Z := hZ2
  have hZcyc : IsCyclic Z := hZc
  have hαZ : Z.map (α : Q →* Q) = Z := Subgroup.map_center_eq α
  let αZ : MulAut Z := (MulEquiv.subgroupMap α Z).trans (MulEquiv.subgroupCongr hαZ)
  have hαZ_apply : ∀ z : Z, ((αZ z : Z) : Q) = α z := by
    intro z
    simp [αZ]
  have hαZ13 : αZ ^ 13 = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    have hpow : ∀ n : ℕ, ∀ w : Z, ((αZ ^ n) w : Q) = (α ^ n) (w : Q) := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
          intro w
          rw [pow_succ, MulAut.mul_apply, ih (αZ w), hαZ_apply w]
          rfl
    rw [hpow 13 z, hα]
    simp
  obtain ⟨k, hk⟩ := hZ2Z.exists_card_eq
  have hmulAut_card : Nat.card (MulAut Z) = Nat.totient (Nat.card Z) := IsCyclic.card_mulAut Z
  have hord13 : orderOf αZ ∣ 13 := orderOf_dvd_of_pow_eq_one hαZ13
  have hordcard : orderOf αZ ∣ Nat.card (MulAut Z) := orderOf_dvd_natCard αZ
  have htot : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
    cases k with
    | zero => simp
    | succ j =>
        rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos j)]
        simp
  have hcop : Nat.Coprime 13 (Nat.totient (2 ^ k)) := by
    rw [htot]
    exact Nat.Prime.coprime_pow_of_not_dvd (p := 2) (a := 13) (m := k - 1) Nat.prime_two
      (by norm_num)
  have hone : orderOf αZ = 1 := by
    have hcard : orderOf αZ ∣ Nat.totient (2 ^ k) := by
      rw [hmulAut_card, hk] at hordcard
      exact hordcard
    have hgcd : orderOf αZ ∣ (Nat.totient (2 ^ k)).gcd 13 := Nat.dvd_gcd hcard hord13
    have hcopg : (Nat.totient (2 ^ k)).gcd 13 = 1 := by
      rw [Nat.gcd_comm]
      exact hcop
    rw [hcopg] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hαZeq1 : αZ = 1 := orderOf_eq_one_iff.mp hone
  have hfixZ : ∀ z : Q, z ∈ Z → α z = z := by
    intro z hz
    have h1 : αZ ⟨z, hz⟩ = (1 : MulAut Z) ⟨z, hz⟩ := by rw [hαZeq1]
    have h2 := congrArg (fun w : Z => (w : Q)) h1
    rw [hαZ_apply ⟨z, hz⟩] at h2
    simpa using h2
  have hmulcomm : ∀ x y : Q ⧸ Z, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← commutatorElement_eq_one_iff_mul_comm]
    change ⁅(QuotientGroup.mk' Z) a, (QuotientGroup.mk' Z) b⁆ = 1
    rw [← map_commutatorElement (QuotientGroup.mk' Z) a b]
    exact (QuotientGroup.eq_one_iff ⁅a, b⁆).mpr (hcomm a b)
  let hQcomm : CommGroup (Q ⧸ Z) :=
    { (inferInstance : Group (Q ⧸ Z)) with mul_comm := hmulcomm }
  have hexp : ∀ y : Q ⧸ Z, y ^ 2 = 1 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk' Z) a ^ 2 = 1
    rw [← map_pow (QuotientGroup.mk' Z) a 2]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq a)
  have h2 : ∀ x : Additive (Q ⧸ Z), (2 : ℕ) • x = 0 := by
    intro x
    have hmul : Additive.toMul x * Additive.toMul x = 1 := by
      rw [← pow_two, hexp]
    have hxx : x + x = Additive.ofMul (Additive.toMul x * Additive.toMul x) := by
      conv_lhs => rw [← ofMul_toMul x]
      rw [← ofMul_mul]
    rw [two_nsmul, hxx, hmul, ofMul_one]
  let hWmod : Module (ZMod 2) (Additive (Q ⧸ Z)) := AddCommGroup.zmodModule h2
  have hWfin : Module.Finite (ZMod 2) (Additive (Q ⧸ Z)) := by
    refine Module.Finite.of_fg_top ?_
    rw [Submodule.fg_def]
    exact ⟨Set.univ, Set.finite_univ, Submodule.span_univ⟩
  let eM : MulAut (Q ⧸ Z) := QuotientGroup.congr Z Z α hαZ
  have heM_mk : ∀ a : Q, eM (QuotientGroup.mk a) = QuotientGroup.mk (α a) := by
    intro a
    change QuotientGroup.congr Z Z α hαZ (QuotientGroup.mk a) = QuotientGroup.mk (α a)
    rw [QuotientGroup.congr_mk]
  let eA : Additive (Q ⧸ Z) ≃+ Additive (Q ⧸ Z) :=
    { toFun := fun x => Additive.ofMul (eM (Additive.toMul x))
      invFun := fun x => Additive.ofMul (eM.symm (Additive.toMul x))
      left_inv := fun x => by
        change Additive.ofMul (eM.symm (Additive.toMul (Additive.ofMul (eM (Additive.toMul x)))))
          = x
        rw [toMul_ofMul, MulEquiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun x => by
        change Additive.ofMul (eM (Additive.toMul (Additive.ofMul (eM.symm (Additive.toMul x)))))
          = x
        rw [toMul_ofMul, MulEquiv.apply_symm_apply, ofMul_toMul]
      map_add' := fun x y => by
        rw [toMul_add, map_mul, ofMul_mul] }
  let ᾱ : Additive (Q ⧸ Z) ≃ₗ[ZMod 2] Additive (Q ⧸ Z) := sz5e1_a13_addEquivLinear eA
  have hbar_apply : ∀ y : Q ⧸ Z, ᾱ (Additive.ofMul y) = Additive.ofMul (eM y) := by
    intro y
    change eA (Additive.ofMul y) = Additive.ofMul (eM y)
    rfl
  have heM_pow : ∀ n : ℕ, ∀ a : Q,
      (eM ^ n) (QuotientGroup.mk a) = QuotientGroup.mk ((α ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
        intro a
        calc (eM ^ (n + 1)) (QuotientGroup.mk a)
            = (eM ^ n) (eM (QuotientGroup.mk a)) := by rw [pow_succ, MulAut.mul_apply]
          _ = (eM ^ n) (QuotientGroup.mk (α a)) := by rw [heM_mk]
          _ = QuotientGroup.mk ((α ^ n) (α a)) := ih (α a)
          _ = QuotientGroup.mk ((α ^ (n + 1)) a) := by rw [pow_succ, MulAut.mul_apply]
  have heM13 : eM ^ 13 = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [heM_pow 13 a, hα]
    simp
  have hbar_pow : ∀ n : ℕ, ∀ a : Q,
      (ᾱ ^ n) (Additive.ofMul (QuotientGroup.mk a))
        = Additive.ofMul (QuotientGroup.mk ((α ^ n) a)) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
        intro a
        calc (ᾱ ^ (n + 1)) (Additive.ofMul (QuotientGroup.mk a))
            = (ᾱ ^ n) (ᾱ (Additive.ofMul (QuotientGroup.mk a))) := by
                rw [pow_succ, LinearEquiv.mul_apply]
          _ = (ᾱ ^ n) (Additive.ofMul (eM (QuotientGroup.mk a))) := by rw [hbar_apply]
          _ = (ᾱ ^ n) (Additive.ofMul (QuotientGroup.mk (α a))) := by rw [heM_mk]
          _ = Additive.ofMul (QuotientGroup.mk ((α ^ n) (α a))) := ih (α a)
          _ = Additive.ofMul (QuotientGroup.mk ((α ^ (n + 1)) a)) := by
                rw [pow_succ, MulAut.mul_apply]
  have hbar13 : ᾱ ^ 13 = 1 := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← ofMul_toMul x, ← ha, hbar_pow 13 a, hα]
    simp
  have hfinrank_le : Module.finrank (ZMod 2) (Additive (Q ⧸ Z)) ≤ 7 := by
    by_contra h
    push Not at h
    have hcard : Nat.card (Additive (Q ⧸ Z))
        = 2 ^ Module.finrank (ZMod 2) (Additive (Q ⧸ Z)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h1 : 2 ^ 8 ≤ Nat.card (Additive (Q ⧸ Z)) := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by norm_num) h
    have h2 : Nat.card (Additive (Q ⧸ Z)) = Z.index := Nat.card_congr Additive.toMul
    rw [h2] at h1
    norm_num at h1
    have hidx' : Z.index ≤ 144 := hidx
    omega
  have hbar1 : ᾱ = 1 := sz5e1_a13_eq_one_of_pow_thirteen_eq_one ᾱ hbar13 hfinrank_le
  have hquot : ∀ q : Q, q⁻¹ * α q ∈ Z := by
    intro q
    have h := congrArg
      (fun f : Additive (Q ⧸ Z) ≃ₗ[ZMod 2] Additive (Q ⧸ Z) =>
        f (Additive.ofMul (QuotientGroup.mk q))) hbar1
    simp only [LinearEquiv.coe_one, id_eq] at h
    rw [hbar_apply] at h
    have heq : eM (QuotientGroup.mk q) = QuotientGroup.mk q := by
      have h2 := congrArg Additive.toMul h
      simpa only [toMul_ofMul] using h2
    have hmk1 : (QuotientGroup.mk' Z) (q⁻¹ * α q) = 1 := by
      rw [map_mul, map_inv]
      change (QuotientGroup.mk q)⁻¹ * QuotientGroup.mk (α q) = 1
      rw [← heM_mk q, heq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hmk1
  have hpow : ∀ n : ℕ, ∀ q : Q, (α ^ n) q = q * (q⁻¹ * α q) ^ n := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih =>
        intro q
        have hmem : (q⁻¹ * α q) ^ n ∈ Z := Z.pow_mem (hquot q) n
        calc (α ^ (n + 1)) q = α ((α ^ n) q) := by rw [pow_succ', MulAut.mul_apply]
          _ = α (q * (q⁻¹ * α q) ^ n) := by rw [ih q]
          _ = α q * α ((q⁻¹ * α q) ^ n) := by rw [map_mul]
          _ = α q * ((q⁻¹ * α q) ^ n) := by rw [hfixZ _ hmem]
          _ = q * (q⁻¹ * α q) * (q⁻¹ * α q) ^ n := by rw [mul_inv_cancel_left]
          _ = q * (q⁻¹ * α q) ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hfq13 : ∀ q : Q, (q⁻¹ * α q) ^ 13 = 1 := by
    intro q
    have h := hpow 13 q
    rw [hα, MulAut.one_apply] at h
    have h' : q * 1 = q * (q⁻¹ * α q) ^ 13 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have hcop2 : Nat.Coprime 13 (2 ^ k) :=
    Nat.Prime.coprime_pow_of_not_dvd (p := 2) (a := 13) (m := k) Nat.prime_two (by norm_num)
  have hfq1 : ∀ q : Q, q⁻¹ * α q = 1 := by
    intro q
    let z : Z := ⟨q⁻¹ * α q, hquot q⟩
    have hz13 : z ^ 13 = 1 := Subtype.ext (by
      change (q⁻¹ * α q) ^ 13 = 1
      exact hfq13 q)
    have hdvd13 : orderOf z ∣ 13 := orderOf_dvd_of_pow_eq_one hz13
    have hdvd2 : orderOf z ∣ Nat.card Z := _root_.orderOf_dvd_natCard z
    rw [hk] at hdvd2
    have h1 : orderOf z = 1 := by
      have hgcd : orderOf z ∣ (2 ^ k).gcd 13 := Nat.dvd_gcd hdvd2 hdvd13
      have h21 : (2 ^ k).gcd 13 = 1 := by
        rw [Nat.gcd_comm]
        exact hcop2
      rw [h21] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)
  apply MulEquiv.ext
  intro q
  show α q = q
  calc α q = q * (q⁻¹ * α q) := by rw [mul_inv_cancel_left]
    _ = q := by rw [hfq1 q, mul_one]

private theorem sz5e1_pce_commutator_center {G : Type*} [Group G]
    (h : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥) :
    ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero] at h
  intro x y
  rw [Subgroup.mem_center_iff]
  intro z
  have hmem : ⁅⁅x, y⁆, z⁆ ∈ (⊥ : Subgroup G) := by
    rw [← h]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      (Subgroup.mem_top z)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem.symm

private theorem sz5e1_pce_commutator_sq_eq_one {G : Type*} [Group G]
    (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hsq : ∀ x : G, x ^ 2 ∈ Subgroup.center G) :
    ∀ a ∈ (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G), a ^ 2 = 1 := by
  have hgen : ∀ x y : G, ⁅x, y⁆ ^ 2 = 1 := by
    intro x y
    have hx : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp (hcomm x y) x
    rw [hx.commutatorElement_pow_left 2, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hsq x) y).symm
  have hle : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  intro a ha
  rw [Subgroup.commutator_def] at ha
  refine Subgroup.closure_induction (p := fun a _ => a ^ 2 = 1) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨y, -, z, -, rfl⟩
    exact hgen y z
  · simp
  · intro x y hx hy ihx ihy
    have hxy : Commute x y := Subgroup.mem_center_iff.mp (hle hy) x
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  · intro x hx ihx
    rw [inv_pow, ihx, inv_one]

private theorem sz5e1_pce_cyclic {Z : Type*} [CommGroup Z] [Finite Z] (hZ2 : IsPGroup 2 Z)
    (hbound : Nat.card (powMonoidHom 2 : Z →* Z).ker ≤ 2) : IsCyclic Z := by
  classical
  obtain ⟨e, he⟩ := hZ2.exists_card_eq
  refine CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    e Z hZ2 he ?_
  intro left right hleft hright
  by_contra hne
  have hleft1 : left ≠ 1 := by rintro rfl; simp at hleft
  have hright1 : right ≠ 1 := by rintro rfl; simp at hright
  have hleftK : left ∈ (powMonoidHom 2 : Z →* Z).ker := by
    rw [MonoidHom.mem_ker]
    exact (orderOf_eq_prime_iff.mp hleft).1
  have hrightK : right ∈ (powMonoidHom 2 : Z →* Z).ker := by
    rw [MonoidHom.mem_ker]
    exact (orderOf_eq_prime_iff.mp hright).1
  let K : Subgroup Z := (powMonoidHom 2 : Z →* Z).ker
  have hboundK : Nat.card K ≤ 2 := hbound
  let a : K := ⟨left, hleftK⟩
  let b : K := ⟨right, hrightK⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hleft1
    exact congrArg (fun x : K => (x : Z)) h
  have hb1 : b ≠ 1 := by
    intro h
    apply hright1
    exact congrArg (fun x : K => (x : Z)) h
  have hab : a ≠ b := by
    intro h
    apply hne
    exact congrArg (fun x : K => (x : Z)) h
  have hcard3 : 3 ≤ Nat.card K := by
    have hinj : Function.Injective (fun i : Fin 3 => ![(1 : K), a, b] i) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have h3 := Nat.card_le_card_of_injective (fun i : Fin 3 => ![(1 : K), a, b] i) hinj
    simpa using h3
  omega

theorem sz5e1_P_central_of_bounds {D : Type} [Group D] [Finite D] (P : Subgroup D) [P.Normal]
    (hD : SzSetup D P)
    (hS1 : ∀ E : Subgroup D, E.Normal → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 2)
    (hS2 : ∀ Q : Subgroup D, Q ≤ P → Q.Normal → Nat.card (⁅Q, Q⁆ : Subgroup D) ≤ 2 →
      (Subgroup.center ↥Q).index ≤ 144) :
    ∀ p ∈ P, ∀ d : D, p * d = d * p := by
  classical
  obtain ⟨C, hCrest⟩ :=
    CFSG.GroupTheory.FT63ChII.ft_lemma_8_2 (p := 2) (P := ↥P) hD.2.1
  have hCchar : C.Characteristic := hCrest.1
  have hCclass : C.lowerCentralSeries 2 = ⊥ := hCrest.2.1.1
  have hCeleab : CFSG.IsElementaryAbelian 2 (C ⧸ Subgroup.center C) := hCrest.2.1.2
  have hCfixpg : IsPGroup 2 (fixingSubgroup (MulAut ↥P) (C : Set ↥P)) := hCrest.2.2.1
  have hCcomm : ⁅(⊤ : Subgroup ↥P), C⁆ ≤ (Subgroup.center C).map C.subtype :=
    hCrest.2.2.2.1
  have hCcen : Subgroup.centralizer (C : Set ↥P) = (Subgroup.center C).map C.subtype :=
    hCrest.2.2.2.2
  let Q : Subgroup D := C.map P.subtype
  have hQle : Q ≤ P := Subgroup.map_subtype_le C
  have hQnormal : Q.Normal := by
    refine ⟨fun x hx d => ?_⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr
      ⟨((MulAut.characteristic C (MulAut.conjNormal d)) ⟨c, hc⟩ : ↥C), ?_, ?_⟩
    · exact ((MulAut.characteristic C (MulAut.conjNormal d)) ⟨c, hc⟩).2
    · change (MulAut.conjNormal d c : D) = d * P.subtype c * d⁻¹
      rw [MulAut.conjNormal_apply]
      rfl
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    obtain ⟨k, hk⟩ := hD.2.1 (⟨(x : D), hQle x.2⟩ : ↥P)
    refine ⟨k, ?_⟩
    have hkD : (x : D) ^ (2 ^ k) = 1 := by
      simpa using congrArg (Subtype.val) hk
    rw [← Subgroup.orderOf_coe x]
    exact orderOf_dvd_of_pow_eq_one hkD
  have hQclass : Q.lowerCentralSeries 2 = ⊥ := by
    change (C.map P.subtype).lowerCentralSeries 2 = ⊥
    rw [← Subgroup.map_lowerCentralSeries (S := C) P.subtype 2, hCclass, Subgroup.map_bot]
  have hQtclass : (⊤ : Subgroup ↥Q).lowerCentralSeries 2 = ⊥ := by
    have h := Subgroup.top_subtype_lowerCentralSeries Q 2
    rw [hQclass] at h
    exact Subgroup.map_subtype_inj.mp (h.trans (Subgroup.map_bot (f := Q.subtype)).symm)
  have hQcomm : ∀ x y : ↥Q, ⁅x, y⁆ ∈ Subgroup.center ↥Q :=
    sz5e1_pce_commutator_center hQtclass
  have hsqC : ∀ x : ↥C, x ^ 2 ∈ Subgroup.center ↥C := by
    intro x
    have hx : (QuotientGroup.mk x : ↥C ⧸ Subgroup.center ↥C) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (@IsElementaryAbelian.exponent_dvd_p 2 (↥C ⧸ Subgroup.center ↥C) _ hCeleab) _
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx
  have hsqQ : ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q := by
    intro x
    obtain ⟨c, hc, hxc⟩ := Subgroup.mem_map.mp x.2
    have hx2 : x ^ 2 =
        (⟨P.subtype (c ^ 2), Subgroup.mem_map_of_mem _ (pow_mem hc 2)⟩ : ↥Q) := by
      apply Subtype.ext
      show (x : D) ^ 2 = P.subtype (c ^ 2)
      rw [← hxc, map_pow]
    rw [hx2]
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨c', hc', hyc⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    show (y : D) * P.subtype (c ^ 2) = P.subtype (c ^ 2) * (y : D)
    rw [← hyc, ← map_mul, ← map_mul]
    congr 1
    exact congrArg (Subtype.val)
      (Subgroup.mem_center_iff.mp (hsqC ⟨c, hc⟩) ⟨c', hc'⟩)
  let Z : Subgroup ↥Q := Subgroup.center ↥Q
  let cmZ : CommGroup Z := Group.commGroupOfCenterEqTop Subgroup.center_eq_top
  let sqZ : Z →* Z := @powMonoidHom Z cmZ.toCommMonoid 2
  let ι : Z →* D := Q.subtype.comp Z.subtype
  let E : Subgroup D := sqZ.ker.map ι
  have hιinj : Function.Injective ι := Q.subtype_injective.comp Z.subtype_injective
  have hZ2 : IsPGroup 2 Z := hQ2.to_subgroup Z
  have hEabel : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ka, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨kb, -, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ka.2 (kb : ↥Q)).symm
  have hEsq : ∀ a ∈ E, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow]
    have hk2 : k ^ 2 = 1 := MonoidHom.mem_ker.mp hk
    rw [hk2, map_one]
  have hEnorm : E.Normal := by
    refine ⟨fun x hx d => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    let phi : MulAut ↥Q := MulAut.conjNormal d
    have hk2 : (k : ↥Q) ^ 2 = 1 :=
      congrArg (fun z : Z => (z : ↥Q)) (MonoidHom.mem_ker.mp hk)
    have hcent : phi (k : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := phi.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp k.2 y'
    have hker : (⟨phi (k : ↥Q), hcent⟩ : Z) ∈ sqZ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (phi (k : ↥Q)) ^ 2 = 1
      rw [← map_pow, hk2, map_one]
    refine Subgroup.mem_map.mpr ⟨⟨phi (k : ↥Q), hcent⟩, hker, ?_⟩
    show (Q.subtype (Z.subtype ⟨phi (k : ↥Q), hcent⟩) : D) = d * Q.subtype (Z.subtype k) * d⁻¹
    change (phi (k : ↥Q) : D) = d * (k : D) * d⁻¹
    rw [MulAut.conjNormal_apply]
  have hEcard : Nat.card E ≤ 2 := hS1 E hEnorm hEabel hEsq
  have hE1leE : (⁅Q, Q⁆ : Subgroup D) ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    let a : ↥Q := ⟨x, hx⟩
    let b : ↥Q := ⟨y, hy⟩
    have hmem : (⟨⁅a, b⁆, hQcomm a b⟩ : Z) ∈ sqZ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show ⁅a, b⁆ ^ 2 = 1
      exact sz5e1_pce_commutator_sq_eq_one hQcomm hsqQ ⁅a, b⁆
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    refine Subgroup.mem_map.mpr ⟨⟨⁅a, b⁆, hQcomm a b⟩, hmem, ?_⟩
    show (Q.subtype (Z.subtype ⟨⁅a, b⁆, hQcomm a b⟩) : D) = ⁅x, y⁆
    rfl
  have hE1card : Nat.card (⁅Q, Q⁆ : Subgroup D) ≤ 2 :=
    (Subgroup.card_le_of_le hE1leE).trans hEcard
  have hidx : (Subgroup.center ↥Q).index ≤ 144 := hS2 Q hQle hQnormal hE1card
  have hbound : Nat.card sqZ.ker ≤ 2 := by
    have h := hEcard
    change Nat.card (sqZ.ker.map ι) ≤ 2 at h
    rwa [Subgroup.card_map_of_injective hιinj] at h
  have hZc : IsCyclic Z := @sz5e1_pce_cyclic Z cmZ _ hZ2 hbound
  have h13dvd : 13 ∣ Nat.card (D ⧸ P) := sz5e1_sz8_thirteen_dvd hD.2.2
  have h13card : 13 ∣ Nat.card D := by
    have h1 : 13 ∣ P.index := by rwa [Subgroup.index_eq_card]
    exact dvd_trans h1 (Subgroup.index_dvd_card (H := P))
  obtain ⟨g, hg⟩ := @exists_prime_orderOf_dvd_card' D _ _ 13 ⟨by norm_num⟩ h13card
  have hg13 : g ^ 13 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hgnot : g ∉ P := by
    intro hgP
    obtain ⟨n, hn⟩ := hD.2.1 (⟨g, hgP⟩ : ↥P)
    have hgn : g ^ (2 ^ n) = 1 := by simpa using congrArg (Subtype.val) hn
    have hdvd : 13 ∣ 2 ^ n := by
      have := orderOf_dvd_of_pow_eq_one hgn
      rwa [hg] at this
    exact (by norm_num : ¬ (13 ∣ 2))
      (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 13) hdvd)
  have hconjQ13 : (MulAut.conjNormal g : MulAut ↥Q) ^ 13 = 1 := by
    rw [← map_pow, hg13, map_one]
  have hconjQ : (MulAut.conjNormal g : MulAut ↥Q) = 1 :=
    sz5e1_aut13_trivial hQcomm hsqQ hZc hZ2 hidx _ hconjQ13
  have hgQ : ∀ z ∈ Q, g * z = z * g := by
    intro z hz
    have hfix : (MulAut.conjNormal g : MulAut ↥Q) ⟨z, hz⟩ = ⟨z, hz⟩ := by
      rw [hconjQ]; rfl
    have hval : g * z * g⁻¹ = z := by
      have h := congrArg (Subtype.val) hfix
      simpa [MulAut.conjNormal_apply] using h
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hval]
  let beta : MulAut ↥P := MulAut.conjNormal g
  have hbeta13 : beta ^ 13 = 1 := by
    dsimp [beta]
    rw [← map_pow, hg13, map_one]
  have hbetamem : beta ∈ fixingSubgroup (MulAut ↥P) (C : Set ↥P) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    show beta y = y
    dsimp [beta]
    apply Subtype.ext
    show g * (y : D) * g⁻¹ = (y : D)
    have hyQ : (y : D) ∈ Q := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [hgQ (y : D) hyQ]
    group
  have hbetaorder : orderOf beta = 1 := by
    have hdvd13 : orderOf beta ∣ 13 := orderOf_dvd_of_pow_eq_one hbeta13
    obtain ⟨n, hn⟩ := hCfixpg ⟨beta, hbetamem⟩
    have hn' : beta ^ (2 ^ n) = 1 := by simpa using congrArg (Subtype.val) hn
    have hdvd2 : orderOf beta ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hcop : Nat.Coprime 13 (2 ^ n) :=
      ((Nat.coprime_primes (by norm_num) (by norm_num)).mpr (by norm_num)).pow_right n
    have hdvd1 : orderOf beta ∣ 1 := by
      have h := Nat.dvd_gcd hdvd13 hdvd2
      rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
    exact Nat.dvd_one.mp hdvd1
  have hbeta1 : beta = 1 := orderOf_eq_one_iff.mp hbetaorder
  have hgP : ∀ p : ↥P, g * (p : D) = (p : D) * g := by
    intro p
    have hfix : beta p = p := by rw [hbeta1]; rfl
    have hval : g * (p : D) * g⁻¹ = (p : D) := by
      have h := congrArg (Subtype.val) hfix
      dsimp [beta] at h
      simpa [MulAut.conjNormal_apply] using h
    calc g * (p : D) = (g * (p : D) * g⁻¹) * g := by group
      _ = (p : D) * g := by rw [hval]
  let N : Subgroup D := Subgroup.centralizer (P : Set D)
  have hgN : g ∈ N := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hgP ⟨p, hp⟩).symm
  have hNtop : N = ⊤ := by
    by_contra hN
    have hd : ∃ d : D, d ∉ N := by
      by_contra h
      apply hN
      rw [Subgroup.eq_top_iff']
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨d, hdN⟩ := hd
    have hρ : ∃ k : D, (QuotientGroup.mk' N) k ≠ 1 := by
      refine ⟨d, ?_⟩
      intro h
      exact hdN ((QuotientGroup.eq_one_iff d).mp h)
    have hker : (QuotientGroup.mk' N : D →* D ⧸ N).ker ≤ P :=
      ker_le_of_nontrivial P hD (QuotientGroup.mk' N) hρ
    have hgle : g ∈ (QuotientGroup.mk' N : D →* D ⧸ N).ker := by
      rw [QuotientGroup.ker_mk']
      exact hgN
    exact hgnot (hker hgle)
  intro p hp d
  have hdN : d ∈ N := by rw [hNtop]; trivial
  rw [Subgroup.mem_centralizer_iff] at hdN
  exact hdN p hp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
