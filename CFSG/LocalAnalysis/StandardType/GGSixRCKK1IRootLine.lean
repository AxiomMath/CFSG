module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.RCKC1

@[expose] def RCKRootLineScalars {U : Type*} [Group U] (R : Subgroup U) (Fq : Type) [Field Fq]
    (ε : Multiplicative Fq ≃* R) : Prop :=
  ∀ l : Fq, l ≠ 0 → ∃ h : U, ∀ t : Fq,
    h * (ε (Multiplicative.ofAdd t) : U) * h⁻¹ = ε (Multiplicative.ofAdd (l * t))

@[expose] def RCKRootLineAt (M : LieUniversal) (f : ℕ) : Prop :=
  ∃ β : Fin M.D.rank → ℤ, β ∈ M.D.roots ∧ CFSG.StandardType.GGLongRoot M.D β ∧
    ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq) (ε : Multiplicative Fq ≃* M.D.rootGroup β),
      Nat.card Fq = 2 ^ f ∧ RCKRootLineScalars (M.D.rootGroup β) Fq ε

@[expose] def RCKRootLineAll (M : LieUniversal) (f : ℕ) : Prop :=
  ∀ β : Fin M.D.rank → ℤ, β ∈ M.D.roots → CFSG.StandardType.GGLongRoot M.D β →
    ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq) (ε : Multiplicative Fq ≃* M.D.rootGroup β),
      Nat.card Fq = 2 ^ f ∧ RCKRootLineScalars (M.D.rootGroup β) Fq ε

theorem rckExists_longRoot (M : LieUniversal) (hr : 0 < M.D.rank) :
    ∃ β : Fin M.D.rank → ℤ, β ∈ M.D.roots ∧ CFSG.StandardType.GGLongRoot M.D β := by
  obtain ⟨γ₀, hγ₀, hmax⟩ := CFSG.StandardType.exists_maxHeight (D := M.D) hr
  exact ⟨γ₀, hγ₀, 1, γ₀, hγ₀, hmax, by rw [map_one, Module.End.one_apply]⟩

theorem rckRootLineAt_of_all {M : LieUniversal} {f : ℕ} (h : RCKRootLineAll M f) (hr : 0 < M.D.rank) :
    RCKRootLineAt M f := by
  obtain ⟨β, hβ, hlong⟩ := rckExists_longRoot M hr
  obtain ⟨Fq, i1, i2, ε, hcard, hsc⟩ := h β hβ hlong
  exact ⟨β, hβ, hlong, Fq, i1, i2, ε, hcard, hsc⟩

theorem rckRootFieldExact_of_scalars {M : LieUniversal} {β : Fin M.D.rank → ℤ} {Fq : Type} [Field Fq]
    {ε : Multiplicative Fq ≃* M.D.rootGroup β} (h1 : RCKRootLineScalars (M.D.rootGroup β) Fq ε)
    (hC : RCKLemmaHCent M β) : RCKRootFieldExact (M.D.rootGroup β) Fq ε := by
  refine ⟨h1, fun n hn => ?_⟩
  set x₀ : M.K := (ε (Multiplicative.ofAdd 1) : M.K) with hx₀def
  have hx₀ : x₀ ∈ M.D.rootGroup β := (ε (Multiplicative.ofAdd 1)).2
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    have h' : ε (Multiplicative.ofAdd (1 : Fq)) = 1 := Subtype.ext h
    have h'' : Multiplicative.ofAdd (1 : Fq) = 1 := by
      simpa using congrArg ε.symm h'
    exact one_ne_zero (Multiplicative.ofAdd.injective (h''.trans ofAdd_zero.symm))
  have hnx : n * x₀ * n⁻¹ ∈ M.D.rootGroup β := (Subgroup.mem_normalizer_iff.mp hn x₀).mp hx₀
  set s : Fq := Multiplicative.toAdd (ε.symm ⟨n * x₀ * n⁻¹, hnx⟩) with hsdef
  have hεs : (ε (Multiplicative.ofAdd s) : M.K) = n * x₀ * n⁻¹ := by
    rw [hsdef, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hs0 : s ≠ 0 := by
    intro h0
    apply hx₀1
    have h2 : n * x₀ * n⁻¹ = 1 := by rw [← hεs, h0, ofAdd_zero, map_one]; rfl
    calc x₀ = n⁻¹ * (n * x₀ * n⁻¹) * n := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨h, hh⟩ := h1 s hs0
  have hfix : (h⁻¹ * n) * x₀ * (h⁻¹ * n)⁻¹ = x₀ := by
    have e1 : h * x₀ * h⁻¹ = n * x₀ * n⁻¹ := by
      rw [← hεs, hx₀def, hh 1, mul_one]
    calc (h⁻¹ * n) * x₀ * (h⁻¹ * n)⁻¹ = h⁻¹ * (n * x₀ * n⁻¹) * h := by group
      _ = h⁻¹ * (h * x₀ * h⁻¹) * h := by rw [e1]
      _ = x₀ := by group
  have hcent : h⁻¹ * n ∈ Subgroup.centralizer ({x₀} : Set M.K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (h⁻¹ * n) * x₀ = ((h⁻¹ * n) * x₀ * (h⁻¹ * n)⁻¹) * (h⁻¹ * n) := by group
      _ = x₀ * (h⁻¹ * n) := by rw [hfix]
  have hcR := hC x₀ hx₀ hx₀1 hcent
  refine ⟨s, hs0, fun t => ?_⟩
  have hcomm : (h⁻¹ * n) * (ε (Multiplicative.ofAdd t) : M.K) =
      (ε (Multiplicative.ofAdd t) : M.K) * (h⁻¹ * n) :=
    ((Subgroup.mem_centralizer_iff.mp hcR) _ (ε (Multiplicative.ofAdd t)).2).symm
  calc n * (ε (Multiplicative.ofAdd t) : M.K) * n⁻¹
      = h * ((h⁻¹ * n) * (ε (Multiplicative.ofAdd t) : M.K)) * (h⁻¹ * n)⁻¹ * h⁻¹ := by group
    _ = h * ((ε (Multiplicative.ofAdd t) : M.K) * (h⁻¹ * n)) * (h⁻¹ * n)⁻¹ * h⁻¹ := by rw [hcomm]
    _ = h * (ε (Multiplicative.ofAdd t) : M.K) * h⁻¹ := by group
    _ = ε (Multiplicative.ofAdd (s * t)) := hh t

theorem rckRootLine_of_chevalleyExtras {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
    [CharP F 2] {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)} (hE : ChevalleyExtras D F x C O)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (i : Fin D.rank)
    (hc : (∑ j, D.cartan i j * β j) = 1 ∨ (∑ j, D.cartan i j * β j) = 2 ∨ (∑ j, D.cartan i j * β j) = -1 ∨
      (∑ j, D.cartan i j * β j) = -2) :
    ∃ ε : Multiplicative F ≃* D.rootGroup β, (∀ c : F, (ε (Multiplicative.ofAdd c) : K) = x β c) ∧
      RCKRootLineScalars (D.rootGroup β) F ε := by
  obtain ⟨himg, hadd, hinj⟩ := hE.param β hβ
  have hx0 : x β 0 = 1 := by
    have h := hadd 0 0
    rw [zero_add] at h
    exact mul_left_cancel (h.symm.trans (mul_one (x β 0)).symm)
  let φ : Multiplicative F →* D.rootGroup β :=
    { toFun := fun a => ⟨x β (Multiplicative.toAdd a),
        (himg _).mpr ⟨Multiplicative.toAdd a, rfl⟩⟩
      map_one' := Subtype.ext (by
        show x β (Multiplicative.toAdd (1 : Multiplicative F)) = 1
        rw [show Multiplicative.toAdd (1 : Multiplicative F) = 0 from rfl]
        exact hx0)
      map_mul' := fun a b => Subtype.ext (by
        show x β (Multiplicative.toAdd (a * b)) =
          x β (Multiplicative.toAdd a) * x β (Multiplicative.toAdd b)
        rw [toAdd_mul, hadd]) }
  have hφbij : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun g => ?_⟩
    · have h1 : Multiplicative.toAdd a = Multiplicative.toAdd b :=
        hinj (congrArg Subtype.val hab)
      exact Multiplicative.toAdd.injective h1
    · obtain ⟨c, hc⟩ := (himg g.1).mp g.2
      exact ⟨Multiplicative.ofAdd c, Subtype.ext (by
        show x β (Multiplicative.toAdd (Multiplicative.ofAdd c)) = g.1
        rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl]
        exact hc)⟩
  let ε : Multiplicative F ≃* D.rootGroup β := MulEquiv.ofBijective φ hφbij
  have hε : ∀ c : F, (ε (Multiplicative.ofAdd c) : K) = x β c := by
    intro c
    have h1 : ε (Multiplicative.ofAdd c) = φ (Multiplicative.ofAdd c) := rfl
    rw [h1]
    rfl
  refine ⟨ε, hε, ?_⟩
  set c₀ : ℤ := ∑ j, D.cartan i j * β j with hc₀
  have hreflrefl : CFSG.LieType.RootSystem.reflection D.cartan i
      (CFSG.LieType.RootSystem.reflection D.cartan i β) = β := by
    have h := congrArg (fun f : Module.End ℤ (Fin D.rank → ℤ) => f β)
      (CFSG.LieType.RootSystem.reflection_mul_self (D.isFiniteType.apply_self i))
    simpa [Module.End.mul_apply] using h
  have hrefl : CFSG.LieType.RootSystem.reflection D.cartan i β ∈ D.roots := by
    have h := (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem
      i β hβ
    rwa [CFSG.LieType.Steinberg.RootSystem.ofCartan_refl_apply] at h
  obtain ⟨esβ, hesβ, hweylsβ⟩ :=
    hE.weyl i (CFSG.LieType.RootSystem.reflection D.cartan i β) hrefl
  have hsum : (∑ j, D.cartan i j *
      (CFSG.LieType.RootSystem.reflection D.cartan i β) j) = -c₀ := by
    rw [← CFSG.LieType.RootSystem.coroot_apply,
      CFSG.LieType.RootSystem.coroot_reflection (D.isFiniteType.apply_self i),
      CFSG.LieType.RootSystem.coroot_apply]
  have hesβ1 : (esβ : F) = 1 := by
    rcases hesβ with h | h
    · rw [h]; exact Int.cast_one
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have hinner : ∀ v : F,
      weylElement x i 1 * x (CFSG.LieType.RootSystem.reflection D.cartan i β) v *
        (weylElement x i 1)⁻¹ = x β v := by
    intro v
    have h := hweylsβ 1 v
    rw [hreflrefl, hesβ1] at h
    simpa using h
  have hinner' : ∀ u : F,
      (weylElement x i 1)⁻¹ * x β u * (weylElement x i 1) =
        x (CFSG.LieType.RootSystem.reflection D.cartan i β) u := by
    intro u
    have h := hinner u
    calc (weylElement x i 1)⁻¹ * x β u * (weylElement x i 1)
        = (weylElement x i 1)⁻¹ *
            (weylElement x i 1 * x (CFSG.LieType.RootSystem.reflection D.cartan i β) u *
              (weylElement x i 1)⁻¹) * (weylElement x i 1) := by rw [← h]
      _ = x (CFSG.LieType.RootSystem.reflection D.cartan i β) u := by group
  have houter : ∀ (t : Fˣ) (v : F),
      weylElement x i t * x (CFSG.LieType.RootSystem.reflection D.cartan i β) v *
        (weylElement x i t)⁻¹ = x β (((t : F) ^ c₀) * v) := by
    intro t v
    have h := hweylsβ t v
    have hexp : -(∑ j, D.cartan i j *
        (CFSG.LieType.RootSystem.reflection D.cartan i β) j) = c₀ := by
      rw [hsum]; ring
    rw [hreflrefl, hexp, hesβ1] at h
    rw [h]
    congr 1
    rw [one_mul, Units.val_zpow_eq_zpow_val]
  have hconj : ∀ (t : Fˣ) (u : F),
      (weylElement x i t * (weylElement x i 1)⁻¹) * x β u *
        (weylElement x i t * (weylElement x i 1)⁻¹)⁻¹ = x β (((t : F) ^ c₀) * u) := by
    intro t u
    calc (weylElement x i t * (weylElement x i 1)⁻¹) * x β u *
          (weylElement x i t * (weylElement x i 1)⁻¹)⁻¹
        = weylElement x i t *
            ((weylElement x i 1)⁻¹ * x β u * (weylElement x i 1)) *
            (weylElement x i t)⁻¹ := by group
      _ = weylElement x i t * x (CFSG.LieType.RootSystem.reflection D.cartan i β) u *
            (weylElement x i t)⁻¹ := by rw [hinner']
      _ = x β (((t : F) ^ c₀) * u) := houter t u
  have hsqrt : ∀ l : F, ∃ s : F, s ^ 2 = l := fun l =>
    (Function.Injective.bijective_of_finite (CharTwo.sq_injective (R := F))).2 l
  intro l hl
  have hpow : ∃ t : Fˣ, (t : F) ^ c₀ = l := by
    rcases hc with h1 | h2 | h3 | h4
    · exact ⟨Units.mk0 l hl, by rw [h1, zpow_one, Units.val_mk0]⟩
    · obtain ⟨s, hs⟩ := hsqrt l
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
        exact hl hs.symm
      exact ⟨Units.mk0 s hs0, by
        rw [h2, Units.val_mk0]
        exact (zpow_natCast s 2).trans hs⟩
    · exact ⟨(Units.mk0 l hl)⁻¹, by
        rw [h3, Units.val_inv_eq_inv_val, Units.val_mk0, zpow_neg_one, inv_inv]⟩
    · obtain ⟨s, hs⟩ := hsqrt l
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
        exact hl hs.symm
      exact ⟨(Units.mk0 s hs0)⁻¹, by
        rw [h4, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, inv_pow, inv_inv]
        exact hs⟩
  obtain ⟨t₀, ht₀⟩ := hpow
  refine ⟨weylElement x i t₀ * (weylElement x i 1)⁻¹, fun t => ?_⟩
  rw [hε t, hε (l * t), ← ht₀]
  exact hconj t₀ t

end CFSG.StandardType.RCKK1I
