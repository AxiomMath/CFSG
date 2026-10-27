module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A1cModuleBridge

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise
open CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem normalizes_of_conj (Λ H : Subgroup Γ) (h : ∀ g ∈ H, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) :
    XMod.Normalizes ↥Λ ↥H Q := by
  intro t a
  refine ⟨⟨(t : Γ) * (a : Γ) * (t : Γ)⁻¹, h t t.2 a a.2⟩, fun q => ?_⟩
  change (t : Γ) • (a : Γ) • q = ((t : Γ) * (a : Γ) * (t : Γ)⁻¹) • (t : Γ) • q
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem normalizes_whole (Λ : Subgroup Γ) (h : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) :
    XMod.Normalizes ↥Λ Γ Q := by
  intro t a
  refine ⟨⟨t * (a : Γ) * t⁻¹, h t a a.2⟩, fun q => ?_⟩
  change t • (a : Γ) • q = (t * (a : Γ) * t⁻¹) • t • q
  rw [smul_smul, smul_smul]
  congr 1
  group

theorem isIrr_smul {Λ : Type*} [Group Λ] {T : Type*} [Group T] [MulDistribMulAction Λ Q]
    [MulDistribMulAction T Q] (h : XMod.Normalizes Λ T Q) (t : T) {L : Subgroup Q}
    (hL : XMod.IsIrr Λ L) : XMod.IsIrr Λ (t • L) := by
  refine ⟨XMod.isInv_smul_of_normalizes h t hL.1, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : L = ⊥ := by
      have := congrArg (fun J => t⁻¹ • J) h0
      simpa [smul_smul, Subgroup.smul_bot] using this
    exact hL.2.1.ne' h1
  · intro J hJ _ hJL
    have hJ' : XMod.IsInv Λ (t⁻¹ • J) := XMod.isInv_smul_of_normalizes h t⁻¹ hJ
    have hle : t⁻¹ • J ≤ L := by
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t⁻¹)).2 hJL
      simpa [inv_smul_smul] using this
    have hJeq : J = t • (t⁻¹ • J) := by rw [smul_inv_smul]
    rcases hL.2.2 (t⁻¹ • J) hJ' bot_le hle with h1 | h1
    · left
      rw [hJeq, h1, Subgroup.smul_bot]
    · right
      rw [hJeq, h1]

@[expose] def typeStab (Λ : Subgroup Γ) (hN : XMod.Normalizes ↥Λ Γ Q) {S₀ : Subgroup Q}
    (hS₀ : XMod.IsInv ↥Λ S₀) : Subgroup Γ where
  carrier := {x | XMod.Iso ↥Λ (x • S₀) S₀}
  one_mem' := by
    change XMod.Iso ↥Λ ((1 : Γ) • S₀) S₀
    rw [one_smul]
    exact XMod.Iso.refl S₀
  mul_mem' := by
    intro x y hx hy
    change XMod.Iso ↥Λ ((x * y) • S₀) S₀
    rw [mul_smul]
    exact (XMod.iso_smul hN x hy).trans hx
  inv_mem' := by
    intro x hx
    change XMod.Iso ↥Λ (x⁻¹ • S₀) S₀
    have h1 := XMod.iso_smul hN x⁻¹ hx
    rw [inv_smul_smul] at h1
    exact XMod.Iso.symm hS₀ h1

theorem mem_typeStab {Λ : Subgroup Γ} {hN : XMod.Normalizes ↥Λ Γ Q} {S₀ : Subgroup Q}
    {hS₀ : XMod.IsInv ↥Λ S₀} {x : Γ} : x ∈ typeStab Λ hN hS₀ ↔ XMod.Iso ↥Λ (x • S₀) S₀ := Iff.rfl

theorem isSylowTwoOf_top_conj [Finite Γ] {T : Subgroup Γ} (hT : IsSylowTwoOf T ⊤) (g : Γ) :
    IsSylowTwoOf (T.map (MulAut.conj g).toMonoidHom) ⊤ := by
  rw [A4.isSylowTwoOf_iff_maximal] at hT ⊢
  obtain ⟨-, hTp, hmax⟩ := hT
  refine ⟨le_top, hTp.map _, fun P _ hP hTP => ?_⟩
  have hP' : IsPGroup 2 (P.map (MulAut.conj g⁻¹).toMonoidHom) := hP.map _
  have hTP' : T ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g * x * g⁻¹, hTP ⟨x, hx, rfl⟩, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group
  have := hmax _ le_top hP' hTP'
  intro y hy
  have h1 : g⁻¹ * y * g⁻¹⁻¹ ∈ T := by
    have := this ⟨y, hy, rfl⟩
    exact this
  exact ⟨g⁻¹ * y * g⁻¹⁻¹, h1, by
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
    group⟩

theorem exists_fixing_translate [Finite Γ] {Λ T A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hT : IsSylowTwoOf T ⊤) (hAT : A ≤ T)
    {V : Subgroup Q} (hVΛ : XMod.IsInv ↥Λ V) (hVT : ∀ t ∈ T, t • V = V) (g₀ : Γ) :
    ∃ g : Γ, XMod.Iso ↥Λ (g • V) (g₀ • V) ∧
      ∀ a ∈ A, XMod.Iso ↥Λ (a • (g₀ • V)) (g₀ • V) → g⁻¹ * a * g ∈ T := by
  classical
  have hN : XMod.Normalizes ↥Λ Γ Q := normalizes_whole Λ hΛ
  have hS₀ : XMod.IsInv ↥Λ (g₀ • V) := XMod.isInv_smul_of_normalizes hN g₀ hVΛ
  set Mθ : Subgroup Γ := typeStab Λ hN hS₀ with hMθ
  set T' : Subgroup Γ := T.map (MulAut.conj g₀).toMonoidHom with hT'
  have hT'M : T' ≤ Mθ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_typeStab]
    have : (MulAut.conj g₀ t) • (g₀ • V) = g₀ • V := by
      show (g₀ * t * g₀⁻¹) • (g₀ • V) = g₀ • V
      rw [mul_smul, mul_smul, inv_smul_smul, hVT t ht]
    rw [show (MulAut.conj g₀).toMonoidHom t = MulAut.conj g₀ t from rfl, this]
    exact XMod.Iso.refl _
  have hT'syl : IsSylowTwoOf T' Mθ := A4.isSylowTwoOf_mono (isSylowTwoOf_top_conj hT g₀) hT'M le_top
  set A₁ : Subgroup Γ := A ⊓ Mθ with hA₁
  have hA₁p : IsPGroup 2 ↥A₁ := hT.2.1.to_le (inf_le_left.trans hAT)
  obtain ⟨S, hSsyl, hA₁S⟩ := A4.exists_isSylowTwoOf_ge (inf_le_right : A₁ ≤ Mθ) hA₁p
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hT'syl hSsyl
  refine ⟨h * g₀, ?_, ?_⟩
  · rw [mul_smul]
    exact (mem_typeStab.1 hh)
  · intro a haA hiso
    have haM : a ∈ Mθ := mem_typeStab.2 hiso
    have haS : a ∈ S := hA₁S ⟨haA, haM⟩
    have h1 : h⁻¹ * a * h ∈ T' := (hconj a).1 haS
    have h2 : g₀⁻¹ * (h⁻¹ * a * h) * g₀ ∈ T := by
      obtain ⟨t, ht, hteq⟩ := h1
      have : g₀⁻¹ * (h⁻¹ * a * h) * g₀ = t := by
        rw [← hteq]
        show g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ = t
        group
      rw [this]
      exact ht
    have h3 : (h * g₀)⁻¹ * a * (h * g₀) ∈ T := by
      have e : (h * g₀)⁻¹ * a * (h * g₀) = g₀⁻¹ * (h⁻¹ * a * h) * g₀ := by group
      rw [e]
      exact h2
    exact h3

theorem smul_translate_eq {T : Subgroup Γ} {V : Subgroup Q} (hVT : ∀ t ∈ T, t • V = V) {a g : Γ}
    (h : g⁻¹ * a * g ∈ T) : a • (g • V) = g • V := by
  have h4 : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  calc a • (g • V) = (g * (g⁻¹ * a * g) * g⁻¹) • (g • V) := by rw [← h4]
    _ = g • ((g⁻¹ * a * g) • V) := by rw [mul_smul, inv_smul_smul, mul_smul]
    _ = g • V := by rw [hVT _ h]

end CFSG.Quasithin.Z391
