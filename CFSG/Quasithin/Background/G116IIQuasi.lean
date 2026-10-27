module

public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.G10FifteenSD

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def conjEquivOfMap {L₁ L₂ : Subgroup (GLV V)} {t : GLV V}
    (h : L₁.map (MulAut.conj t).toMonoidHom = L₂) : ↥L₁ ≃* ↥L₂ :=
  (L₁.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
    (MulEquiv.subgroupCongr h)

theorem quasiEquivalent_restrictRange_of_conj [Finite V] {H L₁ L₂ : Subgroup (GLV V)}
    {I : Submodule (ZMod 2) V} {t : GLV V} (hI : IsIrr H I) (hfH : FaithfulOn H I)
    (hL₁H : L₁ ≤ H) (hL₂H : L₂ ≤ H) (htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    (hmap : L₁.map (MulAut.conj t).toMonoidHom = L₂)
    (hcase : conjSub t I = I ∨ IsDualOf H I (conjSub t I)) :
    ∃ (hL₁ : Invariant L₁ I) (hL₂ : Invariant L₂ I),
      QuasiEquivalent (restrictRange L₁ I hL₁) (restrictRange L₂ I hL₂) := by
  have hL₁ : Invariant L₁ I := hI.1.mono hL₁H
  have hL₂ : Invariant L₂ I := hI.1.mono hL₂H
  have hf₁ : FaithfulOn L₁ I := faithfulOn_of_le hL₁H hfH
  have hf₂ : FaithfulOn L₂ I := faithfulOn_of_le hL₂H hfH
  refine ⟨hL₁, hL₂, ?_⟩
  let φ : ↥(restrictRange L₁ I hL₁) ≃* ↥(restrictRange L₂ I hL₂) :=
    (restrictRangeEquiv hL₁ hf₁).symm.trans
      ((conjEquivOfMap hmap).trans (restrictRangeEquiv hL₂ hf₂))
  have hφ : ∀ l : ↥L₁, φ (restrictRangeEquiv hL₁ hf₁ l) =
      restrictRangeEquiv hL₂ hf₂ (conjEquivOfMap hmap l) := by
    intro l
    simp [φ]
  refine ⟨φ, ?_⟩
  rcases hcase with hti | hdual
  · left
    refine ⟨restrictEquiv t I hti, fun a v => ?_⟩
    obtain ⟨l, rfl⟩ := (restrictRangeEquiv hL₁ hf₁).surjective a
    rw [hφ]
    apply Subtype.ext
    show t ((l : GLV V) (v : V)) = (t * (l : GLV V) * t⁻¹) (t (v : V))
    simp [mul_assoc]
  · right
    obtain ⟨β, hβ1, hβ2, hβinv⟩ := hdual
    let τ : ↥I →ₗ[ZMod 2] ↥(conjSub t I) :=
      (LinearEquiv.ofSubmodules t I (conjSub t I) rfl).toLinearMap
    have hτ : ∀ v : ↥I, ((τ v : ↥(conjSub t I)) : V) = t (v : V) := fun v => rfl
    let ψ₀ : ↥I →ₗ[ZMod 2] (↥I →ₗ[ZMod 2] ZMod 2) := β ∘ₗ τ
    have hinj : Function.Injective ψ₀ := by
      refine (injective_iff_map_eq_zero ψ₀).2 fun v hv => ?_
      have h1 : τ v = 0 := hβ1 _ fun i => by
        have := LinearMap.congr_fun hv i
        exact this
      have h2 : t (v : V) = 0 := by
        have := congrArg Subtype.val h1
        exact this
      apply Subtype.ext
      simpa using h2
    have hcardI : Nat.card ↥I = 2 ^ Module.finrank (ZMod 2) ↥I := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥I)
      rwa [Nat.card_zmod] at this
    have : Finite (↥I →ₗ[ZMod 2] ZMod 2) := finite_dual I
    have hbij : Function.Bijective ψ₀ :=
      hinj.bijective_of_nat_card_le (by rw [hcardI]; exact card_dual_le I)
    let e : ↥I ≃ₗ[ZMod 2] (↥I →ₗ[ZMod 2] ZMod 2) := LinearEquiv.ofBijective ψ₀ hbij
    refine ⟨e, fun a v w => ?_⟩
    obtain ⟨l, rfl⟩ := (restrictRangeEquiv hL₁ hf₁).surjective a
    rw [hφ]
    have hk : t * (l : GLV V) * t⁻¹ ∈ H := htH l (hL₁H l.2)
    have := hβinv (t * (l : GLV V) * t⁻¹) hk (τ v) (τ ((restrictRangeEquiv hL₁ hf₁ l : GLV ↥I) v))
      w ((restrictRangeEquiv hL₂ hf₂ (conjEquivOfMap hmap l) : GLV ↥I) w) ?_ ?_
    · exact this
    · show (t * (l : GLV V) * t⁻¹) (t (v : V)) = t ((l : GLV V) (v : V))
      simp [mul_assoc]
    · rfl

end G11

end CFSG.Quasithin
