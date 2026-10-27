module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.FLc2VModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem card_mul_card_le_inf [Finite V] (U₀ C : Subgroup V) :
    Nat.card U₀ * Nat.card C ≤ Nat.card V * Nat.card ↥(C ⊓ U₀) := by
  have h1 : C.relIndex U₀ * Nat.card ↥(C ⊓ U₀) = Nat.card U₀ := Subgroup.relIndex_mul_card C U₀
  have h2 : C.relIndex U₀ ∣ C.index := Subgroup.relIndex_dvd_index_of_normal C U₀
  have h3 : Nat.card C * C.index = Nat.card V := Subgroup.card_mul_index C
  have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : C.relIndex U₀ ≤ C.index := Nat.le_of_dvd hpos h2
  calc Nat.card U₀ * Nat.card C = C.relIndex U₀ * Nat.card ↥(C ⊓ U₀) * Nat.card C := by rw [h1]
    _ ≤ C.index * Nat.card ↥(C ⊓ U₀) * Nat.card C := by gcongr
    _ = (Nat.card C * C.index) * Nat.card ↥(C ⊓ U₀) := by ring
    _ = Nat.card V * Nat.card ↥(C ⊓ U₀) := by rw [h3]

namespace VModel

variable {n : ℕ} {ρ : SLt n →* MulAut V} {U' Z' : Subgroup V} {X : Type} [CommGroup X]
  {act : SLt n → X → X} (D : VModel n ρ U' Z' X act)

include D

theorem β_fixed (A : Subgroup (SLt n)) {u : ↥U'} (hu : (u : V) ∈ fixV (A.map ρ)) :
    ∀ g ∈ A, act g (D.β u) = D.β u := by
  intro g hg
  have hfix : (ρ g) (u : V) = u := hu (ρ g) ⟨g, hg, rfl⟩
  have h1 := D.equiv g u (D.inv g u u.2)
  have e : (⟨(ρ g) (u : V), D.inv g u u.2⟩ : ↥U') = u := Subtype.ext hfix
  rw [e] at h1
  exact h1.symm

theorem card_U' : Nat.card ↥U' = Nat.card D.β.ker * Nat.card X := by
  exact (Subgroup.card_ker_mul_card_of_surjective D.surj).symm

theorem card_inf_le [Finite V] (A : Subgroup (SLt n)) [Finite X] :
    Nat.card ↥(fixV (A.map ρ) ⊓ U') ≤
      Nat.card D.β.ker * Nat.card {x : X | ∀ g ∈ A, act g x = x} := by
  let φ : ↥(fixV (A.map ρ) ⊓ U') →* X := D.β.comp (Subgroup.inclusion inf_le_right)
  have h := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ Nat.card D.β.ker := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨Subgroup.inclusion inf_le_right x.1, x.2⟩ : ↥D.β.ker)) ?_
    intro x y hxy
    have := congrArg (fun z : ↥D.β.ker => ((z : ↥U') : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card φ.range ≤ Nat.card {x : X | ∀ g ∈ A, act g x = x} := by
    refine Nat.card_mono (Set.toFinite _) ?_
    rintro _ ⟨u, rfl⟩
    exact D.β_fixed A u.2.1
  calc Nat.card ↥(fixV (A.map ρ) ⊓ U') = Nat.card φ.ker * Nat.card φ.range := h.symm
    _ ≤ Nat.card D.β.ker * Nat.card {x : X | ∀ g ∈ A, act g x = x} := Nat.mul_le_mul hker hrange

end VModel

variable [Finite V]

theorem card_fix_transfer {n : ℕ} {ρ : SLt n →* MulAut V} {U' Z' : Subgroup V} {X : Type} [CommGroup X]
    {act : SLt n → X → X} (D : VModel n ρ U' Z' X act) (A : Subgroup (SLt n)) :
    Nat.card X * Nat.card (fixV (A.map ρ)) ≤
      Nat.card V * Nat.card {x : X | ∀ g ∈ A, act g x = x} := by
  have : Finite X := Finite.of_surjective D.β D.surj
  have h0 := card_mul_card_le_inf U' (fixV (A.map ρ))
  have h1 := D.card_inf_le A
  have h2 := D.card_U'
  have hK : 0 < Nat.card D.β.ker := Nat.card_pos
  rw [inf_comm] at h0
  have h3 : Nat.card D.β.ker * (Nat.card X * Nat.card (fixV (A.map ρ))) ≤
      Nat.card D.β.ker * (Nat.card V * Nat.card {x : X | ∀ g ∈ A, act g x = x}) := by
    calc Nat.card D.β.ker * (Nat.card X * Nat.card (fixV (A.map ρ)))
        = (Nat.card D.β.ker * Nat.card X) * Nat.card (fixV (A.map ρ)) := by ring
      _ = Nat.card ↥U' * Nat.card (fixV (A.map ρ)) := by rw [h2]
      _ ≤ Nat.card V * Nat.card ↥(U' ⊓ fixV (A.map ρ)) := h0
      _ ≤ Nat.card V * (Nat.card D.β.ker * Nat.card {x : X | ∀ g ∈ A, act g x = x}) := by
        rw [inf_comm]
        exact Nat.mul_le_mul_left _ h1
      _ = Nat.card D.β.ker * (Nat.card V * Nat.card {x : X | ∀ g ∈ A, act g x = x}) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hK

theorem card_fix_transfer₂ {n : ℕ} {ρ : SLt n →* MulAut V} {U₁ Z₁ U₂ Z₂ : Subgroup V} {X₁ X₂ : Type}
    [CommGroup X₁] [CommGroup X₂] {act₁ : SLt n → X₁ → X₁} {act₂ : SLt n → X₂ → X₂}
    (D₁ : VModel n ρ U₁ Z₁ X₁ act₁) (D₂ : VModel n ρ U₂ Z₂ X₂ act₂) (hdisj : U₁ ⊓ U₂ = ⊥)
    (A : Subgroup (SLt n)) :
    Nat.card X₁ * Nat.card X₂ * Nat.card (fixV (A.map ρ)) ≤
      Nat.card V * (Nat.card {x : X₁ | ∀ g ∈ A, act₁ g x = x} *
        Nat.card {x : X₂ | ∀ g ∈ A, act₂ g x = x}) := by
  have : Finite X₁ := Finite.of_surjective D₁.β D₁.surj
  have : Finite X₂ := Finite.of_surjective D₂.β D₂.surj
  set C : Subgroup V := fixV (A.map ρ) with hC
  let Ψ : ↥U₁ × ↥U₂ →* V := (U₁.subtype).coprod (U₂.subtype)
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have h1 : (a : V) * (b : V) = 1 := hab
    have h2 : (a : V) = (b : V)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a : V) ∈ U₁ ⊓ U₂ := ⟨a.2, by rw [h2]; exact U₂.inv_mem b.2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : (b : V) = 1 := by
      rw [h3, one_mul] at h1
      exact h1
    show (a, b) = (1, 1)
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hRcard : Nat.card Ψ.range = Nat.card ↥U₁ * Nat.card ↥U₂ := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv).symm
  have hsurj : Function.Surjective
      (fun p : ↥(C ⊓ U₁) × ↥(C ⊓ U₂) => (⟨(p.1 : V) * (p.2 : V), by
        refine ⟨C.mul_mem p.1.2.1 p.2.2.1, ⟨(⟨p.1, p.1.2.2⟩, ⟨p.2, p.2.2.2⟩), rfl⟩⟩⟩ : ↥(C ⊓ Ψ.range))) := by
    rintro ⟨v, hvC, ⟨⟨a, b⟩, rfl⟩⟩
    have hfix : ∀ g ∈ A, (ρ g) ((a : V) * (b : V)) = (a : V) * (b : V) :=
      fun g hg => hvC (ρ g) ⟨g, hg, rfl⟩
    have hfa : ∀ g ∈ A, (ρ g) (a : V) = (a : V) ∧ (ρ g) (b : V) = (b : V) := by
      intro g hg
      have e := hfix g hg
      rw [map_mul] at e
      have hga : (ρ g) (a : V) ∈ U₁ := D₁.inv g a a.2
      have hgb : (ρ g) (b : V) ∈ U₂ := D₂.inv g b b.2
      have h1 : (ρ g) (a : V) * (a : V)⁻¹ = (b : V) * ((ρ g) (b : V))⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, e, mul_comm]
      have hmem : (ρ g) (a : V) * (a : V)⁻¹ ∈ U₁ ⊓ U₂ :=
        ⟨U₁.mul_mem hga (U₁.inv_mem a.2), by rw [h1]; exact U₂.mul_mem b.2 (U₂.inv_mem hgb)⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      have ha : (ρ g) (a : V) = (a : V) := mul_inv_eq_one.mp hmem
      refine ⟨ha, ?_⟩
      rw [ha] at e
      exact mul_left_cancel e
    refine ⟨(⟨a, fun x hx => ?_, a.2⟩, ⟨b, fun x hx => ?_, b.2⟩), rfl⟩
    · obtain ⟨g, hg, rfl⟩ := hx
      exact (hfa g hg).1
    · obtain ⟨g, hg, rfl⟩ := hx
      exact (hfa g hg).2
  have hle : Nat.card ↥(C ⊓ Ψ.range) ≤ Nat.card ↥(C ⊓ U₁) * Nat.card ↥(C ⊓ U₂) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective _ hsurj
  have h0 := card_mul_card_le_inf Ψ.range C
  have h1 := D₁.card_inf_le A
  have h2 := D₂.card_inf_le A
  have h1' : Nat.card ↥(C ⊓ U₁) ≤ Nat.card D₁.β.ker * Nat.card {x : X₁ | ∀ g ∈ A, act₁ g x = x} := h1
  have h2' : Nat.card ↥(C ⊓ U₂) ≤ Nat.card D₂.β.ker * Nat.card {x : X₂ | ∀ g ∈ A, act₂ g x = x} := h2
  have hK : 0 < Nat.card D₁.β.ker * Nat.card D₂.β.ker := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h3 : (Nat.card D₁.β.ker * Nat.card D₂.β.ker) * (Nat.card X₁ * Nat.card X₂ * Nat.card C) ≤
      (Nat.card D₁.β.ker * Nat.card D₂.β.ker) *
        (Nat.card V * (Nat.card {x : X₁ | ∀ g ∈ A, act₁ g x = x} *
          Nat.card {x : X₂ | ∀ g ∈ A, act₂ g x = x})) := by
    calc (Nat.card D₁.β.ker * Nat.card D₂.β.ker) * (Nat.card X₁ * Nat.card X₂ * Nat.card C)
        = ((Nat.card D₁.β.ker * Nat.card X₁) * (Nat.card D₂.β.ker * Nat.card X₂)) * Nat.card C := by ring
      _ = (Nat.card ↥U₁ * Nat.card ↥U₂) * Nat.card C := by rw [D₁.card_U', D₂.card_U']
      _ = Nat.card Ψ.range * Nat.card C := by rw [hRcard]
      _ ≤ Nat.card V * Nat.card ↥(C ⊓ Ψ.range) := h0
      _ ≤ Nat.card V * (Nat.card ↥(C ⊓ U₁) * Nat.card ↥(C ⊓ U₂)) := Nat.mul_le_mul_left _ hle
      _ ≤ Nat.card V * ((Nat.card D₁.β.ker * Nat.card {x : X₁ | ∀ g ∈ A, act₁ g x = x}) *
            (Nat.card D₂.β.ker * Nat.card {x : X₂ | ∀ g ∈ A, act₂ g x = x})) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h1' h2')
      _ = (Nat.card D₁.β.ker * Nat.card D₂.β.ker) *
        (Nat.card V * (Nat.card {x : X₁ | ∀ g ∈ A, act₁ g x = x} *
          Nat.card {x : X₂ | ∀ g ∈ A, act₂ g x = x})) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hK

end CFSG.Quasithin.FLc
