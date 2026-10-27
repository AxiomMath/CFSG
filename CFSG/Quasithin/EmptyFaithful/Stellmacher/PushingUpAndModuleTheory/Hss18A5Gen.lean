module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Klein

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

private theorem swap01_normalizes' : ∀ y : Perm (Fin 5),
    swap 0 1 * y * swap 0 1 ∈ S5TF → y ∈ S5TF := by
  unfold S5TF
  decide +kernel

theorem map_conj_swap01_S5T : S5T.map (MulAut.conj (swap (0 : Fin 5) 1)).toMonoidHom = S5T := by
  have hc : Nat.card (S5T.map (MulAut.conj (swap (0 : Fin 5) 1)).toMonoidHom) = Nat.card S5T :=
    Subgroup.card_map_of_injective (MulAut.conj _).injective
  refine Subgroup.eq_of_le_of_card_ge ?_ hc.ge
  intro y hy
  rw [mem_map_conj, mem_S5T_iff] at hy
  rw [mem_S5T_iff]
  have : (swap (0 : Fin 5) 1)⁻¹ = swap 0 1 := by simp
  rw [this] at hy
  exact swap01_normalizes' y hy

theorem map_conj_conj {G : Type*} [Group G] (B : Subgroup G) (g h : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      B.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_even_conj_S5T {B : Subgroup (Perm (Fin 5))} (hBA : B ≤ alternatingGroup (Fin 5))
    (hexp : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 4) :
    ∃ g : Perm (Fin 5), Perm.sign g = 1 ∧ B.map (MulAut.conj g).toMonoidHom = S5T := by
  obtain ⟨g, hg⟩ := exists_conj_le_syl hexp
  have hle : B.map (MulAut.conj g).toMonoidHom ≤ S5T := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨hg ⟨b, hb, rfl⟩, Perm.mem_alternatingGroup.mpr ?_⟩
    have := Perm.mem_alternatingGroup.mp (hBA hb)
    show Perm.sign (g * b * g⁻¹) = 1
    rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign g) (Perm.sign b), mul_assoc,
      mul_inv_cancel, mul_one, this]
  have hceq : Nat.card (B.map (MulAut.conj g).toMonoidHom) = Nat.card S5T := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, card_S5T_eq_four]
  have heq := Subgroup.eq_of_le_of_card_ge hle hceq.ge
  by_cases hs : Perm.sign g = 1
  · exact ⟨g, hs, heq⟩
  · refine ⟨swap 0 1 * g, ?_, ?_⟩
    · rw [map_mul, Perm.sign_swap (by decide)]
      rcases Int.units_eq_one_or (Perm.sign g) with h | h
      · exact absurd h hs
      · rw [h]; decide
    · rw [← map_conj_conj, heq, map_conj_swap01_S5T]

private theorem alt5_le_S5T_sup_even :
    alternatingGroup (Fin 5) ≤
      S5T ⊔ S5T.map (MulAut.conj (swap (3 : Fin 5) 4 * swap 0 1)).toMonoidHom := by
  have h := alt5_le_syl_sup
  have e : S5T.map (MulAut.conj (swap (3 : Fin 5) 4 * swap 0 1)).toMonoidHom =
      S5T.map (MulAut.conj conjT34).toMonoidHom := by
    rw [← map_conj_conj, map_conj_swap01_S5T]
    rfl
  rw [e]
  exact h

theorem exists_alt_gen {B : Subgroup (Perm (Fin 5))} (hBA : B ≤ alternatingGroup (Fin 5))
    (hexp : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 4) :
    ∃ h ∈ alternatingGroup (Fin 5),
      alternatingGroup (Fin 5) ≤ B ⊔ B.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨g, hgs, hg⟩ := exists_even_conj_S5T hBA hexp hcard
  set h₀ : Perm (Fin 5) := swap 3 4 * swap 0 1 with hh₀
  have hh₀A : h₀ ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, hh₀]; decide
  have hgA : g ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr hgs
  refine ⟨g⁻¹ * h₀ * g, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgA) hh₀A) hgA
  · have hB : B = S5T.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← hg, Subgroup.map_map]
      have : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = MonoidHom.id _ := by
        ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    have hB2 : B.map (MulAut.conj (g⁻¹ * h₀ * g)).toMonoidHom =
        (S5T.map (MulAut.conj h₀).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hB, map_conj_conj, map_conj_conj]
      have : g⁻¹ * h₀ * g * g⁻¹ = g⁻¹ * h₀ := by group
      rw [this]
    rw [hB2, hB, ← Subgroup.map_sup]
    intro σ hσ
    refine ⟨g * σ * g⁻¹, alt5_le_S5T_sup_even ?_, ?_⟩
    · exact (alternatingGroup.normal (α := Fin 5)).conj_mem σ hσ g
    · simp [mul_assoc]

section Module

variable {W : Type} [CommGroup W] (ρ : ↥(alternatingGroup (Fin 5)) →* MulAut W)

@[expose] def stabA5 (w : W) : Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ h : σ ∈ alternatingGroup (Fin 5), ρ ⟨σ, h⟩ w = w}
  one_mem' := ⟨Subgroup.one_mem _, by
    have : (⟨1, Subgroup.one_mem _⟩ : ↥(alternatingGroup (Fin 5))) = 1 := rfl
    rw [this, map_one]; rfl⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, h1⟩ ⟨hτ, h2⟩
    refine ⟨Subgroup.mul_mem _ hσ hτ, ?_⟩
    have : (⟨σ * τ, Subgroup.mul_mem _ hσ hτ⟩ : ↥(alternatingGroup (Fin 5))) =
        ⟨σ, hσ⟩ * ⟨τ, hτ⟩ := rfl
    rw [this, map_mul, MulAut.mul_apply, h2, h1]
  inv_mem' := by
    rintro σ ⟨hσ, h1⟩
    refine ⟨Subgroup.inv_mem _ hσ, ?_⟩
    have h3 : ρ ⟨σ⁻¹, Subgroup.inv_mem _ hσ⟩ (ρ ⟨σ, hσ⟩ w) = w := by
      rw [← MulAut.mul_apply, ← map_mul]
      have : (⟨σ⁻¹, Subgroup.inv_mem _ hσ⟩ * ⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) = 1 :=
        Subtype.ext (inv_mul_cancel σ)
      rw [this, map_one]; rfl
    rw [h1] at h3
    exact h3

@[expose] def fixA5 (B : Subgroup (Perm (Fin 5))) : Subgroup W where
  carrier := {w | ∀ b (_ : b ∈ B) (h : b ∈ alternatingGroup (Fin 5)), ρ ⟨b, h⟩ w = w}
  one_mem' := fun b _ h => map_one _
  mul_mem' := fun {x y} hx hy b hb h => by rw [map_mul, hx b hb h, hy b hb h]
  inv_mem' := fun {x} hx b hb h => by rw [map_inv, hx b hb h]

theorem mem_fixA5_iff {B : Subgroup (Perm (Fin 5))} (hB : B ≤ alternatingGroup (Fin 5)) {w : W} :
    w ∈ fixA5 ρ B ↔ B ≤ stabA5 ρ w :=
  ⟨fun h b hb => ⟨hB hb, h b hb (hB hb)⟩, fun h b hb hA => by
    obtain ⟨hA', h'⟩ := h hb
    exact h'⟩

theorem fixA5_sup {B C : Subgroup (Perm (Fin 5))} (hB : B ≤ alternatingGroup (Fin 5))
    (hC : C ≤ alternatingGroup (Fin 5)) : fixA5 ρ (B ⊔ C) = fixA5 ρ B ⊓ fixA5 ρ C := by
  ext w
  rw [Subgroup.mem_inf, mem_fixA5_iff ρ (sup_le hB hC), mem_fixA5_iff ρ hB, mem_fixA5_iff ρ hC,
    sup_le_iff]

theorem index_fixA5_conj {B : Subgroup (Perm (Fin 5))} (hB : B ≤ alternatingGroup (Fin 5))
    {h : Perm (Fin 5)} (hh : h ∈ alternatingGroup (Fin 5)) :
    (fixA5 ρ (B.map (MulAut.conj h).toMonoidHom)).index = (fixA5 ρ B).index := by
  set φ : W ≃* W := ρ ⟨h, hh⟩ with hφ
  have key : fixA5 ρ (B.map (MulAut.conj h).toMonoidHom) = (fixA5 ρ B).map φ.toMonoidHom := by
    ext w
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hw b hb hbA
      have hb' : h * b * h⁻¹ ∈ B.map (MulAut.conj h).toMonoidHom := ⟨b, hb, rfl⟩
      have hA' : h * b * h⁻¹ ∈ alternatingGroup (Fin 5) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hbA) (Subgroup.inv_mem _ hh)
      have h1 := hw _ hb' hA'
      have e : (⟨h * b * h⁻¹, hA'⟩ : ↥(alternatingGroup (Fin 5))) =
          ⟨h, hh⟩ * ⟨b, hbA⟩ * ⟨h, hh⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv] at h1
      have h2 : φ (ρ ⟨b, hbA⟩ (φ.symm w)) = w := by
        have : (ρ ⟨h, hh⟩)⁻¹ w = φ.symm w := rfl
        rw [← this] at *
        simpa [MulAut.mul_apply] using h1
      have h3 : ρ ⟨b, hbA⟩ (φ.symm w) = φ.symm w := by
        apply φ.injective
        rw [h2, MulEquiv.apply_symm_apply]
      exact h3
    · intro hw b' hb' hA'
      obtain ⟨b, hb, rfl⟩ := hb'
      have hbA : b ∈ alternatingGroup (Fin 5) := hB hb
      have e : (⟨h * b * h⁻¹, hA'⟩ : ↥(alternatingGroup (Fin 5))) =
          ⟨h, hh⟩ * ⟨b, hbA⟩ * ⟨h, hh⟩⁻¹ := rfl
      have h4 := hw b hb hbA
      show ρ ⟨h * b * h⁻¹, hA'⟩ w = w
      rw [e, map_mul, map_mul, map_inv]
      have : (ρ ⟨h, hh⟩)⁻¹ w = φ.symm w := rfl
      simp only [MulAut.mul_apply]
      rw [this, h4]
      exact φ.apply_symm_apply w
  rw [key]
  exact Subgroup.index_map_equiv _ φ

theorem card_le_index_fixA5_sq [Finite W]
    (hfree : ∀ w : W, (∀ a (ha : a ∈ alternatingGroup (Fin 5)), ρ ⟨a, ha⟩ w = w) → w = 1)
    {B : Subgroup (Perm (Fin 5))} (hBA : B ≤ alternatingGroup (Fin 5))
    (hexp : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 4) :
    Nat.card W ≤ (fixA5 ρ B).index ^ 2 := by
  obtain ⟨h, hh, hgen⟩ := exists_alt_gen hBA hexp hcard
  have hB2 : B.map (MulAut.conj h).toMonoidHom ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (alternatingGroup.normal (α := Fin 5)).conj_mem b (hBA hb) h
  have hsup : B ⊔ B.map (MulAut.conj h).toMonoidHom = alternatingGroup (Fin 5) :=
    le_antisymm (sup_le hBA hB2) hgen
  have h0 : fixA5 ρ (B ⊔ B.map (MulAut.conj h).toMonoidHom) = ⊥ := by
    rw [hsup, eq_bot_iff]
    intro w hw
    exact hfree w fun a ha => hw a ha ha
  have h1 := Subgroup.index_inf_le (H := fixA5 ρ B) (K := fixA5 ρ (B.map (MulAut.conj h).toMonoidHom))
  rw [← fixA5_sup ρ hBA hB2, h0, Subgroup.index_bot, index_fixA5_conj ρ hBA hh, ← sq] at h1
  exact h1

end Module

end CFSG.Quasithin.F53Mod
