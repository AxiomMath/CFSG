module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinI
public import CFSG.Quasithin.EmptyFaithful.S146zNFinR

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

theorem closure_x0y0A6 : Subgroup.closure ({x0A6, y0A6} : Set A6) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g.1 ∈ Subgroup.closure ({x0P, y0P} : Set (Perm (Fin 6))) :=
    alternatingGroup_le_closure g.2
  have hmap : (Subgroup.closure ({x0A6, y0A6} : Set A6)).map (alternatingGroup (Fin 6)).subtype =
      Subgroup.closure ({x0P, y0P} : Set (Perm (Fin 6))) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [x0A6, y0A6]
  rw [← hmap] at hg
  obtain ⟨k, hk, hk'⟩ := hg
  have : k = g := Subtype.ext hk'
  rw [← this]
  exact hk

section Kap

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

noncomputable def kapFun (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) (g : A6) : A6 :=
  Classical.choose (hn g)

omit [Finite W] in
theorem kapFun_spec (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) (g : A6) :
    ρ (kapFun n hn g) = n * ρ g * n⁻¹ := Classical.choose_spec (hn g)

omit [Finite W] in
theorem kapFun_mul (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹)
    (a b : A6) : kapFun n hn (a * b) = kapFun n hn a * kapFun n hn b := by
  apply h.inj
  rw [map_mul, kapFun_spec, kapFun_spec, kapFun_spec, map_mul]
  group

noncomputable def kap (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) :
    A6 →* A6 :=
  MonoidHom.mk' (kapFun n hn) (kapFun_mul h n hn)

omit [Finite W] in
theorem kap_spec (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) (g : A6) :
    ρ (kap h n hn g) = n * ρ g * n⁻¹ := kapFun_spec n hn g

omit [Finite W] in
theorem kap_ne_one (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹)
    {g : A6} (hg : g ≠ 1) : kap h n hn g ≠ 1 := by
  intro h1
  apply hg
  apply h.inj
  have := kap_spec h n hn g
  rw [h1, map_one] at this
  rw [map_one]
  have h2 : n * ρ g * n⁻¹ = 1 := this.symm
  calc ρ g = n⁻¹ * (n * ρ g * n⁻¹) * n := by group
    _ = 1 := by rw [h2]; group

theorem kap_isT (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹)
    {z : A6} (hz : IsT z) : IsT (kap h n hn z) := by
  obtain ⟨hz3, hz1, hzf⟩ := hz
  have h3 : (kap h n hn z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have h1 := kap_ne_one h n hn hz1
  refine ⟨h3, h1, ?_⟩
  by_contra hno
  push Not at hno
  have hfc : fc ρ (kap h n hn z) = fc ρ z := by
    unfold fc
    rw [kap_spec h n hn z]
    exact card_fixSub_conj n (ρ z)
  rw [fc_U _ ⟨h3, h1, hno⟩, fc_T z ⟨hz3, hz1, hzf⟩] at hfc
  have hF := F2_16 ρ h.nontrivial h.card
  omega


end Kap

@[expose] def z0A6 : A6 := x0A6 * y0A6 * x0A6 * (y0A6 * y0A6 * y0A6) * x0A6 * y0A6 * y0A6

theorem z0A6_val : z0A6.1 = w3 x0P y0P := rfl

theorem z0A6_isT : IsT z0A6 := by
  obtain ⟨h3, h1, hf⟩ := w3_x0y0
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa [z0A6_val, pow_succ, mul_assoc] using h3
  · intro h
    exact h1 (by rw [← z0A6_val, h]; rfl)
  · obtain ⟨i, hi⟩ := hf
    exact ⟨i, by rw [z0A6_val]; exact hi⟩

section Kap2

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem Setup.kap_conj (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹) :
    ∃ σ : Perm (Fin 6), ∀ g : A6, ((kap h n hn g : A6) : Perm (Fin 6)) = σ * g.1 * σ⁻¹ := by
  set κ := kap h n hn with hκ
  have hrel := rel_x0y0
  have y4 : y0A6 * y0A6 * y0A6 * y0A6 = 1 := Subtype.ext hrel.2.1
  have r5 : (x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6) = 1 :=
    Subtype.ext hrel.2.2.1
  have r5' : (x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6)) *
      (x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6)) = 1 := Subtype.ext hrel.2.2.2
  have k4 : κ y0A6 * κ y0A6 * κ y0A6 * κ y0A6 = 1 := by
    calc _ = κ (y0A6 * y0A6 * y0A6 * y0A6) := by simp only [map_mul]
      _ = 1 := by rw [y4, map_one]
  have k5 : (κ x0A6 * κ y0A6) * (κ x0A6 * κ y0A6) * (κ x0A6 * κ y0A6) * (κ x0A6 * κ y0A6) *
      (κ x0A6 * κ y0A6) = 1 := by
    calc _ = κ ((x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6) * (x0A6 * y0A6)) := by
          simp only [map_mul]
      _ = 1 := by rw [r5, map_one]
  have k5' : (κ x0A6 * (κ y0A6 * κ y0A6)) * (κ x0A6 * (κ y0A6 * κ y0A6)) *
      (κ x0A6 * (κ y0A6 * κ y0A6)) * (κ x0A6 * (κ y0A6 * κ y0A6)) *
      (κ x0A6 * (κ y0A6 * κ y0A6)) = 1 := by
    calc _ = κ ((x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6)) *
          (x0A6 * (y0A6 * y0A6)) * (x0A6 * (y0A6 * y0A6))) := by simp only [map_mul]
      _ = 1 := by rw [r5', map_one]
  have k2 : κ x0A6 * κ x0A6 = 1 := by rw [← map_mul, x0A6_sq, map_one]
  have hT := kap_isT h n hn z0A6_isT
  have hw : (κ z0A6).1 = w3 (κ x0A6).1 (κ y0A6).1 := by
    show (κ (x0A6 * y0A6 * x0A6 * (y0A6 * y0A6 * y0A6) * x0A6 * y0A6 * y0A6)).1 = _
    simp only [map_mul, w3]
    rfl
  obtain ⟨hT3, hT1, hTf⟩ := hT
  have hp1 : (κ x0A6).1 ≠ 1 := fun e => kap_ne_one h n hn x0A6_ne_one (Subtype.ext e)
  obtain ⟨σ, hσx, hσy⟩ := pairs_conj (κ x0A6).1 (κ y0A6).1 (mem_alternatingGroup.mp (κ x0A6).2) hp1
    (by simpa using congrArg Subtype.val k2) (mem_alternatingGroup.mp (κ y0A6).2)
    (by simpa using congrArg Subtype.val k4) (by simpa using congrArg Subtype.val k5)
    (by simpa using congrArg Subtype.val k5')
    (by rw [← hw]; simpa [pow_succ, mul_assoc] using congrArg Subtype.val hT3)
    (by rw [← hw]; intro e; exact hT1 (Subtype.ext e))
    (by rw [← hw]; exact hTf)
  refine ⟨σ, ?_⟩
  let E : Subgroup A6 :=
    { carrier := {g | ((κ g : A6) : Perm (Fin 6)) = σ * g.1 * σ⁻¹}
      mul_mem' := fun {a b} ha hb => by
        show ((κ (a * b) : A6) : Perm (Fin 6)) = σ * (a * b).1 * σ⁻¹
        have ha' : ((κ a : A6) : Perm (Fin 6)) = σ * a.1 * σ⁻¹ := ha
        have hb' : ((κ b : A6) : Perm (Fin 6)) = σ * b.1 * σ⁻¹ := hb
        rw [map_mul]
        show ((κ a : A6) : Perm (Fin 6)) * ((κ b : A6) : Perm (Fin 6)) = _
        rw [ha', hb']
        show _ = σ * (a.1 * b.1) * σ⁻¹
        group
      one_mem' := by
        show ((κ 1 : A6) : Perm (Fin 6)) = σ * (1 : A6).1 * σ⁻¹
        rw [map_one]
        show (1 : Perm (Fin 6)) = σ * 1 * σ⁻¹
        group
      inv_mem' := fun {a} ha => by
        show ((κ a⁻¹ : A6) : Perm (Fin 6)) = σ * (a⁻¹).1 * σ⁻¹
        have ha' : ((κ a : A6) : Perm (Fin 6)) = σ * a.1 * σ⁻¹ := ha
        rw [map_inv]
        show ((κ a : A6) : Perm (Fin 6))⁻¹ = σ * a.1⁻¹ * σ⁻¹
        rw [ha']
        group }
  have hgens : ({x0A6, y0A6} : Set A6) ⊆ E := by
    intro g hg
    rcases hg with rfl | rfl
    · show ((κ x0A6 : A6) : Perm (Fin 6)) = σ * x0P * σ⁻¹
      rw [hσx]
      group
    · show ((κ y0A6 : A6) : Perm (Fin 6)) = σ * y0P * σ⁻¹
      rw [hσy]
      group
  intro g
  have : g ∈ E := by
    have := Subgroup.closure_le E |>.mpr hgens
    rw [closure_x0y0A6] at this
    exact this (Subgroup.mem_top g)
  exact this

end Kap2

end CFSG.Quasithin.A6Fin
