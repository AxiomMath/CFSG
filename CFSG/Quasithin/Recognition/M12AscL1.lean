module

public import CFSG.Quasithin.Recognition.M12AscS6c
public import CFSG.Quasithin.Recognition.M12AscY1

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem hom_ext_swapGen {M : Type*} [Monoid M] (f g : Perm (Fin 6) →* M)
    (h : ∀ i : Fin 5, f (swapGen i) = g (swapGen i)) : f = g := by
  ext σ
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swapGen i) := by
    rw [show (fun i : Fin 5 => swapGen i) = fun i : Fin 5 => Equiv.swap i.castSucc i.succ from rfl,
      Equiv.Perm.mclosure_swap_castSucc_succ 5]
    trivial
  exact MonoidHom.eqOn_closureM (by rintro _ ⟨i, rfl⟩; exact h i) hσ

noncomputable def outerAlpha : Perm (Fin 6) →* Perm (Fin 6) :=
  Classical.choose (exists_perm_hom_of_coxeter TA TA_cox.1 TA_cox.2)

theorem outerAlpha_gen (i : Fin 5) : outerAlpha (swapGen i) = TA i :=
  Classical.choose_spec (exists_perm_hom_of_coxeter TA TA_cox.1 TA_cox.2) i

theorem sign_outerAlpha
    (σ : Perm (Fin 6)) : Equiv.Perm.sign (outerAlpha σ) = Equiv.Perm.sign σ := by
  have h : (Equiv.Perm.sign : Perm (Fin 6) →* ℤˣ).comp outerAlpha = Equiv.Perm.sign := by
    apply hom_ext_swapGen
    intro i
    show Equiv.Perm.sign (outerAlpha (swapGen i)) = Equiv.Perm.sign (swapGen i)
    rw [outerAlpha_gen]
    fin_cases i <;> decide +kernel
  exact DFunLike.congr_fun h σ

structure OuterData {m : AscModel z} (c : AscCox m) (y : G) : Prop where
  y_sq : y * y = m.ψ mA
  y_conj : ∀ i : Fin 5, y * c.ρ (swapGen i) * y⁻¹ = c.ρ (TA i)

namespace OuterData

variable {m : AscModel z} {c : AscCox m} {y : G}

theorem conj_rho (h : OuterData c y) (σ : Perm (Fin 6)) :
    y * c.ρ σ * y⁻¹ = c.ρ (outerAlpha σ) := by
  have e : ((MulAut.conj y).toMonoidHom.comp c.ρ : Perm (Fin 6) →* G) =
      c.ρ.comp outerAlpha := by
    apply hom_ext_swapGen
    intro i
    show y * c.ρ (swapGen i) * y⁻¹ = c.ρ (outerAlpha (swapGen i))
    rw [outerAlpha_gen]
    exact h.y_conj i
  exact DFunLike.congr_fun e σ

theorem y_rho
    (h : OuterData c y) (σ : Perm (Fin 6)) : y * c.ρ σ = c.ρ (outerAlpha σ) * y := by
  have := h.conj_rho σ
  calc y * c.ρ σ = (y * c.ρ σ * y⁻¹) * y := by group
    _ = c.ρ (outerAlpha σ) * y := by rw [this]

theorem y_inv (h : OuterData c y) : y⁻¹ = c.ρ pa * y := by
  have h4 : y * y * (y * y) = 1 := by rw [h.y_sq]; exact AscModel.a_sq
  rw [c.ρ_pa, ← h.y_sq]
  calc y⁻¹ = y⁻¹ * (y * y * (y * y)) := by rw [h4, mul_one]
    _ = y * y * y := by group

theorem y_notin
    (h : OuterData c y) (σ : Perm (Fin 6)) : y ≠ c.ρ σ := by
  intro e
  have h1 := h.conj_rho (swap 0 1)
  have h2 : outerAlpha (swap 0 1) = tA1 := outerAlpha_gen 0
  rw [h2, e, ← map_inv, ← map_mul, ← map_mul] at h1
  have := c.ρ_inj h1
  exact (by decide +kernel : ∀ σ : Perm (Fin 6), σ * swap 0 1 * σ⁻¹ ≠ tA1) σ this

theorem rho_ne_rhoy
    (h : OuterData c y) (σ τ : Perm (Fin 6)) : c.ρ σ ≠ c.ρ τ * y := by
  intro e
  apply h.y_notin (τ⁻¹ * σ)
  rw [map_mul, map_inv]
  calc y = (c.ρ τ)⁻¹ * (c.ρ τ * y) := by group
    _ = (c.ρ τ)⁻¹ * c.ρ σ := by rw [← e]

@[expose] def L (h : OuterData c y) : Subgroup G where
  carrier := {g | ∃ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ (g = c.ρ σ ∨ g = c.ρ σ * y)}
  one_mem' := ⟨1, by simp, Or.inl (map_one _).symm⟩
  mul_mem' := by
    rintro _ _ ⟨σ, hσ, rfl | rfl⟩ ⟨τ, hτ, rfl | rfl⟩
    · exact ⟨σ * τ, by rw [map_mul, hσ, hτ]; rfl, Or.inl (map_mul _ _ _).symm⟩
    · refine ⟨σ * τ, by rw [map_mul, hσ, hτ]; rfl, Or.inr ?_⟩
      rw [map_mul, mul_assoc]
    · refine ⟨σ * outerAlpha τ, by rw [map_mul, sign_outerAlpha, hσ, hτ]; rfl, Or.inr ?_⟩
      rw [map_mul, mul_assoc, h.y_rho, ← mul_assoc]
    · refine ⟨σ * outerAlpha τ * pa, ?_, Or.inl ?_⟩
      · rw [map_mul, map_mul, sign_outerAlpha, hσ, hτ]
        have : Equiv.Perm.sign pa = 1 := by decide +kernel
        rw [this]; rfl
      · rw [map_mul, map_mul, c.ρ_pa, ← h.y_sq]
        calc c.ρ σ * y * (c.ρ τ * y) = c.ρ σ * (y * c.ρ τ) * y := by group
          _ = c.ρ σ * (c.ρ (outerAlpha τ) * y) * y := by rw [h.y_rho]
          _ = c.ρ σ * c.ρ (outerAlpha τ) * (y * y) := by group
  inv_mem' := by
    rintro _ ⟨σ, hσ, rfl | rfl⟩
    · exact ⟨σ⁻¹, by rw [map_inv, hσ]; rfl, Or.inl (map_inv _ _).symm⟩
    · refine ⟨pa * outerAlpha σ⁻¹, ?_, Or.inr ?_⟩
      · have : Equiv.Perm.sign pa = 1 := by decide +kernel
        simp [sign_outerAlpha, hσ, this]
      · calc (c.ρ σ * y)⁻¹ = y⁻¹ * (c.ρ σ)⁻¹ := mul_inv_rev _ _
          _ = (c.ρ pa * y) * c.ρ σ⁻¹ := by rw [h.y_inv, ← map_inv]
          _ = c.ρ pa * (y * c.ρ σ⁻¹) := by rw [mul_assoc]
          _ = c.ρ pa * (c.ρ (outerAlpha σ⁻¹) * y) := by rw [h.y_rho]
          _ = c.ρ (pa * outerAlpha σ⁻¹) * y := by rw [map_mul, mul_assoc]

theorem rho_mem_L (h : OuterData c y) (σ : Perm (Fin 6)) :
    c.ρ σ ∈ h.L ↔ Equiv.Perm.sign σ = 1 := by
  constructor
  · rintro ⟨τ, hτ, e | e⟩
    · rw [c.ρ_inj e]; exact hτ
    · exact absurd e (h.rho_ne_rhoy σ τ)
  · intro hσ
    exact ⟨σ, hσ, Or.inl rfl⟩

theorem rhoy_mem_L (h : OuterData c y) (σ : Perm (Fin 6)) :
    c.ρ σ * y ∈ h.L ↔ Equiv.Perm.sign σ = 1 := by
  constructor
  · rintro ⟨τ, hτ, e | e⟩
    · exact absurd e.symm (h.rho_ne_rhoy τ σ)
    · have : c.ρ σ = c.ρ τ := mul_right_cancel e
      rw [c.ρ_inj this]; exact hτ
  · intro hσ
    exact ⟨σ, hσ, Or.inr rfl⟩

theorem z_notin_L (h : OuterData c y) : z ∉ h.L := by
  intro hz'
  have hz2 : c.ρ (swap 0 1) ∈ h.L := by rw [c.ρ_z]; exact hz'
  rw [rho_mem_L] at hz2
  rw [Equiv.Perm.sign_swap (by decide)] at hz2
  exact absurd hz2 (by decide)

theorem z_normalizes_L
    (h : OuterData c y) {l : G} (hl : l ∈ h.L) : z * l * z⁻¹ ∈ h.L := by
  have hz : c.ρ (swap 0 1) = z := c.ρ_z
  have hs : Equiv.Perm.sign (swap (0 : Fin 6) 1) = -1 := Equiv.Perm.sign_swap (by decide)
  obtain ⟨σ, hσ, rfl | rfl⟩ := hl
  · have e : z * c.ρ σ * z⁻¹ = c.ρ (swap 0 1 * σ * (swap 0 1)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hz]
    rw [e, rho_mem_L]
    simp [hσ]
  · have e : z * (c.ρ σ * y) * z⁻¹ = c.ρ (swap 0 1 * σ * (outerAlpha (swap 0 1))⁻¹) * y := by
      calc z * (c.ρ σ * y) * z⁻¹
          = c.ρ (swap 0 1) * (c.ρ σ * y) * (c.ρ (swap 0 1))⁻¹ := by rw [hz]
        _ = c.ρ (swap 0 1) * c.ρ σ * (y * (c.ρ (swap 0 1))⁻¹) := by group
        _ = c.ρ (swap 0 1) * c.ρ σ * (y * c.ρ (swap 0 1)⁻¹) := by rw [map_inv]
        _ = c.ρ (swap 0 1) * c.ρ σ * (c.ρ (outerAlpha (swap 0 1)⁻¹) * y) := by
          rw [h.y_rho]
        _ = c.ρ (swap 0 1 * σ * (outerAlpha (swap 0 1))⁻¹) * y := by
          rw [map_inv, map_mul, map_mul]
          group
    rw [e, rhoy_mem_L]
    simp [sign_outerAlpha, hσ, hs]

theorem L_card (h : OuterData c y) : Nat.card h.L = 720 := by
  have hA : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1} = 360 := by
    have : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1} =
        Nat.card ↥(alternatingGroup (Fin 6)) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun σ => by
        rw [Equiv.Perm.mem_alternatingGroup]))
    rw [this, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  let f : ({σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1} × Bool) → ↥h.L := fun p =>
    ⟨if p.2 then c.ρ p.1 * y else c.ρ p.1, p.1, p.1.2, by
      cases p.2 <;> simp⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨σ, hσ⟩, b⟩ ⟨⟨τ, hτ⟩, b'⟩ e
      have e' := congrArg Subtype.val e
      simp only [f] at e'
      cases b <;> cases b' <;> simp at e'
      · have := c.ρ_inj e'
        subst this
        rfl
      · exact absurd e' (h.rho_ne_rhoy σ τ)
      · exact absurd e'.symm (h.rho_ne_rhoy τ σ)
      · have := c.ρ_inj e'
        subst this
        rfl
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ, rfl | rfl⟩ := hg
      · exact ⟨(⟨σ, hσ⟩, false), rfl⟩
      · exact ⟨(⟨σ, hσ⟩, true), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, hA]
  simp

end OuterData

end CFSG.Quasithin
