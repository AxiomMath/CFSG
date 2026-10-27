module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassificationCheck

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

@[expose] def offsF (i : ℕ) : ℕ := [0, 1, 5, 6, 10, 11, 15].getD i 15

@[expose] def Xf (i : ℕ) : Model 5 :=
  if i = 1 ∨ i = 5 then nat else if i = 3 then orth else triv

theorem series_inv : ∀ i ≤ 6, Pm.InvSub (Qd (offsF i)) := by
  intro i hi
  interval_cases i
  · show Pm.InvSub (Qd 0)
    rw [Qd_zero]
    intro σ x _
    trivial
  · exact Qd_inv (d := 1) (hR_gens (by decide))
  · exact Qd_inv (d := 5) (hR_gens (by decide))
  · exact Qd_inv (d := 6) (hR_gens (by decide))
  · exact Qd_inv (d := 10) (hR_gens (by decide))
  · exact Qd_inv (d := 11) (hR_gens (by decide))
  · exact Qd_inv (d := 15) (fun _ _ _ k _ hk => absurd k.isLt (by omega))

theorem series_step : ∀ i < 6, Step Pm (Qd (offsF i)) (Qd (offsF (i + 1))) (Xf i) := by
  intro i hi
  interval_cases i
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

theorem exists_frob (M : Model 5) (hirr : M.IsIrred) :
    ∃ φ : Pm.W →* M.W, (∀ σ x, φ (Pm.act σ x) = M.act σ (φ x)) ∧ ∀ y, ∃ x, φ x = y := by
  obtain ⟨v, hv1, hv⟩ := exists_fixed_vector M hirr.1
  choose g hg using exists_conj_zDT
  let u : Fin 15 → M.W := fun ω => M.act (g ω) v
  have hu : ∀ (σ : Perm (Fin 5)) (ω : Fin 15), M.act σ (u ω) = u (piF σ ω) := by
    intro σ ω
    have e1 := hg ω
    have e2 := hg (piF σ ω)
    rw [dt_piF, ← e1] at e2
    have hz : zDT = (g (piF σ ω))⁻¹ * (σ * (g ω * zDT * (g ω)⁻¹) * σ⁻¹) * g (piF σ ω) := by
      rw [← e2]; group
    have hs : ((g (piF σ ω))⁻¹ * σ * g ω) * zDT * ((g (piF σ ω))⁻¹ * σ * g ω)⁻¹ = zDT := by
      calc ((g (piF σ ω))⁻¹ * σ * g ω) * zDT * ((g (piF σ ω))⁻¹ * σ * g ω)⁻¹
          = (g (piF σ ω))⁻¹ * (σ * (g ω * zDT * (g ω)⁻¹) * σ⁻¹) * g (piF σ ω) := by group
        _ = zDT := hz.symm
    have hfix := hv _ (centralizer_zDT hs)
    show M.act σ (M.act (g ω) v) = M.act (g (piF σ ω)) v
    rw [← act_mul_apply]
    have : σ * g ω = g (piF σ ω) * ((g (piF σ ω))⁻¹ * σ * g ω) := by group
    rw [this, act_mul_apply, hfix]
  refine ⟨frobHom M u, frobHom_act M u hu, ?_⟩
  have hinv : IsInvSub M ⊤ (frobHom M u).range := by
    intro b _ y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨Pm.act b x, frobHom_act M u hu b x⟩
  have hv' : v ∈ (frobHom M u).range := by
    have h3 : u 3 = v := by
      have h := hg 3
      rw [dt_three] at h
      exact hv _ (centralizer_zDT h)
    refine ⟨Multiplicative.ofAdd (Pi.single 3 1), ?_⟩
    show (∏ ω, if Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single (3 : Fin 15) (1 : ZMod 2)) :
        Multiplicative (Fin 15 → ZMod 2)) ω = 1 then u ω else 1) = v
    rw [Finset.prod_eq_single (3 : Fin 15)]
    · simp [h3]
    · intro b _ hb
      simp [hb]
    · simp
  rcases hirr.2 _ hinv with h0 | h0
  · rw [h0, Subgroup.mem_bot] at hv'
    exact absurd hv' hv1
  · intro y
    have : y ∈ (frobHom M u).range := by rw [h0]; trivial
    exact this

theorem model5_irred_trichotomy (M : Model 5) (hirr : M.IsIrred) :
    (∀ σ w, M.act σ w = w) ∨ Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat) := by
  by_cases hnt : ∀ σ w, M.act σ w = w
  · exact Or.inl hnt
  right
  obtain ⟨φ, hφ, hsurj⟩ := exists_frob M hirr
  obtain ⟨i, hi, ⟨e⟩⟩ := chain_iso hirr φ hφ hsurj (fun i => Qd (offsF i)) Xf 6 Qd_zero
    Qd_fifteen series_inv series_step
  interval_cases i
  · exfalso
    apply hnt
    intro σ w
    apply e.toMulEquiv.injective
    rw [e.map_act]
    rfl
  · exact Or.inr ⟨e⟩
  · exfalso
    apply hnt
    intro σ w
    apply e.toMulEquiv.injective
    rw [e.map_act]
    rfl
  · exact Or.inl ⟨e⟩
  · exfalso
    apply hnt
    intro σ w
    apply e.toMulEquiv.injective
    rw [e.map_act]
    rfl
  · exact Or.inr ⟨e⟩

theorem model5_irred_classification (M : Model 5) (hirr : M.IsIrred)
    (hnt : ∃ σ w, M.act σ w ≠ w) : Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat) := by
  rcases model5_irred_trichotomy M hirr with h | h
  · obtain ⟨σ, w, hw⟩ := hnt
    exact absurd (h σ w) hw
  · exact h

theorem model5_irred_card (M : Model 5) (hirr : M.IsIrred) (hnt : ∃ σ w, M.act σ w ≠ w) :
    Nat.card M.W = 16 := by
  rcases model5_irred_classification M hirr hnt with h | h
  · obtain ⟨e⟩ := h
    rw [e.card_eq]; exact card_orth
  · obtain ⟨e⟩ := h
    rw [e.card_eq]; exact card_nat

theorem nat_not_iso_orth : ¬ Nonempty (nat.Iso orth) := fun ⟨e⟩ => orth_not_iso_nat ⟨e.symm⟩

end CFSG.Quasithin.F53Mod
