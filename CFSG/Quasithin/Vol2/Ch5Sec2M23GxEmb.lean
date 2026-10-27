module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23GxRho

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Matrix

variable {G : Type} [Group G]

omit [Group G] in
theorem conj_ringEquiv_eq_frob {K : Type} [Field K] (κ : K ≃+* F4) {σ : K ≃+* K}
    (hσ : σ ≠ RingEquiv.refl K) :
    κ.symm.trans (σ.trans κ) = CFSG.ComponentClassification.WittDesign.frobF4 := by
  rcases ringEquiv_F4 (κ.symm.trans (σ.trans κ)) with h | h
  · exfalso
    apply hσ
    refine RingEquiv.ext fun x => ?_
    have := congrArg (fun f : F4 ≃+* F4 => κ.symm (f (κ x))) h
    simpa using this
  · exact h

theorem mem_or_mul_inv_mem_of_relIndex_eq_two {X H : Subgroup G}
    (hidx : H.relIndex X = 2) {t : G} (htX : t ∈ X) (htH : t ∉ H) {g : G} (hgX : g ∈ X) :
    g ∈ H ∨ g * t⁻¹ ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hidx
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
  by_cases hg : g ∈ H
  · exact Or.inl hg
  right
  have hg' : (⟨g, hgX⟩ : ↥X) ∉ H.subgroupOf X := hg
  have ht' : (⟨t, htX⟩ : ↥X) ∉ H.subgroupOf X := htH
  have h1 := ha ⟨g, hgX⟩
  have h3 := ha ⟨t, htX⟩
  have hga : (⟨g, hgX⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hg'
  have hta : (⟨t, htX⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases h3 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h ht'
  have := (H.subgroupOf X).mul_mem hga ((H.subgroupOf X).inv_mem hta)
  rw [Subgroup.mem_subgroupOf] at this
  simpa [mul_assoc] using this

theorem induces_pslCoord {G0 : Subgroup G} {K : Type} [Field K] (κ : K ≃+* F4)
    (e : ↥G0 ≃* projectiveSL 3 K) {t : G} (A : GL (Fin 3) K) {σ : K ≃+* K}
    (hσ : σ ≠ RingEquiv.refl K)
    (hrel : ∀ x y : ↥G0, (y : G) = t * x * t⁻¹ →
      e y = LinearFlag.conjAut 3 K A (LinearFlag.fieldAut 3 K σ (e x))) :
    Induces (pslPerm.comp ((pslCoord κ).toMonoidHom.comp e.toMonoidHom)) t
      (planePerm (semΓ (Matrix.GeneralLinearGroup.map κ.toRingHom A)
        CFSG.ComponentClassification.WittDesign.frobF4)) := by
  intro x hx htx
  have e1 := hrel ⟨x, hx⟩ ⟨t * x * t⁻¹, htx⟩ rfl
  change pslPerm (pslCoord κ (e ⟨t * x * t⁻¹, htx⟩)) = _ * pslPerm (pslCoord κ (e ⟨x, hx⟩)) * _
  rw [e1, pslPerm_pslCoord_conjAut, conj_ringEquiv_eq_frob κ hσ]

theorem injective_pslCoord_comp {G0 : Subgroup G} {K : Type} [Field K] (κ : K ≃+* F4)
    (e : ↥G0 ≃* projectiveSL 3 K) :
    Function.Injective (pslPerm.comp ((pslCoord κ).toMonoidHom.comp e.toMonoidHom)) :=
  pslPerm_injective.comp ((pslCoord κ).injective.comp e.injective)

theorem range_pslCoord_comp {G0 : Subgroup G} {K : Type} [Field K] (κ : K ≃+* F4)
    (e : ↥G0 ≃* projectiveSL 3 K) :
    (pslPerm.comp ((pslCoord κ).toMonoidHom.comp e.toMonoidHom)).range = P0 := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := e.surjective ((pslCoord κ).symm q)
    refine ⟨x, ?_⟩
    simp [hx]

theorem map_refl_GL (A : GL (Fin 3) F4) :
    Matrix.GeneralLinearGroup.map ((RingEquiv.refl F4 : F4 ≃+* F4) : F4 →+* F4) A = A := by
  ext i j
  simp

theorem semΓ_conj_frob (M A : GL (Fin 3) F4) :
    semΓ M (RingEquiv.refl F4) * semΓ A CFSG.ComponentClassification.WittDesign.frobF4 *
        (semΓ M (RingEquiv.refl F4))⁻¹ =
      semΓ (M * A * Matrix.GeneralLinearGroup.map
        (CFSG.ComponentClassification.WittDesign.frobF4 : F4 →+* F4) M⁻¹)
        CFSG.ComponentClassification.WittDesign.frobF4 := by
  rw [semΓ_inv, semΓ_mul, semΓ_mul, map_refl_GL]
  congr 1

theorem planePerm_conj_frob (M A : GL (Fin 3) F4) :
    planePerm (semΓ M (RingEquiv.refl F4)) *
        planePerm (semΓ A CFSG.ComponentClassification.WittDesign.frobF4) *
        (planePerm (semΓ M (RingEquiv.refl F4)))⁻¹ =
      planePerm (semΓ (M * A * Matrix.GeneralLinearGroup.map
        (CFSG.ComponentClassification.WittDesign.frobF4 : F4 →+* F4) M⁻¹)
        CFSG.ComponentClassification.WittDesign.frobF4) := by
  rw [← map_inv, ← map_mul, ← map_mul, semΓ_conj_frob]

theorem induces_conj {G0 : Subgroup G} {ψ : ↥G0 →* Equiv.Perm (Fin 21)} {t : G}
    {A : GL (Fin 3) F4}
    (h : Induces ψ t (planePerm (semΓ A CFSG.ComponentClassification.WittDesign.frobF4)))
    (M : GL (Fin 3) F4) :
    Induces ((MulAut.conj (planePerm (semΓ M (RingEquiv.refl F4)))).toMonoidHom.comp ψ) t
      (planePerm (semΓ (M * A * Matrix.GeneralLinearGroup.map
        (CFSG.ComponentClassification.WittDesign.frobF4 : F4 →+* F4) M⁻¹)
        CFSG.ComponentClassification.WittDesign.frobF4)) := by
  intro x hx htx
  rw [← planePerm_conj_frob]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [h x hx htx]
  group

theorem range_conj_eq_P0 {G0 : Subgroup G} {ψ : ↥G0 →* Equiv.Perm (Fin 21)} (hψ : ψ.range = P0)
    (M : GL (Fin 3) F4) :
    ((MulAut.conj (planePerm (semΓ M (RingEquiv.refl F4)))).toMonoidHom.comp ψ).range = P0 := by
  rw [MonoidHom.range_comp, hψ]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact planePerm_conj_mem _ hp
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem exists_rho_of_induces {G0 T : Subgroup G} (hTN : T ≤ Subgroup.normalizer (G0 : Set G))
    (hidx : G0.relIndex (G0 ⊔ T) = 2) {ψ : ↥G0 →* Equiv.Perm (Fin 21)}
    (hψinj : Function.Injective ψ) (hψ : ψ.range = P0) {t : G} (htT : t ∈ T)
    (A : GL (Fin 3) F4)
    (hind : Induces ψ t (planePerm (semΓ A CFSG.ComponentClassification.WittDesign.frobF4))) :
    ∃ (ρ : ↥(G0 ⊔ T) →* Equiv.Perm (Fin 21)) (htGT : t ∈ G0 ⊔ T),
      Function.Injective ρ ∧ t ∉ G0 ∧
      (∀ g : G, g ∈ G0 ⊔ T → g ∈ G0 ∨ g * t⁻¹ ∈ G0) ∧
      (∀ (g : G) (hg : g ∈ G0), ρ ⟨g, Subgroup.mem_sup_left hg⟩ = ψ ⟨g, hg⟩) ∧
      ρ ⟨t, htGT⟩ = planePerm (semΓ A CFSG.ComponentClassification.WittDesign.frobF4) ∧
      Nat.card ↥(G0 ⊔ T) = 40320 := by
  set τ := planePerm (semΓ A CFSG.ComponentClassification.WittDesign.frobF4) with hτ
  have htN : t ∈ Subgroup.normalizer (G0 : Set G) := hTN htT
  have htS : t ∈ induceSub ψ := ⟨htN, τ, hind⟩
  have hτnot := planePerm_semΓ_frob_not_mem A
  have htG0 : t ∉ G0 := by
    intro htG
    have h1 : Induces ψ t (ψ ⟨t, htG⟩) := fun y hy hty => by
      have : (⟨t * y * t⁻¹, hty⟩ : ↥G0) = ⟨t, htG⟩ * ⟨y, hy⟩ * ⟨t, htG⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have h2 := Induces.unique hψ htN h1 hind
    apply hτnot
    rw [← hτ, ← h2, ← hψ]
    exact ⟨_, rfl⟩
  have htGT : t ∈ G0 ⊔ T := Subgroup.mem_sup_right htT
  have hsplit : ∀ g : G, g ∈ G0 ⊔ T → g ∈ G0 ∨ g * t⁻¹ ∈ G0 := fun g hg =>
    mem_or_mul_inv_mem_of_relIndex_eq_two hidx htGT htG0 hg
  have hle : G0 ⊔ T ≤ induceSub ψ := by
    intro g hg
    rcases hsplit g hg with h | h
    · exact mem_induceSub_of_mem h
    · have := (induceSub ψ).mul_mem (mem_induceSub_of_mem (ψ := ψ) h) htS
      simpa using this
  set ρ : ↥(G0 ⊔ T) →* Equiv.Perm (Fin 21) := (induceHom hψ).comp (Subgroup.inclusion hle)
    with hρ
  have hρG0 : ∀ g : ↥(G0 ⊔ T), ∀ hg : (g : G) ∈ G0, ρ g = ψ ⟨g, hg⟩ := fun g hg =>
    induceHom_of_mem hψ (Subgroup.inclusion hle g) hg
  have hρt : ρ ⟨t, htGT⟩ = τ := induceHom_eq hψ (g := Subgroup.inclusion hle ⟨t, htGT⟩) hind
  refine ⟨ρ, htGT, ?_, htG0, hsplit, fun g hg => hρG0 ⟨g, _⟩ hg, hρt, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rcases hsplit g g.2 with h | h
    · rw [hρG0 g h] at hg
      have : (⟨g, h⟩ : ↥G0) = 1 := hψinj (by rw [hg, map_one])
      have h1 : (g : G) = 1 := congrArg Subtype.val this
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    · exfalso
      have hgt : (g : G) * t⁻¹ ∈ G0 ⊔ T := Subgroup.mul_mem _ g.2 (Subgroup.inv_mem _ htGT)
      have e1 : g = ⟨(g : G) * t⁻¹, hgt⟩ * ⟨t, htGT⟩ := Subtype.ext (by simp)
      rw [e1, map_mul, hρt, hρG0 _ h] at hg
      apply hτnot
      rw [← hτ, eq_inv_of_mul_eq_one_right hg, ← hψ]
      exact Subgroup.inv_mem _ ⟨_, rfl⟩
  · have hG0 : Nat.card G0 = 20160 := by
      have h := Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
      rw [hψ, card_range_pslPerm] at h
      exact h
    have h1 := Subgroup.card_mul_index (G0.subgroupOf (G0 ⊔ T))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hG0] at h1
    have h2 : (G0.subgroupOf (G0 ⊔ T)).index = 2 := hidx
    rw [h2] at h1
    omega

end CFSG.Quasithin.H13
