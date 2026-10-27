module

public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Open (IsElemAbelian)

variable {R R' : Type} [Group R] [Group R']

@[expose] def EltHyp (a : R) (D : Subgroup R) : Prop :=
  D ≤ Subgroup.centralizer ({a} : Set R) ∧
    (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧ CFSG.IsQuasisimple D

@[expose] def EltConcl (p : ℕ) (A D : Subgroup R) : Prop :=
  ∃ U : Subgroup R, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
    ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set R) ∧
      ∃ j ∈ D, t * j ≠ j * t

@[expose] def EltNormWeak (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∀ a ∈ A, a ≠ 1 → ∀ D : Subgroup R, EltHyp a D → EltConcl p A D

theorem mem_centralizer_map_iff (φ : R ≃* R') {a : R} {c : R'} :
    c ∈ Subgroup.centralizer ({φ a} : Set R') ↔
      φ.symm c ∈ Subgroup.centralizer ({a} : Set R) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg φ.symm h
  · intro h
    simpa using congrArg φ h

theorem eltHyp_map (φ : R ≃* R') {a : R} {D : Subgroup R} (h : EltHyp a D) :
    EltHyp (φ a) (D.map φ.toMonoidHom) := by
  obtain ⟨hDC, hDn, hDq⟩ := h
  refine ⟨fun x hx => ?_, fun c hc x hx => ?_,
    (CFSG.IsQuasisimple.congr (D.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hDq⟩
  · rw [Subgroup.mem_map_equiv] at hx
    rw [mem_centralizer_map_iff]
    exact hDC hx
  · rw [Subgroup.mem_map_equiv] at hx ⊢
    rw [mem_centralizer_map_iff] at hc
    rw [map_mul, map_mul, map_inv]
    exact hDn _ hc _ hx

theorem eltConcl_of_map (φ : R ≃* R') {p : ℕ} {A D : Subgroup R}
    (h : EltConcl p (A.map φ.toMonoidHom) (D.map φ.toMonoidHom)) : EltConcl p A D := by
  obtain ⟨U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, j, hjD, hj⟩ := h
  rw [Subgroup.mem_map_equiv] at htD hjD
  refine ⟨U.comap φ.toMonoidHom, fun u hu => ?_, fun h0 => hU1 ?_,
    hU2.comap_of_injective _ φ.injective, fun s hs u hu => ?_, φ.symm t, htD, ?_, fun s hs => ?_,
    ?_, φ.symm j, hjD, fun hc => hj ?_⟩
  · have h1 := Subgroup.mem_map_equiv.1 (hUD (Subgroup.mem_comap.1 hu))
    simpa using h1
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 : φ.symm x ∈ U.comap φ.toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa using hx
    rw [h0, Subgroup.mem_bot] at h1
    simpa using congrArg φ h1
  · rw [Subgroup.mem_comap] at hu ⊢
    have h1 := hAU _ (Subgroup.mem_map_of_mem φ.toMonoidHom hs) _ hu
    rwa [map_mul, map_mul, map_inv]
  · rw [← map_pow, htp, map_one]
  · apply φ.injective
    have h1 := htA _ (Subgroup.mem_map_of_mem φ.toMonoidHom hs)
    simpa using h1
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.1 htU (φ u)
  · simpa using congrArg φ hc

theorem eltConcl_mono {p : ℕ} {A B D : Subgroup R} (hAB : A ≤ B) (h : EltConcl p B D) :
    EltConcl p A D := by
  obtain ⟨U, hUD, hU1, hU2, hBU, t, htD, htp, htB, htU, hj⟩ := h
  exact ⟨U, hUD, hU1, hU2, fun s hs => hBU s (hAB hs), t, htD, htp, fun s hs => htB s (hAB hs),
    htU, hj⟩

theorem eltNormWeak_of_mulEquiv (φ : R ≃* R') {p r : ℕ} (h : EltNormWeak p r R') :
    EltNormWeak p r R := by
  intro A hA hr h3 hα a ha ha1 D hD
  have hc : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective φ.injective
  refine eltConcl_of_map φ (h _ (hA.map _) (by rw [hc]; exact hr) (by rw [hc]; exact h3) ?_
    (φ a) ⟨a, ha, rfl⟩ (fun h1 => ha1 (φ.injective (h1.trans (map_one φ).symm))) _
    (eltHyp_map φ hD))
  obtain ⟨U, hU1, hU2, hAU⟩ := hα
  refine ⟨U.map φ.toMonoidHom, ?_, hU2.map _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective U φ.injective]
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_normalizer_iff.1 (hAU hs) (φ.symm x)

end CFSG.StandardType.SmallExc.F4Two

end
