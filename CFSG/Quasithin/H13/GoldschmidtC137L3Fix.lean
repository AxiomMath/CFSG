module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.H13.GoldschmidtC137L3Mod

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Quasithin.L3

variable {M : Type} [CommGroup M] (φ : M ≃* Multiplicative Vec)

include φ

omit φ in
theorem mem_fixV_zpowers {a : MulAut M} {m : M} :
    m ∈ fixV (Subgroup.zpowers a) ↔ a m = m :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_fixV_zpowers_invol {a : MulAut M} (h2 : a ^ 2 = 1) (h1 : a ≠ 1) :
    Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
  have hinv : IsInvol (psi φ a) := by
    refine ⟨?_, fun h => h1 ((psi φ).injective (by rw [h, map_one]))⟩
    rw [← pow_two, ← map_pow, h2, map_one]
  have h4 := invol_fixS_card _ hinv
  rw [← h4, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv (crdEquiv φ) fun m => ?_)
  rw [mem_fixV_zpowers]
  simp only [crdEquiv_apply, fixS, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [act_psi]
  exact (crd_injective φ).eq_iff.symm

theorem mem_fixV_v4M {u : M} {hu : u ≠ 1} {m : M} :
    m ∈ fixV (v4M φ u hu) ↔ m = 1 ∨ m = u := by
  constructor
  · intro h
    have h1 := v4_fix (crd φ u) (crd_ne_zero φ hu) (crd φ m) (fun g hg => by
      have := h ((psi φ).symm g) (by
        show psi φ ((psi φ).symm g) ∈ AS {0, crd φ u}
        rw [MulEquiv.apply_symm_apply]
        exact hg)
      have h2 := act_psi φ ((psi φ).symm g) m
      rw [MulEquiv.apply_symm_apply, this] at h2
      exact h2)
    rcases h1 with h0 | h0
    · exact Or.inl ((crd_eq_zero_iff φ m).1 h0)
    · exact Or.inr (crd_injective φ h0)
  · rintro (h | h)
    · rw [h]
      exact (fixV (v4M φ u hu)).one_mem
    · rw [h]
      intro a ha
      exact (mem_stabM φ).1 (v4M_le_stabM φ u hu ha)

theorem card_fixV_v4M {u : M} (hu : u ≠ 1) : Nat.card (fixV (v4M φ u hu)) = 2 := by
  have hu' : u ∈ fixV (v4M φ u hu) := (mem_fixV_v4M φ).2 (Or.inr rfl)
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (fixV (v4M φ u hu)).one_mem⟩, ⟨u, hu'⟩, ?_, ?_⟩
  · intro h
    exact hu (congrArg Subtype.val h).symm
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_fixV_v4M φ).1 z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem fixV_top : fixV (⊤ : Subgroup (MulAut M)) = ⊥ := by
  ext m
  rw [mem_fixV, Subgroup.mem_bot]
  constructor
  · intro h
    by_contra hm
    obtain ⟨g, hg⟩ := act_nofix (crd φ m) (fun h0 => hm ((crd_eq_zero_iff φ m).1 h0))
    have h1 := h ((psi φ).symm g) trivial
    have h2 := act_psi φ ((psi φ).symm g) m
    rw [MulEquiv.apply_symm_apply, h1] at h2
    exact hg h2
  · rintro rfl x _
    exact map_one x

omit [CommGroup M] φ in
theorem exists_gen_conjΓ (t : Γ) (ht : IsInvol t) :
    ∃ g₂ g₃ : Γ, Subgroup.closure ({t, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹} : Set Γ) = ⊤ := by
  obtain ⟨x, hx⟩ := conj_invol x12_invol ht
  obtain ⟨y₂, hy₂⟩ := conj_invol x12_invol x23_invol
  obtain ⟨y₃, hy₃⟩ := conj_invol x12_invol x31_invol
  refine ⟨x * y₂ * x⁻¹, x * y₃ * x⁻¹, ?_⟩
  have e2 : x * y₂ * x⁻¹ * t * (x * y₂ * x⁻¹)⁻¹ = x * x23 * x⁻¹ := by
    rw [← hx, ← hy₂]; group
  have e3 : x * y₃ * x⁻¹ * t * (x * y₃ * x⁻¹)⁻¹ = x * x31 * x⁻¹ := by
    rw [← hx, ← hy₃]; group
  rw [e2, e3, ← hx]
  have h := MonoidHom.map_closure (MulAut.conj x).toMonoidHom ({x12, x23, x31} : Set Γ)
  rw [closure_gens, Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective] at h
  have himg : (MulAut.conj x).toMonoidHom '' ({x12, x23, x31} : Set Γ) =
      {x * x12 * x⁻¹, x * x23 * x⁻¹, x * x31 * x⁻¹} := by
    simp [Set.image_insert_eq]
  rw [himg] at h
  exact h.symm

theorem exists_gen_conj {t : MulAut M} (h2 : t ^ 2 = 1) (h1 : t ≠ 1) :
    ∃ g₂ g₃ : MulAut M,
      Subgroup.closure ({t, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹} : Set (MulAut M)) = ⊤ := by
  have hinv : IsInvol (psi φ t) := by
    refine ⟨?_, fun h => h1 ((psi φ).injective (by rw [h, map_one]))⟩
    rw [← pow_two, ← map_pow, h2, map_one]
  obtain ⟨g₂, g₃, h⟩ := exists_gen_conjΓ _ hinv
  refine ⟨(psi φ).symm g₂, (psi φ).symm g₃, ?_⟩
  apply Subgroup.map_injective (f := (psi φ).toMonoidHom) (psi φ).injective
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ (psi φ).surjective]
  have himg : (psi φ).toMonoidHom '' ({t, (psi φ).symm g₂ * t * ((psi φ).symm g₂)⁻¹,
      (psi φ).symm g₃ * t * ((psi φ).symm g₃)⁻¹} : Set (MulAut M)) =
      {psi φ t, g₂ * psi φ t * g₂⁻¹, g₃ * psi φ t * g₃⁻¹} := by
    simp [Set.image_insert_eq]
  rw [himg]
  exact h

end CFSG.Quasithin.H13.U3.GC137
