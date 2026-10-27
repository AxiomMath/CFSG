module

public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem map_eq_of_forall_mem {g : V ≃ₗ[F] V} {U U' : Submodule F V}
    (h1 : ∀ u ∈ U, g u ∈ U') (h2 : ∀ u ∈ U', g⁻¹ u ∈ U) : U.map (g : V →ₗ[F] V) = U' := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun u hu => h1 u hu) fun u hu => ?_
  exact ⟨g⁻¹ u, h2 u hu, g.apply_symm_apply u⟩

theorem isImprimitiveOnV_of_family {G₀ : Subgroup (V ≃ₗ[F] V)} {ι : Type*} [Finite ι]
    (hι : 1 < Nat.card ι) (U : ι → Submodule F V) (hU0 : ∀ i, U i ≠ ⊥) (hind : iSupIndep U)
    (hsup : (⨆ i, U i) = ⊤) (hperm : ∀ g ∈ G₀, ∀ i, ∃ j, (U i).map (g : V →ₗ[F] V) = U j) :
    IsImprimitiveOnV G₀ := by
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, U ∘ e.symm, hι, fun i => hU0 _, hind.comp e.symm.injective, ?_, ?_⟩
  · rw [← hsup]
    exact e.symm.iSup_comp (g := U)
  · intro g hg i
    obtain ⟨j, hj⟩ := hperm g hg (e.symm i)
    exact ⟨e j, by simp only [Function.comp_apply, Equiv.symm_apply_apply, hj]⟩

theorem isImprimitiveOnV_of_pair {G₀ : Subgroup (V ≃ₗ[F] V)} {U U' : Submodule F V}
    (hU : U ≠ ⊥) (hU' : U' ≠ ⊥) (hdisj : Disjoint U U') (hsup : U ⊔ U' = ⊤)
    (hperm : ∀ g ∈ G₀,
      (U.map (g : V →ₗ[F] V) = U ∧ U'.map (g : V →ₗ[F] V) = U') ∨
        (U.map (g : V →ₗ[F] V) = U' ∧ U'.map (g : V →ₗ[F] V) = U)) :
    IsImprimitiveOnV G₀ := by
  refine ⟨2, ![U, U'], by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hU
    · exact hU'
  · refine (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide) (fun k => ?_)).mpr hdisj
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [← hsup]
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup (fun i => ![U, U'] i) 0)
      (le_iSup (fun i => ![U, U'] i) 1))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro g hg i
    rcases hperm g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · fin_cases i
      · exact ⟨0, h1⟩
      · exact ⟨1, h2⟩
    · fin_cases i
      · exact ⟨1, h1⟩
      · exact ⟨0, h2⟩

theorem irreducible_of_index_two {G H : Subgroup (V ≃ₗ[F] V)} (hirr : IsIrredOnV G)
    (hprim : ¬ IsImprimitiveOnV G) (hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    {t : V ≃ₗ[F] V} (ht : t ∈ G) (hcos : ∀ g ∈ G, g ∈ H ∨ g * t ∈ H) : IsIrredOnV H := by
  intro U hU
  by_cases htH : t ∈ H
  ·
    refine hirr U fun g hg w hw => ?_
    rcases hcos g hg with h | h
    · exact hU g h w hw
    · have hgH : g ∈ H := by
        have := H.mul_mem h (H.inv_mem htH)
        rwa [mul_inv_cancel_right] at this
      exact hU g hgH w hw
  have htt : t * t ∈ H := (hcos t ht).resolve_left htH
  by_contra hne
  push Not at hne
  obtain ⟨hU0, hU1⟩ := hne
  set U' := U.map (t : V →ₗ[F] V)
  have hmemU' : ∀ x, x ∈ U' ↔ t⁻¹ x ∈ U := fun x => Submodule.mem_map_equiv U
  have hinvapp : ∀ (g : V ≃ₗ[F] V) (x : V), g (g⁻¹ x) = x := fun g x => g.apply_symm_apply x
  have hHU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := hU
  have hHU' : ∀ h ∈ H, ∀ x ∈ U', h x ∈ U' := by
    intro h hh x hx
    rw [hmemU'] at hx ⊢
    have hc : t⁻¹ * h * t ∈ H := by
      have := hHn t⁻¹ (G.inv_mem ht) h hh
      rwa [inv_inv] at this
    have := hU _ hc (t⁻¹ x) hx
    simpa only [LinearEquiv.mul_apply, hinvapp] using this
  have hswap : ∀ g ∈ G, g ∉ H → (∀ u ∈ U, g u ∈ U') ∧ (∀ x ∈ U', g x ∈ U) := by
    intro g hg hgH
    have hgt : g * t ∈ H := (hcos g hg).resolve_left hgH
    have htg : t * g ∈ H := by
      have := hHn t ht (g * t) hgt
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
    have htig : t⁻¹ * g ∈ H := by
      have := H.mul_mem (H.inv_mem htt) htg
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using this
    refine ⟨fun u hu => ?_, fun x hx => ?_⟩
    · rw [hmemU']
      have := hU _ htig u hu
      simpa only [LinearEquiv.mul_apply] using this
    · rw [hmemU'] at hx
      have := hU _ hgt (t⁻¹ x) hx
      simpa only [LinearEquiv.mul_apply, hinvapp] using this
  have hfix : ∀ g ∈ G, ((∀ u ∈ U, g u ∈ U) ∧ (∀ x ∈ U', g x ∈ U')) ∨
      ((∀ u ∈ U, g u ∈ U') ∧ (∀ x ∈ U', g x ∈ U)) := by
    intro g hg
    by_cases hgH : g ∈ H
    · exact Or.inl ⟨hHU g hgH, hHU' g hgH⟩
    · exact Or.inr (hswap g hg hgH)
  have hinf : U ⊓ U' = ⊥ := by
    rcases hirr (U ⊓ U') (fun g hg w hw => by
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
      rcases hfix g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Submodule.mem_inf.mpr ⟨h1 w hw1, h2 w hw2⟩
      · exact Submodule.mem_inf.mpr ⟨h2 w hw2, h1 w hw1⟩) with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ inf_le_left)) hU1
  have hsup : U ⊔ U' = ⊤ := by
    rcases hirr (U ⊔ U') (fun g hg w hw => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      rcases hfix g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Submodule.add_mem_sup (h1 a ha) (h2 b hb)
      · rw [add_comm]
        exact Submodule.add_mem_sup (h2 b hb) (h1 a ha)) with h | h
    · exact absurd (eq_bot_iff.mpr (h ▸ le_sup_left)) hU0
    · exact h
  have hU'0 : U' ≠ ⊥ := by
    intro h
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    have : t u ∈ U' := Submodule.mem_map_of_mem hu
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    simpa using this
  apply hprim
  refine isImprimitiveOnV_of_pair hU0 hU'0 (disjoint_iff.mpr hinf) hsup fun g hg => ?_
  by_cases hgH : g ∈ H
  · have hgi : g⁻¹ ∈ H := H.inv_mem hgH
    exact Or.inl ⟨map_eq_of_forall_mem (hHU g hgH) (hHU g⁻¹ hgi),
      map_eq_of_forall_mem (hHU' g hgH) (hHU' g⁻¹ hgi)⟩
  · have hgi : g⁻¹ ∉ H := fun h => hgH (by simpa using H.inv_mem h)
    obtain ⟨h1, h2⟩ := hswap g hg hgH
    obtain ⟨h1', h2'⟩ := hswap g⁻¹ (G.inv_mem hg) hgi
    exact Or.inr ⟨map_eq_of_forall_mem h1 h2', map_eq_of_forall_mem h2 h1'⟩

end CFSG.Quasithin.SimsG4
