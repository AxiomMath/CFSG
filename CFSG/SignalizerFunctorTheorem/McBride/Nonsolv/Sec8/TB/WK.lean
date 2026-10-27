module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Pair

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] {A : Subgroup G} {θ : G → Subgroup G}

@[expose] def wKFam (θ : G → Subgroup G) (E F : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ K' ∈ Ind (thetaOf θ F), Y = wK θ E K'}

theorem map_conj_lHat_le {H L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    (lHat H L).map (MulAut.conj a).toMonoidHom ≤ lHat H (L.map (MulAut.conj a).toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun R hR => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨map_conj_mem_lcal hR.1 ha, fun hLR => hR.2 ?_⟩
  intro x hx y hy
  have h := hLR (Subgroup.mem_map_of_mem _ hx) _ (Subgroup.mem_map_of_mem _ hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  calc y * x = a⁻¹ * (a * y * a⁻¹ * (a * x * a⁻¹)) * a := by group
    _ = a⁻¹ * (a * x * a⁻¹ * (a * y * a⁻¹)) * a := by rw [h]
    _ = x * y := by group

theorem map_conj_lHat {H L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    (lHat H L).map (MulAut.conj a).toMonoidHom = lHat H (L.map (MulAut.conj a).toMonoidHom) := by
  refine le_antisymm (map_conj_lHat_le ha) ?_
  have h1 := map_conj_lHat_le (H := H) (L := L.map (MulAut.conj a).toMonoidHom) (inv_mem ha)
  rw [map_conj_map_conj_inv] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) h1
  rwa [map_conj_inv_map_conj] at h2

theorem wK_map_conj (hA : IsMulCommutative A) {E : Subgroup G} (hEA : E ≤ A)
    (hAH : A ≤ Subgroup.normalizer (thetaOf θ E : Set G)) {a : G} (ha : a ∈ A) (K' : Subgroup G) :
    (wK θ E K').map (MulAut.conj a).toMonoidHom = wK θ E (K'.map (MulAut.conj a).toMonoidHom) := by
  have := hA
  have hcomm : ∀ b ∈ E, b * a = a * b := fun b hb => setLike_mul_comm (hEA hb) ha
  unfold wK
  rw [Subgroup.map_sup, map_conj_lHat (hAH ha),
    Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective,
    Near.Lemma212.map_conj_centralizer_of_commute E hcomm]

variable [Finite G]

theorem isRegFam_wKFam
    (h : Counterexample p A θ) {E K : Subgroup G} (hB : TypeB p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    IsRegFam A (sSup (Msig p A θ)) (wKFam θ E F) (E ⊔ F) := by
  obtain ⟨hdp, htrans, hstab⟩ := h.theorem_8_5 hB hF hFE
  have hΩ := h.isRegFam_line_of_typeB hB.toTypeBCore hF hFE
  have hInd := h.ind_eq_lcal_line_of_typeB hB.toTypeBCore hF hFE
  have hAH := h.isFunctor.normalizes_thetaOf hB.mem.1
  refine ⟨hdp, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K', hK'⟩ := hΩ.nonempty
    exact ⟨wK θ E K', K', hInd ▸ hK', rfl⟩
  · rintro _ ⟨K', hK', rfl⟩ hbot
    exact hΩ.ne_bot K' (hInd ▸ hK') (le_bot_iff.mp (hbot ▸ le_sup_left))
  · rintro a ha _ ⟨K', hK', rfl⟩
    refine ⟨K'.map (MulAut.conj a).toMonoidHom, ?_,
      wK_map_conj h.elemAbelian.1 hB.mem.1 hAH ha K'⟩
    rw [hInd]
    exact hΩ.map_conj_mem a ha K' (hInd ▸ hK')
  · rintro _ ⟨K', hK', rfl⟩ _ ⟨K'', hK'', rfl⟩
    exact htrans K' hK' K'' hK''
  · rintro _ ⟨K', hK', rfl⟩
    exact hstab K' hK'

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
