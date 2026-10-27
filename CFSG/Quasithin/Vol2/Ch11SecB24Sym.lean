module

public import CFSG.Quasithin.Vol2.Ch11SecB24One

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem exists_sym (h : Hyp24 T L I n V₁ V₂) {g : G} (hAT : conjSubgroup (fsuV T I) g ≤ T)
    (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥)
    (hVN : fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) :
    ∃ k : G, conjSubgroup (fsuV T I) k ≤ T ∧ ⁅fsuV T I, conjSubgroup (fsuV T I) k⁆ ≠ ⊥ ∧
      fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) k : Set G) ∧
      conjSubgroup (fsuV T I) k⁻¹ = conjSubgroup (fsuV T I) g := by
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  have hAV : conjSubgroup A g⁻¹ = V := E3.conjSubgroup_conj_inv V g
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans (T_le_normalizer_fsuV T I)
  have hBN : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have := E3.conjSubgroup_mono_left g⁻¹ hVN
    rwa [E3.conjSubgroup_normalizer, hAV] at this
  have hB2 : IsPGroup 2 ↥(conjSubgroup V g⁻¹) :=
    E3.isPGroup_conjSubgroup (isPGroup_fsuV h.hyp) g⁻¹
  have hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.fsu.sylow (T_le_normalizer_fsuV T I)
  obtain ⟨x, hx, hxB⟩ := exists_conj_le_of_isSylowTwoOf hTS hBN hB2
  have hVx : conjSubgroup V x⁻¹ = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hx)
  have hVx' : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.mpr hx
  have hk : conjSubgroup V (g⁻¹ * x⁻¹) = conjSubgroup (conjSubgroup V g⁻¹) x⁻¹ :=
    (conjSubgroup_conjSubgroup _ _ _).symm
  have hcj : cjSub x (conjSubgroup V g⁻¹) = conjSubgroup (conjSubgroup V g⁻¹) x⁻¹ := by
    ext y
    simp only [mem_cjSub, mem_conjSubgroup_iff, inv_inv]
  refine ⟨g⁻¹ * x⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hk, ← hcj]
    exact hxB
  · rw [hk]
    have e1 : ⁅V, conjSubgroup (conjSubgroup V g⁻¹) x⁻¹⁆ =
        conjSubgroup (conjSubgroup ⁅A, V⁆ g⁻¹) x⁻¹ := by
      rw [E3.conjSubgroup_commutator, E3.conjSubgroup_commutator, hAV, hVx]
    rw [e1]
    intro h0
    apply hnc
    rw [Subgroup.commutator_comm]
    exact conjSubgroup_eq_bot_iff.mp (conjSubgroup_eq_bot_iff.mp h0)
  · rw [hk, ← E3.conjSubgroup_normalizer]
    have h1 : V ≤ Subgroup.normalizer (conjSubgroup V g⁻¹ : Set G) := by
      rw [← E3.conjSubgroup_le_conjSubgroup_iff g, E3.conjSubgroup_normalizer,
        E3.conjSubgroup_inv_conj]
      exact hAN
    calc V = conjSubgroup V x⁻¹ := hVx.symm
      _ ≤ _ := E3.conjSubgroup_mono_left x⁻¹ h1
  · rw [mul_inv_rev, inv_inv, inv_inv, ← conjSubgroup_conjSubgroup, hVx']

theorem inf_centralizer_sym (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g k : G}
    (hkT : conjSubgroup (fsuV T I) k ≤ T) (hnck : ⁅fsuV T I, conjSubgroup (fsuV T I) k⁆ ≠ ⊥)
    (hkg : conjSubgroup (fsuV T I) k⁻¹ = conjSubgroup (fsuV T I) g) :
    conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G) = conjSubgroup V₂ k⁻¹ := by
  have h2 := (line24 hI h hkT hnck).2
  have : conjSubgroup (fsuV T I ⊓ Subgroup.centralizer (conjSubgroup (fsuV T I) k : Set G)) k⁻¹ =
      conjSubgroup V₂ k⁻¹ := by rw [h2]
  rw [conjSubgroup_inf_centralizer, E3.conjSubgroup_conj_inv, hkg] at this
  exact this

end CFSG.Quasithin.Vol2.Ch11.SecB
