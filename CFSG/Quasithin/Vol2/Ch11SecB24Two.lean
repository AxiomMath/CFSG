module

public import CFSG.Quasithin.Vol2.Ch11SecA14Delta2
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Vol2.Ch11SecB24Claim

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

theorem isSylowTwoOf_conjSubgroup {G : Type} [Group G] {S H : Subgroup G}
    (hS : QuasithinUnique.IsSylowTwoOf S H) {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    QuasithinUnique.IsSylowTwoOf (conjSubgroup S g) H := by
  have hH : conjSubgroup H g = H := conjSubgroup_eq_iff_mem_normalizer.mpr hg
  refine ⟨hH ▸ E3.conjSubgroup_mono_left g hS.1, E3.isPGroup_conjSubgroup hS.2.1 g, ?_⟩
  have := E3.relIndex_conjSubgroup S H g
  rw [hH] at this
  show ¬ 2 ∣ (conjSubgroup S g).relIndex H
  rw [this]
  exact hS.2.2

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem isSylowTwoOf_inf_lOf (h : Hyp24 T L I n V₁ V₂) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ LOf L V₂) (LOf L V₂) := by
  have hsub : LOf L V₂ ≤ LOf L V₂ ⊔ T := le_sup_left
  have hN : LOf L V₂ ⊔ T ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_lOf h.hyp.normal (IsVi.le_normalizer h.v₂))
  exact QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
    (isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.fsu.sylow le_sup_right) hsub
    (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mpr hN))

theorem case_eq24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g k : G}
    (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥)
    (hVN : fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G))
    (hkg : conjSubgroup (fsuV T I) k⁻¹ = conjSubgroup (fsuV T I) g)
    (hCA : conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      conjSubgroup V₂ k⁻¹)
    (hcase : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ = V₂) : False := by
  have hfl := h.flag hI
  obtain ⟨hCL2, hpt⟩ := hI.facts.l2Point G L (fsuV T I) ⊤ T V₁ V₂ n hfl
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  set CV := V ⊓ Subgroup.centralizer (L : Set G) with hCVdef
  have hV2A : V₂ ≤ A ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf ?_ ?_
    · rw [← hcase]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hVN
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact B2F.isElemAbelian_comm hfl.elem hw (hfl.le₂ hv)
  have hV2eq : V₂ = conjSubgroup V₂ k⁻¹ :=
    Subgroup.eq_of_le_of_card_ge (hCA ▸ hV2A) (le_of_eq (E3.card_conjSubgroup V₂ k⁻¹))
  have hkN : k⁻¹ ∈ Subgroup.normalizer (V₂ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hV2eq.symm
  have hV2k : conjSubgroup V₂ k⁻¹ = V₂ := hV2eq.symm
  obtain ⟨hcomp, hnot, huniq⟩ := hI.s1113 G T L I n V₂ h.hyp h.v₂
  have hL2 : conjSubgroup (LOf L V₂) k⁻¹ = LOf L V₂ := by
    refine huniq _ ?_ ?_
    · have := isCComponent_map_equiv (MulAut.conj k⁻¹⁻¹) hcomp
      change quasithinIsCComponent (conjSubgroup (LOf L V₂) k⁻¹)
        (conjSubgroup (Subgroup.normalizer (V₂ : Set G)) k⁻¹) at this
      rwa [E3.conjSubgroup_normalizer, hV2k] at this
    · intro hle
      apply hnot
      rw [← E3.conjSubgroup_le_conjSubgroup_iff k⁻¹, E3.conjSubgroup_centralizer, hV2k]
      exact hle
  have hkL2 : k⁻¹ ∈ Subgroup.normalizer (LOf L V₂ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hL2
  have hk2 : k ∈ Subgroup.normalizer (V₂ : Set G) := by simpa using Subgroup.inv_mem _ hkN
  have hkL : k ∈ Subgroup.normalizer (LOf L V₂ : Set G) := by
    simpa using Subgroup.inv_mem _ hkL2
  have hV2i : conjSubgroup V₂ k = V₂ := conjSubgroup_eq_iff_mem_normalizer.mpr hk2
  have hL2i : conjSubgroup (LOf L V₂) k = LOf L V₂ := conjSubgroup_eq_iff_mem_normalizer.mpr hkL
  have hCVi : conjSubgroup CV k = CV := by
    rw [← hCL2, conjSubgroup_inf_centralizer, hV2i, hL2i]
  have hU1 : CV ≤ conjSubgroup V₁ k := by
    rw [← hCVi]
    exact E3.conjSubgroup_mono_left k hfl.cV_le
  have hU2 : conjSubgroup V₁ k ≤ V₂ := by
    rw [← hV2i]
    exact E3.conjSubgroup_mono_left k hfl.le₁₂
  have hU3 : CV.relIndex (conjSubgroup V₁ k) = 2 ^ n := by
    rw [← hCVi, E3.relIndex_conjSubgroup, hfl.index₁]
  have hS := isSylowTwoOf_conjSubgroup (isSylowTwoOf_inf_lOf h) hkL
  have hSN : conjSubgroup (T ⊓ LOf L V₂) k ≤
      Subgroup.normalizer (conjSubgroup V₁ k : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact E3.conjSubgroup_mono_left k (inf_le_left.trans hfl.T_le_V₁)
  obtain ⟨l, hl, hlU⟩ := hpt _ _ hU1 hU2 hU3 hS hSN
  have hV1 : conjSubgroup V₁ (k * l⁻¹) = V₁ := by
    rw [← conjSubgroup_conjSubgroup, hlU, E3.conjSubgroup_conj_inv]
  have hmem : (k * l⁻¹)⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.inv_mem _ (conjSubgroup_eq_iff_mem_normalizer.mp hV1)
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := hfl.le_normalizer (lOf_le L V₂ hl)
  have hVc : conjSubgroup V (k * l⁻¹)⁻¹ = A := by
    rw [mul_inv_rev, inv_inv, ← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr hlV]
    exact hkg
  exact not_mem_normalizer_of_ne_bot h.abelian (g := (k * l⁻¹)⁻¹) (by rw [hVc]; exact hnc) hmem

end CFSG.Quasithin.Vol2.Ch11.SecB
