module

public import CFSG.Quasithin.EmptyFaithful.S152Y06

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Y0s (T Mc M : Subgroup G) : Subgroup (OTwoQuot M) :=
  imageOTwoQuot M (y0Of T Mc M)

@[expose] def Rcs (Mc M : Subgroup G) : Subgroup (OTwoQuot M) :=
  imageOTwoQuot M (rcOf Mc M)

@[expose] noncomputable def Ys (T Mc M : Subgroup G) : Subgroup (OTwoQuot M) :=
  imageOTwoQuot M (yOf152 T Mc M)

namespace Data

variable {T Mc M : Subgroup G} (h : Data T Mc M)

include h

theorem commutator_y0Of_rc_le_M : ⁅y0Of T Mc M, rcOf Mc M⁆ ≤ M :=
  h.commutator_le_y0Of.trans (y0Of_le T Mc M)

theorem Ys_eq : Ys T Mc M = oTwoUpper (⁅Y0s T Mc M, Rcs Mc M⁆ ⊔ Rcs Mc M) := by
  have hsupM : ⁅y0Of T Mc M, rcOf Mc M⁆ ⊔ rcOf Mc M ≤ M :=
    sup_le h.commutator_y0Of_rc_le_M h.rc_le_M
  unfold Ys Y0s Rcs
  rw [h.yOf_eq, imageOTwoQuot_oTwoUpper hsupM,
    imageOTwoQuot_sup h.commutator_y0Of_rc_le_M h.rc_le_M,
    imageOTwoQuot_commutator (y0Of_le T Mc M) h.rc_le_M]

theorem Rcs_isPGroup : IsPGroup 2 (Rcs Mc M) :=
  imageOTwoQuot_isPGroup h.rc_le_M (rc_isPGroup Mc M)

theorem Rcs_le_normalizer_Y0s : Rcs Mc M ≤ Subgroup.normalizer (Y0s T Mc M : Set (OTwoQuot M)) :=
  imageOTwoQuot_le_normalizer h.rc_le_normalizer_y0Of

theorem Y0s_inf_ker :
    Y0s T Mc M ⊓ (piStar h).ker =
      imageOTwoQuot M (y0Of T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
  (imageOTwoQuot_inf_centralizer h).symm

theorem Rcs_centralizes :
    ∀ ρ ∈ Rcs Mc M, ∀ n ∈ Y0s T Mc M ⊓ (piStar h).ker, ρ * n = n * ρ := by
  intro ρ hρ n hn
  rw [Y0s_inf_ker h] at hn
  obtain ⟨c, hcM, hcC, rfl⟩ := mem_imageOTwoQuot_iff.mp hn
  obtain ⟨r, hrM, hrR, rfl⟩ := mem_imageOTwoQuot_iff.mp hρ
  rw [mk_commute_iff]
  have hcomm := Hyp14117.commutator_conjClosure_le h.qtfe h.hyp (y0Of_le T Mc M)
  have hrW : r ∈ conjClosure (pCoreOf 2 (Mc ⊓ M)) (y0Of T Mc M ⊔ T) := le_conjClosure _ _ hrR
  have hcC' : c ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := ⟨hcM, hcC.2⟩
  have h1 := Subgroup.commutator_mem_commutator hcC' hrW
  have h2 : c * r * c⁻¹ * r⁻¹ ∈ pCoreOf 2 M := hcomm h1
  have h3 : r * c * r⁻¹ * c⁻¹ = (c * r * c⁻¹ * r⁻¹)⁻¹ := by group
  show r * c * r⁻¹ * c⁻¹ ∈ pCoreOf 2 M
  rw [h3]
  exact (pCoreOf 2 M).inv_mem h2

theorem Rcs_inf_ker : Rcs Mc M ⊓ (piStar h).ker = ⊥ := by
  rw [Rcs, ← imageOTwoQuot_inf_centralizer h, rcOf, Hyp14117.inf_centralizer_eq h.qtfe h.hyp]
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨x, hxM, hxO, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  rw [Subgroup.mem_bot]
  exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM⟩).mpr hxO

theorem map_Y0s : (Y0s T Mc M).map (piStar h) = oTwoUpper (mBar0 T Mc M) := by
  unfold Y0s
  rw [map_piStar_imageOTwoQuot h (y0Of_le T Mc M), h.autOn_y0Of]

theorem map_Rcs : (Rcs Mc M).map (piStar h) = autOn (rcOf Mc M) (V154 T Mc M) := by
  unfold Rcs
  rw [map_piStar_imageOTwoQuot h h.rc_le_M]

theorem map_Ys : (Ys T Mc M).map (piStar h) = autOn (yOf152 T Mc M) (V154 T Mc M) := by
  unfold Ys
  rw [map_piStar_imageOTwoQuot h h.yOf_le_M]

theorem exists_Rcs_of_mem_autOn {a : MulAut (V154 T Mc M)}
    (ha : a ∈ autOn (rcOf Mc M) (V154 T Mc M)) : ∃ r ∈ Rcs Mc M, piStar h r = a := by
  rw [← h.map_Rcs] at ha
  obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.mp ha
  exact ⟨r, hr, hra⟩

theorem Ys_Rcs_centralize :
    ⁅imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)),
        Ys T Mc M ⊔ Rcs Mc M⁆ = ⊥ :=
  (lemma_14_1_17_three h.qtfe h.hyp (y0Of_le T Mc M)).1

theorem Ys_centralizes_N : ∀ y ∈ Ys T Mc M, ∀ n ∈ Y0s T Mc M ⊓ (piStar h).ker, n * y = y * n := by
  intro y hy n hn
  have hnC : n ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [Y0s_inf_ker h] at hn
    refine imageOTwoQuot_mono ?_ hn
    exact inf_le_inf_right _ (y0Of_le T Mc M)
  have h0 := h.Ys_Rcs_centralize
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
  have := Subgroup.mem_centralizer_iff.mp (h0 hnC) y (Subgroup.mem_sup_left hy)
  exact this.symm

theorem Rcs_centralizes_C : ∀ ρ ∈ Rcs Mc M,
    ∀ n ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)), n * ρ = ρ * n := by
  intro ρ hρ n hn
  have h0 := h.Ys_Rcs_centralize
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
  have := Subgroup.mem_centralizer_iff.mp (h0 hn) ρ (Subgroup.mem_sup_right hρ)
  exact this.symm

theorem Ys_inf_ker_odd : ∀ u ∈ Ys T Mc M ⊓ (piStar h).ker, Odd (orderOf u) := by
  intro u hu
  have hmem : u ∈ imageOTwoQuot M (yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [imageOTwoQuot_inf_centralizer h]
    exact hu
  exact ((lemma_14_1_17_three h.qtfe h.hyp (y0Of_le T Mc M)).2 u hmem).2.1

end Data

theorem yOf_inf_centralizer_le {T Mc M : Subgroup G} (h : Data T Mc M)
    (hK : Ys T Mc M ⊓ (piStar h).ker = ⊥) :
    yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M := by
  intro y hy
  have hyM : y ∈ M := h.yOf_le_M hy.1
  have hu : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := by
    refine ⟨mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hy.1, rfl⟩, ?_⟩
    exact (piStar_mk_eq_one_iff h hyM).mpr hy.2
  rw [hK, Subgroup.mem_bot] at hu
  exact (mk_eq_one_iff_mem_pCoreOf ⟨y, hyM⟩).mp hu

end S152Y

end CFSG.Quasithin
