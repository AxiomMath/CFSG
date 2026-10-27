module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.D216Restrict
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

private theorem s16h_mem_stabSub_of_mem_normalizer {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hgu
    have hg' : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hg
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b (X := L) (g := g⁻¹)
        (fun x hx => (Subgroup.mem_normalizer_iff.mp hg' x).mp hx) (g u) hgu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b (X := L) (g := g)
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx) u hu

private theorem s16h_le_stabSub_commSub_top {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (commSub ⊤ L) :=
  fun l hl => s16h_mem_stabSub_of_mem_normalizer (Subgroup.le_normalizer hl)

private theorem s16h_map_subtype_mem_irrSet {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U : Subgroup W} (hLU : L ≤ stabSub U)
    {J : Subgroup U} (hJ : J ∈ irrSet (autSub L U)) :
    J.map U.subtype ∈ irrSet L := by
  set I : Subgroup W := J.map U.subtype with hI
  rw [irrSet, Set.mem_setOf_eq] at hJ
  obtain ⟨hJcomm, hJIrr⟩ := hJ
  rw [IsIrrOn] at hJIrr
  obtain ⟨hJlt, hJstab, hJNstab, hJmax⟩ := hJIrr
  have hIU : I ≤ U := by
    rw [hI]
    exact Subgroup.map_subtype_le J
  have hm : (J ⊓ fixV (autSub L U)).map U.subtype = I ⊓ fixV L := by
    rw [hI]
    rw [Subgroup.map_inf_eq J (fixV (autSub L U)) U.subtype U.subtype_injective,
      map_subtype_fixV_autSub hLU, ← inf_assoc,
      inf_eq_left.mpr (Subgroup.map_subtype_le J)]
  have hIstab : StableUnder L I := by
    rw [hI]
    intro g hgL u hu
    rcases Subgroup.mem_map.mp hu with ⟨j, hj, rfl⟩
    exact Subgroup.mem_map.mpr ⟨resHom U ⟨g, hLU hgL⟩ j,
      hJstab _ (mem_autSub.mpr ⟨⟨g, hLU hgL⟩, hgL, rfl⟩) j hj,
      resHom_apply U ⟨g, hLU hgL⟩ j⟩
  have hIfixstab : StableUnder L (I ⊓ fixV L) :=
    stableUnder_inf hIstab (stableUnder_fixV fun y hy h hh =>
      L.mul_mem (L.mul_mem hy hh) (L.inv_mem hy))
  have hIlt : I ⊓ fixV L < I := by
    rw [← hm, hI]
    exact (Subgroup.map_lt_map_iff_of_injective U.subtype_injective).mpr hJlt
  refine ⟨?_, ?_⟩
  · rw [hI]
    rw [commSub_map_subtype hLU J, hJcomm]
  · refine ⟨hIlt, hIstab, hIfixstab, ?_⟩
    intro K hKstab hIK hKI
    have hKU : K ≤ U := hKI.trans (Subgroup.map_subtype_le J)
    let K' : Subgroup U := K.subgroupOf U
    have hKmap : K'.map U.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKU
    have hfixsub : (I ⊓ fixV L).subgroupOf U = J ⊓ fixV (autSub L U) := by
      apply Subgroup.map_injective U.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hIU)]
      exact hm.symm
    have hK'stab : StableUnder (autSub L U) K' := by
      intro φ hφ k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      rw [resHom_apply]
      exact hKstab g hg k hk
    have hJsub : (J.map U.subtype).subgroupOf U = J := by
      apply Subgroup.map_injective U.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le J)]
    have hJK' : J ⊓ fixV (autSub L U) ≤ K' := by
      rw [← hfixsub]
      exact Subgroup.subgroupOf_mono U hIK
    have hK'J : K' ≤ J := by
      have hle : K' ≤ (J.map U.subtype).subgroupOf U := Subgroup.subgroupOf_mono U hKI
      rw [hJsub] at hle
      exact hle
    rcases hJmax K' hK'stab hJK' hK'J with hK' | hK'
    · left
      rw [← hKmap, hK', hm]
    · right
      rw [← hKmap, hK']

theorem s16h_L3_res_trans {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    (hk : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    ∀ J₁ ∈ irrSet (autSub L (commSub ⊤ L)), ∀ J₂ ∈ irrSet (autSub L (commSub ⊤ L)),
      ∃ g ∈ autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L),
        J₂ = J₁.map g.toMonoidHom := by
  intro J₁ hJ₁ J₂ hJ₂
  have hLU : L ≤ stabSub (commSub ⊤ L) := s16h_le_stabSub_commSub_top L
  have hI₁ : J₁.map (commSub ⊤ L).subtype ∈ irrSet L :=
    s16h_map_subtype_mem_irrSet hLU hJ₁
  have hI₂ : J₂.map (commSub ⊤ L).subtype ∈ irrSet L :=
    s16h_map_subtype_mem_irrSet hLU hJ₂
  obtain ⟨g, hg, hgeq⟩ := hk (J₁.map (commSub ⊤ L).subtype) hI₁
    (J₂.map (commSub ⊤ L).subtype) hI₂
  have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
  have hgU : g ∈ stabSub (commSub ⊤ L) := s16h_mem_stabSub_of_mem_normalizer hgN
  refine ⟨resHom (commSub ⊤ L) ⟨g, hgU⟩,
    mem_autSub.mpr ⟨⟨g, hgU⟩, hg, rfl⟩, ?_⟩
  have hcomp : (commSub ⊤ L).subtype.comp
        (resHom (commSub ⊤ L) ⟨g, hgU⟩).toMonoidHom =
      g.toMonoidHom.comp (commSub ⊤ L).subtype := by
    ext j
    simp only [MonoidHom.comp_apply]
    exact resHom_apply (commSub ⊤ L) ⟨g, hgU⟩ j
  apply Subgroup.map_injective (commSub ⊤ L).subtype_injective
  show (J₂.map (commSub ⊤ L).subtype) =
    (J₁.map (resHom (commSub ⊤ L) ⟨g, hgU⟩).toMonoidHom).map (commSub ⊤ L).subtype
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact hgeq

theorem s16h_trans_of_commSub_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : commSub ⊤ L ∈ irrSet L) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
  have hU' : commSub (commSub ⊤ L) L = commSub ⊤ L ∧
      IsIrrOn L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) := by
    simpa only [irrSet, Set.mem_setOf_eq] using h
  obtain ⟨hUcomm, hUirr⟩ := hU'
  rw [IsIrrOn] at hUirr
  obtain ⟨hZU, hstU, hstZ, hmax⟩ := hUirr
  have key : ∀ I ∈ irrSet L, I = commSub ⊤ L := by
    intro I hI
    have hI' : commSub I L = I ∧ IsIrrOn L I (I ⊓ fixV L) := by
      simpa only [irrSet, Set.mem_setOf_eq] using hI
    obtain ⟨hIcomm, hIirr⟩ := hI'
    rw [IsIrrOn] at hIirr
    obtain ⟨hIlt, hIstab, hIinfstab, hImax⟩ := hIirr
    have hIleU : I ≤ commSub ⊤ L := by
      rw [← hIcomm]
      exact commSub_mono le_top le_rfl
    have hKstab : StableUnder L (I ⊔ (commSub ⊤ L ⊓ fixV L)) :=
      stableUnder_sup hIstab hstZ
    have hKleU : I ⊔ (commSub ⊤ L ⊓ fixV L) ≤ commSub ⊤ L :=
      sup_le hIleU inf_le_left
    rcases hmax (I ⊔ (commSub ⊤ L ⊓ fixV L)) hKstab le_sup_right hKleU with hK | hK
    · have hIZ : I ≤ commSub ⊤ L ⊓ fixV L := sup_eq_right.mp hK
      exact absurd (hIZ.trans inf_le_right) (not_le_fixV_of_mem_irrSet hI)
    · have hcomm : commSub (I ⊔ (commSub ⊤ L ⊓ fixV L)) L = I := by
        rw [commSub_sup_left, hIcomm,
          (commSub_eq_bot_iff.mpr inf_le_right :
            commSub (commSub ⊤ L ⊓ fixV L) L = ⊥), sup_bot_eq]
      rw [hK, hUcomm] at hcomm
      exact hcomm.symm
  intro I₁ hI₁ I₂ hI₂
  refine ⟨1, by simp, ?_⟩
  rw [key I₁ hI₁, key I₂ hI₂]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by
    ext x
    exact MulAut.one_apply W x
  rw [hone, Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
