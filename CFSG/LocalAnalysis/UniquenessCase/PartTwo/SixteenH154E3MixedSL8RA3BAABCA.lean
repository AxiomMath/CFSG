module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionKernelCardinality
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl28_autSub_setup {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
      (FFModel.nat (StatedSL 2 K)).Realizes (autSub L (commSub ⊤ L)) ⊤
        (fixV (autSub L (commSub ⊤ L))) ∧
      commSub ⊤ (autSub L (commSub ⊤ L)) = ⊤ := by
  classical
  obtain ⟨-, hNat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hNat
  obtain ⟨π, hπ⟩ := hreal
  have hreal' : (FFModel.nat (StatedSL 2 K)).Realizes L (commSub ⊤ L)
      (commSub ⊤ L ⊓ fixV L) := ⟨π, hπ⟩
  refine ⟨K, hKf, hKfin, ?_, ?_, ?_⟩
  · rw [hKcard]; norm_num
  · have hLU : L ≤ stabSub (commSub ⊤ L) := by
      rw [← CFSG.Quasithin.commV_eq_commSub L]
      exact CFSG.Quasithin.le_stabSub_commV_self L
    have hfix : (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) =
        fixV (autSub L (commSub ⊤ L)) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [mem_fixV_autSub]
        intro g hg _
        exact mem_fixV.mp hx.2 g hg
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact ⟨x.2, mem_fixV.mpr fun g hg => mem_fixV_autSub.mp hx g hg (hLU hg)⟩
    have h0 := s16h_realizes_autSub (V := W) (D := FFModel.nat (StatedSL 2 K))
      (H := L) (U := commSub ⊤ L) (I := commSub ⊤ L)
      (Z := commSub ⊤ L ⊓ fixV L) hLU le_rfl inf_le_left hreal'
    rw [Subgroup.subgroupOf_self] at h0
    rwa [hfix] at h0
  · have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
    haveI : Group.IsPerfect (FFModel.nat (StatedSL 2 K)).Gam :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
    have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := π) hπ.1
    have hLU : L ≤ stabSub (commSub ⊤ L) := by
      rw [← CFSG.Quasithin.commV_eq_commSub L]
      exact CFSG.Quasithin.le_stabSub_commV_self L
    have hLU' : ∀ l ∈ L, ∀ w ∈ commSub ⊤ L, l w ∈ commSub ⊤ L :=
      fun l hl w hw => ((mem_stabSub.mp (hLU hl)) w).2 hw
    have hcommU : commSub (commSub ⊤ L) L = commSub ⊤ L :=
      s16jp_commSub_commSub hperf (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))
    have htop : (⊤ : Subgroup ↥(commSub ⊤ L)).map (commSub ⊤ L).subtype = commSub ⊤ L := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hgen : ∀ l (hl : l ∈ L), ∀ w : ↥(commSub ⊤ L),
        (⟨l (w : W) * (w : W)⁻¹,
          (commSub ⊤ L).mul_mem (hLU' l hl w w.2) ((commSub ⊤ L).inv_mem w.2)⟩ :
            ↥(commSub ⊤ L)) ∈
          commSub ⊤ (autSub L (commSub ⊤ L)) := by
      intro l hl w
      exact Subgroup.subset_closure ⟨resHom (commSub ⊤ L) ⟨l, hLU hl⟩,
        mem_autSub.mpr ⟨⟨l, hLU hl⟩, hl, rfl⟩, w, Subgroup.mem_top w, by
          apply Subtype.ext
          rfl⟩
    have hle' : commSub (commSub ⊤ L) L ≤
        (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype := by
      show Subgroup.closure {c | ∃ x ∈ L, ∃ w ∈ commSub ⊤ L, x w * w⁻¹ = c} ≤ _
      rw [Subgroup.closure_le]
      rintro c ⟨l, hl, w, hw, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨l w * w⁻¹,
        (commSub ⊤ L).mul_mem (hLU' l hl w hw) ((commSub ⊤ L).inv_mem hw)⟩,
        hgen l hl ⟨w, hw⟩, rfl⟩
    have hmap : (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype =
        commSub ⊤ L := by
      refine le_antisymm ?_ ?_
      · calc (commSub ⊤ (autSub L (commSub ⊤ L))).map (commSub ⊤ L).subtype
            ≤ (⊤ : Subgroup ↥(commSub ⊤ L)).map (commSub ⊤ L).subtype := Subgroup.map_mono le_top
          _ = commSub ⊤ L := htop
      · exact (le_of_eq hcommU.symm).trans hle'
    refine Subgroup.map_injective (commSub ⊤ L).subtype_injective ?_
    rw [hmap, htop]

theorem s16h_sl28_autSub_le_centralizer {L : Subgroup (MulAut W)} :
    autSub (Subgroup.centralizer (L : Set (MulAut W))) (commSub ⊤ L) ≤
      Subgroup.centralizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨g, hg, hgx⟩ := mem_autSub.mp hx
  obtain ⟨l, hl, hly⟩ := mem_autSub.mp hy
  have hgl : (l : MulAut W) * (g : MulAut W) = (g : MulAut W) * (l : MulAut W) :=
    Subgroup.mem_centralizer_iff.mp hg (l : MulAut W) hl
  have hstab : l * g = g * l := Subtype.ext hgl
  calc y * x = resHom (commSub ⊤ L) l * resHom (commSub ⊤ L) g := by rw [← hly, ← hgx]
    _ = resHom (commSub ⊤ L) (l * g) := (map_mul _ _ _).symm
    _ = resHom (commSub ⊤ L) (g * l) := by rw [hstab]
    _ = resHom (commSub ⊤ L) g * resHom (commSub ⊤ L) l := map_mul _ _ _
    _ = x * y := by rw [hgx, hly]

theorem s16h_sl28_autSub_card_dvd_of_setup {L : Subgroup (MulAut W)} {K : Type}
    [Field K] [Finite K] (hKcard : Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (autSub L (commSub ⊤ L)) ⊤
      (fixV (autSub L (commSub ⊤ L))))
    (hcomm : commSub ⊤ (autSub L (commSub ⊤ L)) = ⊤) :
    Nat.card ↥(autSub (Subgroup.centralizer (L : Set (MulAut W))) (commSub ⊤ L)) ∣ 7 := by
  classical
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat (StatedSL 2 K)) hπ
  obtain ⟨χ, hχinj, -⟩ := exists_scalar_hom_of_isCoord (D := FFModel.nat (StatedSL 2 K))
    (LM := KGNat.linModelNat (StatedSL 2 K)) hf hcomm
    (fun T hT => KGNat.commutant_statedSL (n := 2) (by norm_num) T hT)
  let A : Subgroup (MulAut W) := Subgroup.centralizer (L : Set (MulAut W))
  let H : Subgroup (MulAut ↥(commSub ⊤ L)) := autSub L (commSub ⊤ L)
  have hle : autSub A (commSub ⊤ L) ≤ Subgroup.centralizer (H : Set (MulAut ↥(commSub ⊤ L))) :=
    s16h_sl28_autSub_le_centralizer
  let ι : ↥(autSub A (commSub ⊤ L)) →*
      ↥(Subgroup.centralizer (H : Set (MulAut ↥(commSub ⊤ L)))) := Subgroup.inclusion hle
  have hinj : Function.Injective (χ.comp ι) := hχinj.comp (Subgroup.inclusion_injective hle)
  have hdvd : Nat.card ↥(autSub A (commSub ⊤ L)) ∣ Nat.card Kˣ :=
    Subgroup.card_dvd_of_injective (χ.comp ι) hinj
  rw [Nat.card_units, hKcard] at hdvd
  simpa using hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
