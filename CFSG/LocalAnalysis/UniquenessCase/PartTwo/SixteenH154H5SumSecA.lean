module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

@[expose] def s16h_secIncl (Z I U : Subgroup W) (hIU : I ≤ U) : Sec I Z →* Sec U Z :=
  QuotientGroup.quotientMapSubgroupOfOfLe (le_refl Z) hIU

theorem s16h_secIncl_mk (Z I U : Subgroup W) (hIU : I ≤ U) (x : ↥I) :
    s16h_secIncl Z I U hIU (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hIU x) :=
  rfl

theorem s16h_secIncl_injective (Z I U : Subgroup W) (hIU : I ≤ U) :
    Function.Injective (s16h_secIncl Z I U hIU) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MonoidHom.mem_ker, s16h_secIncl_mk] at hx
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    have h1 := (QuotientGroup.eq_one_iff (Subgroup.inclusion hIU a)).mp hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1)

theorem s16h_secIncl_range (Z I U : Subgroup W) (hIU : I ≤ U) :
    (s16h_secIncl Z I U hIU).range =
      (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H a =>
      rw [s16h_secIncl_mk]
      exact Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hIU a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨QuotientGroup.mk ⟨u, Subgroup.mem_subgroupOf.mp hu⟩, ?_⟩
    rw [s16h_secIncl_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem s16h_secIncl_secHom {L : Subgroup (MulAut W)} (Z I U : Subgroup W) (hIU : I ≤ U)
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U) (a : ↥L)
    (x : Sec I Z) :
    s16h_secIncl Z I U hIU (CFSG.Quasithin.B5.secHom L hLI hLZ a x) =
      CFSG.Quasithin.B5.secHom L hLU hLZ a (s16h_secIncl Z I U hIU x) := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [s16h_secIncl_mk, CFSG.Quasithin.B5.secHom_mk, CFSG.Quasithin.B5.secHom_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem s16h_le_stabSub_of_stable {L : Subgroup (MulAut W)} {I : Subgroup W}
    (h : StableUnder L I) : L ≤ stabSub I := by
  intro a ha
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h2 : a⁻¹ (a u) ∈ I := h a⁻¹ (L.inv_mem ha) (a u) hu
    simpa using h2
  · intro hu
    exact h a ha u hu

theorem s16h_subgroupOf_iSup {ι : Sort*} {U : Subgroup W} {I : ι → Subgroup W}
    (hI : ∀ i, I i ≤ U) :
    (⨆ i, I i).subgroupOf U = ⨆ i, (I i).subgroupOf U := by
  refine le_antisymm ?_ ?_
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    have key : ∀ (hyU : (u : W) ∈ U),
        (⟨(u : W), hyU⟩ : ↥U) ∈ ⨆ i, (I i).subgroupOf U := by
      refine Subgroup.iSup_induction' I ?_ ?_ ?_ hu
      · intro i x hx hyU
        exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_subgroupOf.mpr hx)
      · intro hyU
        have h : (⟨1, hyU⟩ : ↥U) = 1 := Subtype.ext rfl
        rw [h]
        exact one_mem _
      · intro x y hx hy ihx ihy hxyU
        have hxU : x ∈ U := iSup_le hI hx
        have hyU : y ∈ U := iSup_le hI hy
        have hxy : (⟨x * y, hxyU⟩ : ↥U) = ⟨x, hxU⟩ * ⟨y, hyU⟩ := Subtype.ext rfl
        rw [hxy]
        exact mul_mem (ihx hxU) (ihy hyU)
    simpa using key u.2
  · refine iSup_le fun i => ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (le_iSup I i (Subgroup.mem_subgroupOf.mp hx))

theorem s16h_subgroupOf_iSup_ne {ι : Type*} {U : Subgroup W} {I : ι → Subgroup W}
    (hI : ∀ j, I j ≤ U) (i : ι) :
    (⨆ (j : ι) (_ : j ≠ i), I j).subgroupOf U = ⨆ (j : ι) (_ : j ≠ i),
      (I j).subgroupOf U := by
  rw [iSup_subtype', iSup_subtype']
  exact s16h_subgroupOf_iSup fun j => hI j.val

theorem s16h_mem_autSec_range {L : Subgroup (MulAut W)} {Z U : Subgroup W}
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) {g : MulAut (Sec U Z)} :
    g ∈ autSec L U Z ↔ ∃ a : ↥L, CFSG.Quasithin.B5.secHom L hLU hLZ a = g := by
  rw [← CFSG.Quasithin.B5.map_secHom_eq_autSec L hLU hLZ (le_refl L),
    Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.mem_range]

theorem s16h_secIncl_image_stable {L : Subgroup (MulAut W)} (Z I U : Subgroup W)
    (hIU : I ≤ U) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U) :
    ∀ g ∈ autSec L U Z, ∀ x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)),
      g x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  intro g hg x hx
  obtain ⟨a, rfl⟩ := (s16h_mem_autSec_range hLU hLZ).mp hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  have huI : (u : W) ∈ I := Subgroup.mem_subgroupOf.mp hu
  have haU : (a : MulAut W) (u : W) ∈ U := (hLU a.2 (u : W)).2 u.2
  have haI : (a : MulAut W) (u : W) ∈ I := (hLI a.2 (u : W)).2 huI
  rw [show QuotientGroup.mk' (Z.subgroupOf U) u = QuotientGroup.mk u from rfl,
    CFSG.Quasithin.B5.secHom_mk]
  exact Subgroup.mem_map.mpr ⟨⟨_, haU⟩, Subgroup.mem_subgroupOf.mpr haI, rfl⟩

theorem s16h_secIncl_comap_map_eq {Z I U : Subgroup W} (hZI : Z ≤ I) (hIU : I ≤ U) :
    ((I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))).comap
        (QuotientGroup.mk' (Z.subgroupOf U)) = I.subgroupOf U := by
  refine Subgroup.comap_map_eq_self ?_
  rw [QuotientGroup.ker_mk']
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (hZI (Subgroup.mem_subgroupOf.mp hx))

theorem s16h_secIncl_simple {L : Subgroup (MulAut W)} (Z I U : Subgroup W)
    (hZI : Z ≤ I) (hIU : I ≤ U) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLU : L ≤ stabSub U) (hirr : IsIrrOn L I Z) :
    ∀ J : Subgroup (Sec U Z),
      (∀ g ∈ autSec L U Z, ∀ x ∈ J, g x ∈ J) →
      J ≤ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) →
      J = ⊥ ∨ J = (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  intro J hJstab hJle
  set J₀ : Subgroup W := (J.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype with hJ₀
  have hJ₀_le : J₀ ≤ I := by
    rw [hJ₀]
    have h1 : J.comap (QuotientGroup.mk' (Z.subgroupOf U)) ≤ I.subgroupOf U :=
      (Subgroup.comap_mono hJle).trans (le_of_eq (s16h_secIncl_comap_map_eq hZI hIU))
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_subgroupOf.mp (h1 hu)
  have hZJ₀ : Z ≤ J₀ := by
    intro z hz
    rw [hJ₀]
    refine Subgroup.mem_map.mpr ⟨⟨z, hIU (hZI hz)⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (Z.subgroupOf U) ⟨z, hIU (hZI hz)⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨z, hIU (hZI hz)⟩ : ↥U)).mpr (Subgroup.mem_subgroupOf.mpr hz)
    rw [h1]
    exact J.one_mem
  have hStabJ₀ : StableUnder L J₀ := by
    intro a ha w hw
    rw [hJ₀] at hw ⊢
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_comap] at hu
    have haU : (a : MulAut W) (u : W) ∈ U := (hLU ha (u : W)).2 u.2
    refine Subgroup.mem_map.mpr ⟨⟨(a : MulAut W) (u : W), haU⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have heq : QuotientGroup.mk' (Z.subgroupOf U) ⟨(a : MulAut W) (u : W), haU⟩ =
        CFSG.Quasithin.B5.secHom L hLU hLZ ⟨a, ha⟩
          (QuotientGroup.mk' (Z.subgroupOf U) u) := by
      rw [show QuotientGroup.mk' (Z.subgroupOf U) u = QuotientGroup.mk u from rfl,
        show QuotientGroup.mk' (Z.subgroupOf U) ⟨(a : MulAut W) (u : W), haU⟩ =
          QuotientGroup.mk ⟨(a : MulAut W) (u : W), haU⟩ from rfl,
        CFSG.Quasithin.B5.secHom_mk]
    rw [heq]
    exact hJstab (CFSG.Quasithin.B5.secHom L hLU hLZ ⟨a, ha⟩)
      ((s16h_mem_autSec_range hLU hLZ).mpr ⟨⟨a, ha⟩, rfl⟩)
      (QuotientGroup.mk' (Z.subgroupOf U) u) hu
  have hcorr : J = (J₀.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, rfl⟩ := (QuotientGroup.mk'_surjective (N := Z.subgroupOf U)) x
      refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      exact hx
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_subgroupOf] at hu
      rw [hJ₀] at hu
      obtain ⟨v, hv, hv_eq⟩ := Subgroup.mem_map.mp hu
      rw [Subgroup.mem_comap] at hv
      have hvu : v = u := Subtype.ext hv_eq
      rw [hvu] at hv
      exact hv
  rcases hirr.2.2.2 J₀ hStabJ₀ hZJ₀ hJ₀_le with hJ₀Z | hJ₀I
  · left
    rw [hcorr, hJ₀Z, Subgroup.map_eq_bot_iff]
    intro x hx
    simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hx
  · right
    rw [hcorr, hJ₀I]

theorem s16h_secIncl_hend {L : Subgroup (MulAut W)} (Z I U : Subgroup W) (hZI : Z ≤ I)
    (hIU : I ≤ U) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hLU : L ≤ stabSub U)
    (hend : ∀ f : Sec I Z →* Sec I Z,
      (∀ g ∈ autSec L I Z, ∀ x, f (g x) = g (f x)) →
      f = 1 ∨ f = MonoidHom.id (Sec I Z))
    (f : Sec U Z →* Sec U Z)
    (hfcomm : ∀ g ∈ autSec L U Z, ∀ x, f (g x) = g (f x))
    (hfmem : ∀ x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)),
      f x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) :
    (∀ x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)), f x = x) ∨
      (∀ x ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)), f x = 1) := by
  let e : Sec I Z ≃* (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) :=
    (MonoidHom.ofInjective (s16h_secIncl_injective Z I U hIU)).trans
      (MulEquiv.subgroupCongr (s16h_secIncl_range Z I U hIU))
  let fI : (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) →*
      (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) :=
    (f.comp (Subgroup.subtype _)).codRestrict _ fun y => hfmem y.1 y.2
  let f' : Sec I Z →* Sec I Z := e.symm.toMonoidHom.comp (fI.comp e.toMonoidHom)
  have he : ∀ y : Sec I Z,
      ((e y : (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) : Sec U Z) =
        s16h_secIncl Z I U hIU y := fun _ => rfl
  have he_symm : ∀ z : (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)),
      s16h_secIncl Z I U hIU (e.symm z) = (z : Sec U Z) := by
    intro z
    rw [show e.symm z = (MonoidHom.ofInjective (s16h_secIncl_injective Z I U hIU)).symm
        ((MulEquiv.subgroupCongr (s16h_secIncl_range Z I U hIU)).symm z) from rfl,
      MonoidHom.apply_ofInjective_symm]
    exact MulEquiv.subgroupCongr_symm_apply _ _
  have hf'_apply : ∀ y : Sec I Z,
      s16h_secIncl Z I U hIU (f' y) = f (s16h_secIncl Z I U hIU y) := by
    intro y
    calc s16h_secIncl Z I U hIU (f' y)
        = s16h_secIncl Z I U hIU (e.symm (fI (e y))) := rfl
      _ = (fI (e y) : Sec U Z) := he_symm (fI (e y))
      _ = f (((e y : (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) : Sec U Z)) := rfl
      _ = f (s16h_secIncl Z I U hIU y) := congrArg f (he y)
  have hf'comm : ∀ g ∈ autSec L I Z, ∀ x, f' (g x) = g (f' x) := by
    intro g hg x
    obtain ⟨a, rfl⟩ := (s16h_mem_autSec_range hLI hLZ).mp hg
    have hmem : CFSG.Quasithin.B5.secHom L hLU hLZ a ∈ autSec L U Z :=
      (s16h_mem_autSec_range hLU hLZ).mpr ⟨a, rfl⟩
    apply s16h_secIncl_injective Z I U hIU
    calc s16h_secIncl Z I U hIU (f' (CFSG.Quasithin.B5.secHom L hLI hLZ a x))
        = f (s16h_secIncl Z I U hIU (CFSG.Quasithin.B5.secHom L hLI hLZ a x)) := hf'_apply _
      _ = f (CFSG.Quasithin.B5.secHom L hLU hLZ a (s16h_secIncl Z I U hIU x)) :=
            congrArg f (s16h_secIncl_secHom Z I U hIU hLI hLZ hLU a x)
      _ = CFSG.Quasithin.B5.secHom L hLU hLZ a (f (s16h_secIncl Z I U hIU x)) := hfcomm _ hmem _
      _ = CFSG.Quasithin.B5.secHom L hLU hLZ a (s16h_secIncl Z I U hIU (f' x)) :=
            congrArg _ (hf'_apply x).symm
      _ = s16h_secIncl Z I U hIU (CFSG.Quasithin.B5.secHom L hLI hLZ a (f' x)) :=
            (s16h_secIncl_secHom Z I U hIU hLI hLZ hLU a (f' x)).symm
  rcases hend f' hf'comm with h1 | hid
  · right
    intro x hx
    have hx' : x ∈ (s16h_secIncl Z I U hIU).range := by
      rw [s16h_secIncl_range]; exact hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx'
    have hy : f' y = 1 := by rw [h1]; rfl
    simpa [← hf'_apply y, hy]
  · left
    intro x hx
    have hx' : x ∈ (s16h_secIncl Z I U hIU).range := by
      rw [s16h_secIncl_range]; exact hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx'
    have hy : f' y = y := by rw [hid]; rfl
    simpa [← hf'_apply y, hy]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
