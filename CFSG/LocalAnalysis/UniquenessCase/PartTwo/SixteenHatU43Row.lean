module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.HardMathSupport.Timmesfeld.LieRank.U43
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.EmptyFaithful.Insp9QS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_false_of_hat_u43_component
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hS : ∃ S : Type, ∃ _ : Group S,
      CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥(lBar V₀ V hV L) S) : False := by
  classical
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  obtain ⟨S, hGrp, hLie, hHat⟩ := hS
  letI := hGrp
  obtain ⟨K, hK, hbarK⟩ :=
    exists_calC_cover_of_component h125 c.std.h127 c.std.h119 hcomp
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 h125
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCq : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  haveI hCperf : Group.IsPerfect ↥C := ⟨hCq.1⟩
  have hCmap : C.map ψ = lBar V₀ V hV L :=
    barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  let f : ↥C →* ↥(lBar V₀ V hV L) :=
    (ψ.comp C.subtype).codRestrict (lBar V₀ V hV L) (fun c => by
      have hc : ψ (c : Bar2 D.M) ∈ C.map ψ := Subgroup.mem_map_of_mem ψ c.2
      rwa [hCmap] at hc)
  have hf : Function.Surjective f := by
    rintro ⟨h, hh⟩
    have hh' : h ∈ C.map ψ := by rw [hCmap]; exact hh
    obtain ⟨c, hc, hcψ⟩ := Subgroup.mem_map.1 hh'
    exact ⟨⟨c, hc⟩, Subtype.ext hcψ⟩
  have hNnormal : ((Subgroup.center ↥(lBar V₀ V hV L)).comap f).Normal :=
    Subgroup.normal_comap f
  have hNproper : (Subgroup.center ↥(lBar V₀ V hV L)).comap f ≠ ⊤ := by
    intro htop
    have hct : Subgroup.center ↥(lBar V₀ V hV L) = ⊤ := by
      have hmap := congrArg (Subgroup.map f) htop
      rwa [Subgroup.map_comap_eq_self_of_surjective hf,
        Subgroup.map_top_of_surjective f hf] at hmap
    exact CFSG.Quasithin.Insp9.qs_center_ne_top hHat.1 hct
  haveI := hNnormal
  have hNle : (Subgroup.center ↥(lBar V₀ V hV L)).comap f ≤ Subgroup.center ↥C :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hCq _ hNproper
  have hker_le : f.ker ≤ Subgroup.center ↥C := by
    intro x hx
    apply hNle
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact Subgroup.one_mem _
  have hcenterC : (Subgroup.center ↥(lBar V₀ V hV L)).comap f =
      Subgroup.center ↥C :=
    CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel f hf hker_le
  have hcenter_map : (Subgroup.center ↥C).map f =
      Subgroup.center ↥(lBar V₀ V hV L) := by
    rw [← hcenterC, Subgroup.map_comap_eq_self_of_surjective hf]
  have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥C) := by
    have h3 : 3 ∣ Nat.card ((Subgroup.center ↥C).map f) := by
      simp [hcenter_map, hHat.2.1]
    exact h3.trans (Subgroup.card_map_dvd (H := Subgroup.center ↥C) f)
  let eH : ↥(lBar V₀ V hV L) ⧸ Subgroup.center ↥(lBar V₀ V hV L) ≃* S := hHat.2.2.some
  let eS : S ≃* CFSG.LieType.Multipliers.U43.X₀ :=
    (CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hLie).some
  let g : ↥(lBar V₀ V hV L) →* CFSG.LieType.Multipliers.U43.X₀ :=
    (eH.trans eS).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥(lBar V₀ V hV L)))
  let φ : ↥C →* CFSG.LieType.Multipliers.U43.X₀ := g.comp f
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, rfl⟩ := (eH.trans eS).surjective x
    obtain ⟨z, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar V₀ V hV L)) y
    exact ⟨z, rfl⟩
  have hφ : Function.Surjective φ := hg.comp hf
  have hker_g : g.ker = Subgroup.center ↥(lBar V₀ V hV L) := by
    change ((eH.trans eS).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥(lBar V₀ V hV L)))).ker = _
    rw [MonoidHom.ker_comp_of_injective
      (f := QuotientGroup.mk' (Subgroup.center ↥(lBar V₀ V hV L)))
      (g := (eH.trans eS).toMonoidHom) (eH.trans eS).injective,
      QuotientGroup.ker_mk']
  have hker : φ.ker = Subgroup.center ↥C := by
    change (g.comp f).ker = _
    rw [← MonoidHom.comap_ker g f, hker_g, hcenterC]
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥C)) 3 h3dvd
  have hzC : orderOf (z : ↥C) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hz3 : (z : ↥C) ^ 3 = 1 := by
    rw [← hzC]
    exact pow_orderOf_eq_one (z : ↥C)
  let Z : Subgroup ↥C := Subgroup.zpowers (z : ↥C)
  have hZk : Z ≤ φ.ker := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr z.2
  have hZexp : ∀ w ∈ Z, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hZcard : 3 ≤ Nat.card Z := by
    rw [Nat.card_zpowers, hzC]
  have h5 : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) :=
    CFSG.HardMathSupport.Timmesfeld.LieRank.five_le_pRank_of_cover
      φ hφ hker.le hZk hZexp hZcard
  have h5C : 5 ≤ CFSG.Open.pRank 3 C := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C] at h5
  have h5top : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    h5C.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top)
  have hbar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) =
      CFSG.Open.pRank 3 D.M :=
    (CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M).symm
  rw [hbar] at h5top
  have hle : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
