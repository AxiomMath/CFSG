module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ul
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rad118 (D : Data G) : Subgroup G :=
  barPreimage D.M (centralizer
    ((((CFSG.fittingSubgroup ↥(barImage D.M (D.M ⊓ centralizer (D.U : Set G)))).map
        (barImage D.M (D.M ⊓ centralizer (D.U : Set G))).subtype) ⊔
      ((CFSG.layer ↥(barImage D.M (D.M ⊓ centralizer (D.U : Set G)))).map
        (barImage D.M (D.M ⊓ centralizer (D.U : Set G))).subtype) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)))

namespace P22k2

abbrev cStar (D : Data G) : Subgroup (Bar2 D.M) :=
  barImage D.M (D.M ⊓ centralizer (D.U : Set G))

noncomputable abbrev fStar (D : Data G) : Subgroup (Bar2 D.M) :=
  ((CFSG.fittingSubgroup ↥(cStar D)).map (cStar D).subtype) ⊔ ((CFSG.layer ↥(cStar D)).map (cStar D).subtype)

theorem cStar_normal (D : Data G) : (cStar D).Normal :=
  uc22p22u_barImage_normal (uc22p22u_normalizes_cent (P22x.uc22p22xf_hV D))

theorem layer_cStar_normal (D : Data G) : ((CFSG.layer ↥(cStar D)).map (cStar D).subtype).Normal := by
  haveI := cStar_normal D
  haveI : (CFSG.layer ↥(cStar D)).Characteristic := CFSG.LocalCores.layer_characteristic
  infer_instance

theorem fStar_normal (D : Data G) : (fStar D).Normal := by
  haveI := cStar_normal D
  haveI := layer_cStar_normal D
  haveI : ((CFSG.fittingSubgroup ↥(cStar D)).map (cStar D).subtype).Normal := inferInstance
  exact Subgroup.sup_normal _ _

theorem centralizer_fStar_normal (D : Data G) : (centralizer (fStar D : Set (Bar2 D.M))).Normal := by
  haveI := fStar_normal D
  exact uc22p21c_normal_centralizer (fStar D)

end P22k2

open P22k2

theorem rad118_le_M (D : Data G) : rad118 D ≤ D.M := uc22p21c_barPreimage_le _ _

theorem pCoreOf_le_rad118 (D : Data G) : pCoreOf 2 D.M ≤ rad118 D := by
  intro x hx
  obtain ⟨m, hm, hmx⟩ := hx
  have hxM : x ∈ D.M := hmx ▸ m.2
  refine uc22p21c_mem_barPreimage.2 ⟨hxM, ?_⟩
  have h1 : uc22p21cPi D.M m = 1 := (QuotientGroup.eq_one_iff m).2 hm
  have h2 : (⟨x, hxM⟩ : ↥D.M) = m := Subtype.ext hmx.symm
  rw [h2, h1]
  exact one_mem _

theorem M_le_normalizer_rad118 (D : Data G) : D.M ≤ normalizer (rad118 D : Set G) := by
  haveI := centralizer_fStar_normal D
  exact uc22p22u_barPreimage_normalizes

theorem rad118_centr (D : Data G) {x r : G} (hx : x ∈ rad118 D) (hxC : x ∈ centralizer (D.U : Set G))
    (hr : r ∈ rad118 D) : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 D.M := by
  obtain ⟨hxM, hxF⟩ := uc22p21c_mem_barPreimage.1 hx
  obtain ⟨hrM, hrF⟩ := uc22p21c_mem_barPreimage.1 hr
  have hxN : uc22p21cPi D.M ⟨x, hxM⟩ ∈ cStar D :=
    uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, ⟨hxM, hxC⟩, rfl⟩
  have hxFs : uc22p21cPi D.M ⟨x, hxM⟩ ∈ fStar D :=
    uc22p22u_inf_centralizer_fstar_le (cStar D) ⟨hxN, hxF⟩
  have hcomm : uc22p21cPi D.M ⟨x, hxM⟩ * uc22p21cPi D.M ⟨r, hrM⟩ =
      uc22p21cPi D.M ⟨r, hrM⟩ * uc22p21cPi D.M ⟨x, hxM⟩ :=
    Subgroup.mem_centralizer_iff.1 hrF _ hxFs
  have h1 : ⁅(⟨x, hxM⟩ : ↥D.M), ⟨r, hrM⟩⁆ ∈ CFSG.pCore 2 ↥D.M := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi D.M _ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  exact ⟨_, h1, rfl⟩

theorem rad118_lift (D : Data G) (h118U : C118 D ⊥ D.U) :
    ∀ y ∈ ⁅D.M, D.M⁆, ∃ r ∈ rad118 D, ∃ c ∈ D.M ⊓ centralizer (D.U : Set G), y = r * c := by
  intro y hy
  haveI := layer_cStar_normal D
  have h118 : ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ ≤
      centralizer (fStar D : Set (Bar2 D.M)) ⊔ (CFSG.layer ↥(cStar D)).map (cStar D).subtype := by
    unfold C118 at h118U
    rwa [uc22p22u_cTilde_bot] at h118U
  have hcomm : ⁅D.M, D.M⁆ = (⁅(⊤ : Subgroup ↥D.M), (⊤ : Subgroup ↥D.M)⁆).map D.M.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [hcomm] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hπy : uc22p21cPi D.M y' ∈ ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ := by
    have h1 : (⁅(⊤ : Subgroup ↥D.M), (⊤ : Subgroup ↥D.M)⁆).map (uc22p21cPi D.M) ≤
        ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h1 ⟨y', hy', rfl⟩
  obtain ⟨c', hc', e', he', hce⟩ := Subgroup.mem_sup_of_normal_right.1 (h118 hπy)
  obtain ⟨r, rfl⟩ := uc22p21c_pi_surjective D.M c'
  obtain ⟨c₀, hc₀, hπc₀⟩ := uc22p21c_mem_barImage.1 (Subgroup.map_subtype_le _ he')
  obtain ⟨q, hq⟩ : ∃ q : ↥D.M, q = (r * c₀)⁻¹ * y' := ⟨_, rfl⟩
  have hqmem : q ∈ CFSG.pCore 2 ↥D.M := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi D.M q = 1
    rw [hq, map_mul, map_inv, map_mul, hπc₀, hce, inv_mul_cancel]
  have hq1 : uc22p21cPi D.M q = 1 := (QuotientGroup.eq_one_iff q).2 hqmem
  have hrr : ((r * q : ↥D.M) : G) ∈ rad118 D := by
    refine uc22p21c_mem_barPreimage.2 ⟨(r * q).2, ?_⟩
    change uc22p21cPi D.M (r * q) ∈ _
    rw [map_mul, hq1, mul_one]
    exact hc'
  have hnorm : D.M ≤ normalizer ((D.M ⊓ centralizer (D.U : Set G) : Subgroup G) : Set G) :=
    uc22p22u_normalizes_cent (P22x.uc22p22xf_hV D)
  have hcc : ((q⁻¹ * c₀ * q : ↥D.M) : G) ∈ D.M ⊓ centralizer (D.U : Set G) := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hnorm (q⁻¹ : ↥D.M).2) (c₀ : G)).1 hc₀
    simpa [mul_assoc] using h1
  have hy'eq : y' = (r * q) * (q⁻¹ * c₀ * q) := by
    rw [hq]
    group
  exact ⟨_, hrr, _, hcc, congrArg (fun z : ↥D.M => (z : G)) hy'eq⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
