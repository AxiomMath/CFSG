module

public import CFSG.RankThree.GF2n.Tim79aRootStatements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem not_commute_VZ_conj (hc : MinCex M V Q P H) {g : ↥(xOf V H)} {u w : G} (hu : u ∈ V)
    (hw : w ∈ conjSubgroup (g : G) V) (huw : ⁅u, w⁆ ∉ wOf V H) :
    ¬ ∀ a ∈ VZ V H, ∀ b ∈ conjSubgroup (xToZ hc.V_le_H g) (VZ V H), a * b = b * a := by
  intro hcomm
  have hc2 := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := g) (by
    intro a ha b hb
    rw [map_one, conjSubgroup_one] at ha
    exact hcomm a ha b hb)
  have h1 : u * w = w * u :=
    hc2 u (by rwa [show ((1 : ↥(xOf V H)) : G) = 1 from rfl, conjSubgroup_one]) w hw
  apply huw
  rw [commutatorElement_eq_one_iff_mul_comm.mpr h1]
  exact (wOf V H).one_mem

theorem exists_Dy_of_commutator (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    {g : ↥(xOf V H)} {u w : G} (hu : u ∈ V) (hw : w ∈ conjSubgroup (g : G) V)
    (huw : ⁅u, w⁆ ∉ wOf V H) :
    ∃ y : Xbar V H, y ∈ Dy V H ∧ (y : Hbar V H) ∈ barOf V H (conjSubgroup (g : G) V) ∧
      projZ V H y ≠ 1 ∧ projZ V H y ∈ conjSubgroup (xToZ hc.V_le_H g) (VZ V H) := by
  have hVH : V ≤ H := hc.V_le_H
  have hgH : (g : G) ∈ H := xOf_le_H hVH g.2
  have huH : u ∈ H := hVH hu
  have hwH : w ∈ H := conjSubgroup_le_of_le_of_mem hVH hgH hw
  have hwX : w ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hgH) hw
  have hwW : w ∉ wOf V H := by
    intro hwW
    apply huw
    have h2 : u * w * u⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H huH) w).mp hwW
    rw [commutatorElement_def]
    exact (wOf V H).mul_mem h2 ((wOf V H).inv_mem hwW)
  have hw1 : w ≠ 1 := fun h => hwW (h ▸ (wOf V H).one_mem)
  set y : Xbar V H := ⟨piBar V H ⟨w, hwH⟩, mem_barOf_iff.mpr ⟨⟨w, hwH⟩, hwX, rfl⟩⟩
  have hyD : y ∈ Dy V H :=
    mem_dbarOf_iff.mpr ⟨⟨w, hwH⟩, ⟨hw1, conjSubgroup (g : G) V, conjSubgroup_mem_omegaOf hgH, hw⟩,
      hwW, rfl⟩
  have hyT : (y : Hbar V H) ∈ barOf V H (conjSubgroup (g : G) V) :=
    mem_barOf_iff.mpr ⟨⟨w, hwH⟩, hw, rfl⟩
  refine ⟨y, hyD, hyT, fun h1 => hd.noncentral y hyD ((QuotientGroup.eq_one_iff _).mp h1), ?_⟩
  rw [← imgZ_conj hc.V_le_H g]
  exact ⟨y, Subgroup.mem_subgroupOf.mpr hyT, rfl⟩

theorem exists_mul_of_Rtilde_sup (hc : MinCex M V Q P H) (hd : Sec23Data V H) {T : Subgroup G}
    (hTH : T ≤ H) {y : Xbar V H} (hyD : y ∈ Dy V H) (hyT : (y : Hbar V H) ∈ barOf V H T)
    (hgen : Rtilde V H P ⊔ Subgroup.zpowers (projZ V H y) = ⊤) :
    ∀ x ∈ xOf V H, ∃ t ∈ (P ⊓ xOf V H) ⊔ T, ∃ w ∈ wOf V H, x = t * w := by
  have hVH : V ≤ H := hc.V_le_H
  set A : Subgroup G := P ⊓ xOf V H
  set K₀ : Subgroup (Xbar V H) :=
    (barOf V H ((wOf V H ⊔ A) ⊔ T)).subgroupOf (barOf V H (xOf V H)) with hK₀
  have hyK₀ : y ∈ K₀ := by
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact barOf_mono le_sup_right hyT
  have hRK : Rbar V H P ≤ K₀ := by
    intro r hr
    obtain ⟨p, hp, hpr⟩ := mem_barOf_iff.mp (mem_Rbar.mp hr)
    obtain ⟨x', hx', hx'r⟩ := mem_barOf_iff.mp r.2
    have h1 : piBar V H (x'⁻¹ * p) = 1 := by
      rw [map_mul, map_inv, hpr, hx'r, inv_mul_cancel]
    have h2 : ((x'⁻¹ * p : ↥H) : G) ∈ wOf V H := (piBar_eq_one_iff _).mp h1
    have hpX : (p : G) ∈ xOf V H := by
      have h3 : (p : G) = (x' : G) * ((x'⁻¹ * p : ↥H) : G) := by simp
      rw [h3]
      exact (xOf V H).mul_mem hx' (wOf_le_xOf V H h2)
    have hpA : (p : G) ∈ (wOf V H ⊔ A) ⊔ T :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hp, hpX⟩))
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact mem_barOf_iff.mpr ⟨p, hpA, hpr⟩
  have hmap : K₀.map (projZ V H) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (Subgroup.map_mono hRK) (Subgroup.zpowers_le.mpr ⟨y, hyK₀, rfl⟩)
  have hker : (projZ V H).ker = Subgroup.center (Xbar V H) := QuotientGroup.ker_mk' _
  have hK : K₀ ⊔ Subgroup.center (Xbar V H) = ⊤ := by
    have h1 := Subgroup.comap_map_eq (projZ V H) K₀
    rw [hmap, Subgroup.comap_top, hker] at h1
    exact h1.symm
  have hXle : xOf V H ≤ (wOf V H ⊔ A) ⊔ T :=
    xOf_le_sup_of_sup_center hd hVH le_sup_left hK ⟨y, hyD, hyK₀⟩
  have hAT : A ⊔ T ≤ Subgroup.normalizer (wOf V H : Set G) :=
    (sup_le (inf_le_left.trans hc.PleH) hTH).trans (H_le_normalizer_wOf V H)
  intro x hx
  have hx' : x ∈ (A ⊔ T) ⊔ wOf V H := by
    have h := hXle hx
    rwa [sup_assoc, sup_comm (wOf V H)] at h
  have hx'' : x ∈ ((A ⊔ T : Subgroup G) : Set G) * (wOf V H : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAT]
    exact hx'
  obtain ⟨t, ht, w, hw, rfl⟩ := Set.mem_mul.mp hx''
  exact ⟨t, ht, w, hw, rfl⟩

end MinCex

theorem exists_mul_of_rootS1Model {M V Q P H : Subgroup G} [Finite G] (hs : Sec23Setup M V Q P H)
    (hR : Sec24bTilde V H P) (hm : RootS1Model (XbarZ V H) (VZ V H)) {g : G} (hg : g ∈ xOf V H)
    (hex : ∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H) :
    ∀ x ∈ xOf V H, ∃ y ∈ (P ⊓ xOf V H) ⊔ conjSubgroup g V, ∃ w ∈ wOf V H, x = y * w := by
  obtain ⟨u, hu, w, hw, huw⟩ := hex
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hd : Sec23Data V H := hs.data
  have hVH : V ≤ H := hc.V_le_H
  have hgH : g ∈ H := xOf_le_H hVH hg
  obtain ⟨y, hyD, hyT, hy1, hyc⟩ := hc.exists_Dy_of_commutator hd (g := ⟨g, hg⟩) hu hw huw
  have hnc := hc.not_commute_VZ_conj (g := ⟨g, hg⟩) hu hw huw
  have hgen : Rtilde V H P ⊔ Subgroup.zpowers (projZ V H y) = ⊤ := by
    rw [hR]
    exact hm (xToZ hc.V_le_H ⟨g, hg⟩) hnc _ hyc hy1
  exact hc.exists_mul_of_Rtilde_sup hd (conjSubgroup_le_of_le_of_mem hVH hgH) hyD hyT hgen

theorem tim79aSec25S1TildeStatement_of_model (hk : RootPairOfKindStatement) (hm : RootS1All) :
    Tim79aSec25S1TildeStatement := by
  intro G _ _ M V Q P H hs hcase hR g hg hex
  exact exists_mul_of_rootS1Model hs hR (hm (XbarZ V H) (VZ V H) (hk G M V Q P H hs hcase)) hg
    hex

end CFSG.RankThree.GF2n.Tim79a
