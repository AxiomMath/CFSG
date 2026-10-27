module

public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.Fischer.Uniq.Graph
import CFSG.OddTranspositions.PartThree.CommSetConjCentralizer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.PartFour.LineStabilizer
public import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Fischer

variable {G : Type} [Group G] {D : Set G}

private theorem lineMem_comm (D : Set G) (v w : G) : lineMem D v w = lineMem D w v := by
  ext x
  rw [mem_lineMem, mem_lineMem]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => h ⟨hy.2, hy.1⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => h ⟨hy.2, hy.1⟩⟩

private theorem self_mem_lineMem {D : Set G} {v w : G} (hv : v ∈ D) : v ∈ lineMem D v w :=
  mem_lineMem.mpr ⟨hv, fun _ hy => hy.1⟩

private theorem right_mem_lineMem {D : Set G} {v w : G} (hw : w ∈ D) : w ∈ lineMem D v w :=
  mem_lineMem.mpr ⟨hw, fun _ hy => hy.2⟩

private theorem lineMem_subset (D : Set G) (v w : G) : lineMem D v w ⊆ D :=
  fun _ hx => (mem_lineMem.mp hx).1

@[expose] def IsHypLineSpace (D : Set G) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, ¬ Commute b a → ∀ c ∈ lineMem D a b, c ≠ a →
    ¬ Commute c a ∧ lineMem D a c = lineMem D a b

theorem IsHypLineSpace.lineMem_eq (hL : IsHypLineSpace D) {a b c c' : G} (ha : a ∈ D)
    (hb : b ∈ D) (hab : ¬ Commute b a) (hc : c ∈ lineMem D a b) (hc' : c' ∈ lineMem D a b)
    (hcc' : c' ≠ c) : ¬ Commute c' c ∧ lineMem D c c' = lineMem D a b := by
  by_cases hca : c = a
  · have hc'a : c' ≠ a := by rwa [hca] at hcc'
    rw [hca]
    exact hL a ha b hb hab c' hc' hc'a
  · by_cases hc'a : c' = a
    · have h := hL a ha b hb hab c hc hca
      rw [hc'a]
      refine ⟨fun hcomm => h.1 hcomm.symm, ?_⟩
      rw [lineMem_comm D c a]
      exact h.2
    · have hcD : c ∈ D := lineMem_subset D a b hc
      have h := hL a ha b hb hab c hc hca
      have hac : ¬ Commute a c := fun hcomm => h.1 hcomm.symm
      have hc'_ac : c' ∈ lineMem D a c := by rw [h.2]; exact hc'
      have hc'_ca : c' ∈ lineMem D c a := by rw [lineMem_comm D c a]; exact hc'_ac
      have h2 := hL c hcD a ha hac c' hc'_ca hcc'
      refine ⟨h2.1, ?_⟩
      rw [h2.2, lineMem_comm D c a]
      exact h.2

theorem IsHypLineSpace.commSet_inter_eq (hL : IsHypLineSpace D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) (hab : ¬ Commute b a) {x : G} (hx : x ∈ lineMem D a b) (hxa : x ≠ a) :
    commSet D a ∩ commSet D x = commSet D a ∩ commSet D b := by
  obtain ⟨hxa', hline⟩ := hL a ha b hb hab x hx hxa
  have hb_line : b ∈ lineMem D a x := by
    rw [hline]
    exact right_mem_lineMem hb
  have hbperp : perpMem D a ∩ perpMem D x ⊆ perpMem D b := (mem_lineMem.mp hb_line).2
  have hxperp : perpMem D a ∩ perpMem D b ⊆ perpMem D x := (mem_lineMem.mp hx).2
  ext y
  constructor
  · rintro ⟨hya, hyx⟩
    have hyD : y ∈ D := hya.1
    have hyb : y ∈ perpMem D b := hbperp ⟨⟨hyD, hya.2.1⟩, ⟨hyD, hyx.2.1⟩⟩
    exact ⟨hya, ⟨hyD, hyb.2, fun h => hab (h ▸ hya.2.1)⟩⟩
  · rintro ⟨hya, hyb⟩
    have hyD : y ∈ D := hya.1
    have hyx : y ∈ perpMem D x := hxperp ⟨⟨hyD, hya.2.1⟩, ⟨hyD, hyb.2.1⟩⟩
    exact ⟨hya, ⟨hyD, hyx.2, fun h => hxa' (h ▸ hya.2.1)⟩⟩

theorem commute_apply_iff (σ : commGraph D ≃g commGraph D) (a b : D) :
    Commute (σ a : G) (σ b) ↔ Commute (a : G) b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · have hne : σ a ≠ σ b := fun h => hab (σ.injective h)
    constructor
    · intro h
      exact (commGraph_adj_iff.mp (σ.map_adj_iff.mp (show (commGraph D).Adj (σ a) (σ b) from
        ⟨hne, h⟩))).2
    · intro h
      exact (commGraph_adj_iff.mp (σ.map_adj_iff.mpr (show (commGraph D).Adj a b from
        ⟨hab, h⟩))).2

theorem mem_lineMem_of_forall_apply_eq (σ : commGraph D ≃g commGraph D) {a b : G}
    (hσ : ∀ v : D, (v : G) ∈ perpMem D a ∩ perpMem D b → σ v = v) {x : D}
    (hx : (x : G) ∈ lineMem D a b) : (σ x : G) ∈ lineMem D a b := by
  refine mem_lineMem.mpr ⟨(σ x).2, ?_⟩
  rintro p ⟨hpa, hpb⟩
  refine ⟨hpa.1, ?_⟩
  have hfix : σ ⟨p, hpa.1⟩ = ⟨p, hpa.1⟩ := hσ ⟨p, hpa.1⟩ ⟨hpa, hpb⟩
  have hpx : Commute (p : G) x := (hx.2 ⟨hpa, hpb⟩).2
  have h1 : Commute ((σ ⟨p, hpa.1⟩ : D) : G) ((σ x : D) : G) :=
    (commute_apply_iff σ ⟨p, hpa.1⟩ x).mpr hpx
  have h2 : ((σ ⟨p, hpa.1⟩ : D) : G) = p := congrArg Subtype.val hfix
  rw [h2] at h1
  exact h1

theorem lineMem_inter_perpMem_eq_singleton (hL : IsHypLineSpace D) {u w t : G} (hu : u ∈ D)
    (hw : w ∈ D) (hwu : ¬ Commute w u) (ht : t ∈ perpMem D w) (htu : ¬ Commute t u) :
    lineMem D u t ∩ perpMem D w = {t} := by
  classical
  apply Set.Subset.antisymm
  · rintro s ⟨hs, hsw⟩
    by_contra hst
    rw [Set.mem_singleton_iff] at hst
    have htD : t ∈ D := ht.1
    have hline := hL.lineMem_eq hu htD htu (right_mem_lineMem htD) hs hst
    have hw_perp : w ∈ perpMem D t ∩ perpMem D s :=
      ⟨⟨hw, ht.2.symm⟩, ⟨hw, hsw.2.symm⟩⟩
    have hu_line : u ∈ lineMem D t s := by
      rw [hline.2]
      exact self_mem_lineMem hu
    have hwpu : w ∈ perpMem D u := (mem_lineMem.mp hu_line).2 hw_perp
    exact hwu hwpu.2
  · rintro s hs
    have hst : s = t := by simpa using hs
    rw [hst]
    exact ⟨right_mem_lineMem ht.1, ht⟩

theorem apply_eq_of_commute_of_apply_eq (hL : IsHypLineSpace D) {u : G} (hu : u ∈ D)
    {σ : commGraph D ≃g commGraph D} (hσ : ∀ v : D, Commute (v : G) u → σ v = v) {w : D}
    (hwu : ¬ Commute (w : G) u) (hσw : σ w = w) {v : D} (hv : Commute (v : G) w) : σ v = v := by
  by_cases hvu : Commute (v : G) u
  · exact hσ v hvu
  · have hmem : (σ v : G) ∈ lineMem D u (v : G) :=
      mem_lineMem_of_forall_apply_eq σ (a := u) (b := (v : G)) (x := v)
        (fun p hp => hσ p hp.1.2) (right_mem_lineMem v.2)
    have hperp : (σ v : G) ∈ perpMem D w := by
      refine ⟨(σ v).2, ?_⟩
      have hcomm : Commute ((σ v : D) : G) ((σ w : D) : G) :=
        (commute_apply_iff σ v w).mpr hv
      rwa [hσw] at hcomm
    have hsing := lineMem_inter_perpMem_eq_singleton hL hu w.2 hwu ⟨v.2, hv⟩ hvu
    have hsingle : (σ v : G) ∈ ({(v : G)} : Set G) := by
      rw [← hsing]
      exact ⟨hmem, hperp⟩
    exact Subtype.ext (by simpa using hsingle)

private theorem ncard_commSet_eq (hS : Asc72.Setup G D) {u w : G} (hu : u ∈ D) (hw : w ∈ D) :
    (commSet D u).ncard = (commSet D w).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hu hw)
  rw [commSet_conj_eq_image hS.normal g u]
  exact (Set.ncard_image_of_injective _ fun a b h => by simpa using h).symm

private theorem exists_mem_commSet_not_commute [Finite G] (hS : Asc72.Setup G D)
    (htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b) {u w : G} (hu : u ∈ D)
    (hw : w ∈ D) (hwu : ¬ Commute w u) : ∃ z ∈ commSet D u, ¬ Commute z w := by
  by_contra h
  push Not at h
  have hsub : commSet D u ⊆ commSet D w := fun x hx =>
    ⟨hx.1, h x hx, fun hxw => hwu (by rw [← hxw]; exact hx.2.1)⟩
  have huw : u = w :=
    htwin u hu w hw (Set.eq_of_subset_of_ncard_le hsub (ncard_commSet_eq hS hw hu).le)
  exact hwu (by rw [← huw])

private theorem eq_of_mem_lineMem_of_mem_commSet (hL : IsHypLineSpace D) {u v w x z : G}
    (hu : u ∈ D) (hw : w ∈ D) (hwu : ¬ Commute w u) (hv : v ∈ lineMem D u w)
    (hvu : ¬ Commute v u) (hz : z ∈ commSet D u) (hvz : ¬ Commute v z)
    (hxu : x ∈ lineMem D u v) (hxz : x ∈ lineMem D z v) : x = v := by
  have hvD : v ∈ D := lineMem_subset D u w hv
  by_contra hne
  have hline_uw := hL u hu w hw hwu v hv fun h => hvu (by rw [h])
  have hline_uv := hL.lineMem_eq hu hvD hvu (right_mem_lineMem hvD) hxu hne
  have hline_zv := hL.lineMem_eq hz.1 hvD hvz (right_mem_lineMem hvD) hxz hne
  have hz_mem : z ∈ lineMem D u w := by
    rw [← hline_uw.2, ← hline_uv.2, hline_zv.2]
    exact self_mem_lineMem hz.1
  exact (hL u hu w hw hwu z hz_mem hz.2.2).1 hz.2.1

private theorem eq_of_mem_lineMem_of_notMem_lineMem (hL : IsHypLineSpace D) {u v w x : G}
    (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D) (hvu : ¬ Commute v u) (hvw : ¬ Commute v w)
    (hwu : w ≠ u) (hv_uw : v ∉ lineMem D u w) (hxu : x ∈ lineMem D u v)
    (hxw : x ∈ lineMem D w v) : x = v := by
  by_contra hne
  have hline_uv := hL.lineMem_eq hu hv hvu (right_mem_lineMem hv) hxu hne
  have hline_wv := hL.lineMem_eq hw hv hvw (right_mem_lineMem hv) hxw hne
  have hw_mem : w ∈ lineMem D u v := by
    rw [← hline_uv.2, hline_wv.2]
    exact self_mem_lineMem hw
  apply hv_uw
  rw [(hL.lineMem_eq hu hv hvu (self_mem_lineMem hu) hw_mem hwu).2]
  exact right_mem_lineMem hv

theorem apply_eq_of_apply_eq [Finite G] (hS : Asc72.Setup G D) (hL : IsHypLineSpace D)
    (htwin : ∀ a ∈ D, ∀ b ∈ D, commSet D a = commSet D b → a = b) {u : G} (hu : u ∈ D)
    {σ : commGraph D ≃g commGraph D} (hσ : ∀ v : D, Commute (v : G) u → σ v = v) {w : D}
    (hwu : ¬ Commute (w : G) u) (hσw : σ w = w) (v : D) : σ v = v := by
  classical
  have hσw_fix : ∀ x : D, Commute (x : G) w → σ x = x :=
    fun x hx => apply_eq_of_commute_of_apply_eq (σ := σ) (v := x) hL hu hσ hwu hσw hx
  by_cases hvu : Commute (v : G) u
  · exact hσ v hvu
  by_cases hvw : Commute (v : G) w
  · exact hσw_fix v hvw
  have hσv_uv : (σ v : G) ∈ lineMem D u (v : G) :=
    mem_lineMem_of_forall_apply_eq σ (a := u) (b := (v : G)) (x := v)
      (fun p hp => hσ p hp.1.2) (right_mem_lineMem v.2)
  by_cases hv_uw : (v : G) ∈ lineMem D u (w : G)
  ·
    obtain ⟨z, hz, hzw⟩ := exists_mem_commSet_not_commute hS htwin hu w.2 hwu
    have hσz_fix : ∀ x : D, Commute (x : G) z → σ x = x :=
      fun x hx => apply_eq_of_commute_of_apply_eq (u := (w : G)) (w := ⟨z, hz.1⟩) (v := x)
        hL w.2 hσw_fix hzw (hσ ⟨z, hz.1⟩ hz.2.1) hx
    by_cases hvz : Commute (v : G) z
    · exact hσz_fix v hvz
    exact Subtype.ext (eq_of_mem_lineMem_of_mem_commSet hL hu w.2 hwu hv_uw hvu hz hvz hσv_uv
      (mem_lineMem_of_forall_apply_eq σ (a := z) (b := (v : G)) (x := v)
        (fun p hp => hσz_fix p hp.1.2) (right_mem_lineMem v.2)))
  · exact Subtype.ext (eq_of_mem_lineMem_of_notMem_lineMem hL hu v.2 w.2 hvu hvw
      (fun h => hwu (by rw [h])) hv_uw hσv_uv
      (mem_lineMem_of_forall_apply_eq σ (a := (w : G)) (b := (v : G)) (x := v)
        (fun p hp => hσw_fix p hp.1.2) (right_mem_lineMem v.2)))

end CFSG.OddTranspositions.PartThree
