module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction

local notation "D4T" => TwistTag.D4.tag

@[expose] def d4Node : Fin (Tag.rank D4T) := (2 : Fin 4)

@[expose] def d4PerpNodes : Set (Fin (Tag.rank D4T)) := {j | j ≠ d4Node}

theorem rcp_iform_eq_sum_mul (θ v : Fin (Tag.rank D4T) → ℤ) :
    iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem rcp_iform_highRoot_single (j : Fin (Tag.rank D4T)) :
    iform (highRoot D4T) (Pi.single j 1) = if j = d4Node then 1 else 0 := by
  revert j; decide +kernel

theorem rcp_iform_highRoot (v : Fin (Tag.rank D4T) → ℤ) :
    iform (highRoot D4T) v = v d4Node := by
  rw [rcp_iform_eq_sum_mul]
  simp only [rcp_iform_highRoot_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

section Weyl

theorem rcp_smul_apply_node {w : WeylGroup D4T} (hw : w • highRoot D4T = highRoot D4T)
    (v : Fin (Tag.rank D4T) → ℤ) : (w • v) d4Node = v d4Node := by
  rw [← rcp_iform_highRoot (w • v), ← rcp_iform_highRoot v]
  conv_lhs => rw [← hw]
  exact iform_smul w _ _

theorem rcp_mem_parabolicWeylGroup {w : WeylGroup D4T} (hw : w • highRoot D4T = highRoot D4T) :
    w ∈ parabolicWeylGroup D4T d4PerpNodes := by
  have h : w ∈ (parabolicWeylGroup D4T d4PerpNodes : Set (WeylGroup D4T)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer D4T d4PerpNodes).1]
    intro v i hi
    have hi0 : i = d4Node := by simpa [d4PerpNodes] using hi
    subst hi0
    exact rcp_smul_apply_node hw v
  exact h

theorem rcp_reflect_highRoot (j : Fin (Tag.rank D4T)) (hj : j ≠ d4Node) :
    reflect D4T j (highRoot D4T) = highRoot D4T := by
  revert j; decide +kernel

end Weyl

section Bruhat

variable {K : Type} [Field K]

theorem rcp_exists_conj_pinnedX_highRoot_of_mem_borelGroup {b : ModGL D4T K}
    (hb : b ∈ borelGroup D4T K) {c : K} (hc : c ≠ 0) :
    ∃ d : K, d ≠ 0 ∧
      b * pinnedX D4T K (highRoot D4T) c * b⁻¹ = pinnedX D4T K (highRoot D4T) d := by
  have h : b * pinnedX D4T K (highRoot D4T) c * b⁻¹ ∈ rootSubgroup D4T K (highRoot D4T) := by
    rw [← map_conj_highRoot_of_mem_borelGroup hb]
    exact ⟨_, mem_rootSubgroup.2 ⟨c, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 h
  refine ⟨d, fun hd0 => hc ?_, hd.symm⟩
  rw [hd0, pinnedX_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hd
  exact pinnedX_injective D4T K _ (hd.trans (pinnedX_zero D4T K _).symm)

theorem rcp_eq_of_pinnedX_eq_pinnedX {β γ : Fin (Tag.rank D4T) → ℤ} (hβ : IsRoot D4T β)
    (hγ : IsRoot D4T γ ∧ 0 < height γ) {d e : K} (hd : d ≠ 0)
    (h : pinnedX D4T K β d = pinnedX D4T K γ e) : β = γ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [β, γ] (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hβ, hpos⟩
        · exact hγ)
      (fun α => if α = β then d else 0) (fun α => if α = γ then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          hne, Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      β (by simp)
    simp only [hne, ↓reduceIte] at hL
    exact hd hL
  · have hmem : pinnedX D4T K β d ∈ borelGroup D4T K ⊓ negUnipotent D4T K := by
      refine Subgroup.mem_inf.2 ⟨?_, pinnedX_mem_rootSpan
        (S := {α | IsRoot D4T α ∧ height α < 0}) ⟨hβ, hneg⟩ d⟩
      rw [h]
      exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan
        (S := {α | IsRoot D4T α ∧ 0 < height α}) hγ e)
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
    exact hd (pinnedX_injective D4T K β (hmem.trans (pinnedX_zero D4T K β).symm))

theorem rcp_mem_parabolicSubgroup_of_conj {g : ModGL D4T K} (hg : g ∈ adjointGroup D4T K)
    {c e : K} (hc : c ≠ 0)
    (h : g * pinnedX D4T K (highRoot D4T) c * g⁻¹ = pinnedX D4T K (highRoot D4T) e) :
    g ∈ parabolicSubgroup D4T K d4PerpNodes := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  set n := canonicalRep (coxeterSystem D4T) K w with hn
  obtain ⟨d, hd0, hd⟩ := rcp_exists_conj_pinnedX_highRoot_of_mem_borelGroup hb' hc
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero, mul_inv_eq_one, mul_eq_left] at h
    exact hc (pinnedX_injective D4T K _ (h.trans (pinnedX_zero D4T K _).symm))
  obtain ⟨e', -, he'⟩ := rcp_exists_conj_pinnedX_highRoot_of_mem_borelGroup (inv_mem hb) he0
  have hnd : n * pinnedX D4T K (highRoot D4T) d * n⁻¹ = pinnedX D4T K (highRoot D4T) e' := by
    rw [← hd, ← he', ← h]
    group
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_highRoot D4T)
  rw [hn, hεc] at hnd
  have hεd : ε * d ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hd0
  have hwθ := rcp_eq_of_pinnedX_eq_pinnedX (IsRoot.smul (isRoot_highRoot D4T) w)
    ⟨isRoot_highRoot D4T, height_highRoot_pos D4T⟩ hεd hnd
  have hmem : b * n * b' ∈ (parabolicSubgroup D4T K d4PerpNodes : Set (ModGL D4T K)) := by
    rw [(standard_parabolic_cells D4T K).1 d4PerpNodes]
    exact Set.mem_biUnion (rcp_mem_parabolicWeylGroup hwθ) hw
  exact hmem

theorem rcp_weylElt_conj_highRoot [CharP K 2] {j : Fin (Tag.rank D4T)} (hj : j ∈ d4PerpNodes)
    (c : K) :
    weylElt D4T K j 1 * pinnedX D4T K (highRoot D4T) c * (weylElt D4T K j 1)⁻¹ =
      pinnedX D4T K (highRoot D4T) c := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← canonicalRep_simple (coxeterSystem D4T) K j,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_highRoot D4T) c]
  congr 1
  exact (simple_smul j _).trans (rcp_reflect_highRoot j hj)

theorem rcp_parabolicSubgroup_le_normalizer [CharP K 2] :
    parabolicSubgroup D4T K d4PerpNodes ≤
      normalizer (rootSubgroup D4T K (highRoot D4T) : Set (ModGL D4T K)) := by
  refine sup_le (borelGroup_le_normalizer_highRoot K) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    show weylElt D4T K j 1 * pinnedX D4T K (highRoot D4T) c * (weylElt D4T K j 1)⁻¹ ∈ _
    rw [rcp_weylElt_conj_highRoot hj]
    exact mem_rootSubgroup.2 ⟨c, rfl⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    refine ⟨pinnedX D4T K (highRoot D4T) c, mem_rootSubgroup.2 ⟨c, rfl⟩, ?_⟩
    show weylElt D4T K j 1 * pinnedX D4T K (highRoot D4T) c * (weylElt D4T K j 1)⁻¹ = _
    rw [rcp_weylElt_conj_highRoot hj]

end Bruhat

end CFSG.RankThree.PartOne.D4RC
