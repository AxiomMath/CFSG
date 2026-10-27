module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType

open CFSG.Open

section Subtype

variable {G : Type*} [Group G]

theorem ggCentralizer_singleton_subgroupOf {H : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (H : Set G)) (g : H) :
    (Subgroup.centralizer {c * (g : G)}).subgroupOf H = Subgroup.centralizer {g} := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hyc : (y : G) * c = c * (y : G) :=
    Subgroup.mem_centralizer_iff.mp hc y y.2
  have hgc : (g : G) * c = c * (g : G) :=
    Subgroup.mem_centralizer_iff.mp hc g g.2
  constructor
  · intro h
    apply Subtype.ext
    have h' : c * ((y : G) * (g : G)) = c * ((g : G) * (y : G)) := by
      calc c * ((y : G) * (g : G)) = (c * (y : G)) * (g : G) := by group
        _ = ((y : G) * c) * (g : G) := by rw [hyc]
        _ = (y : G) * (c * (g : G)) := by group
        _ = ((c * (g : G)) * (y : G)) := h
        _ = c * ((g : G) * (y : G)) := by group
    exact mul_left_cancel h'
  · intro h
    have hG : (y : G) * (g : G) = (g : G) * (y : G) := by
      have := congrArg (Subtype.val) h
      simpa using this
    calc (y : G) * (c * (g : G)) = ((y : G) * c) * (g : G) := by group
      _ = (c * (y : G)) * (g : G) := by rw [hyc]
      _ = c * ((y : G) * (g : G)) := by group
      _ = c * ((g : G) * (y : G)) := by rw [hG]
      _ = (c * (g : G)) * (y : G) := by group

theorem ggPCoreOf_normalizer_map_subtype (H : Subgroup G) (R' : Subgroup H) :
    (pCoreOf 2 (Subgroup.normalizer (R' : Set H))).map H.subtype =
      pCoreOf 2 (H ⊓ Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G)) := by
  set M : Subgroup G := Subgroup.normalizer ((R'.map H.subtype : Subgroup G) : Set G) with hM
  have hN : Subgroup.normalizer (R' : Set H) = (H ⊓ M).subgroupOf H := by
    rw [Subgroup.inf_subgroupOf_left]
    change Subgroup.normalizer (R' : Set H) = Subgroup.comap H.subtype M
    rw [hM]
    have hle : (R'.map H.subtype : Subgroup G) ≤ H.subtype.range := by
      rw [Subgroup.range_subtype]
      exact Subgroup.map_subtype_le R'
    rw [Subgroup.comap_normalizer_eq_of_le_range (f := H.subtype) hle,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [hN, GGRootNorm.pCoreOf_subgroupOf (H := H ⊓ M) (K := H) inf_le_left]
  exact Subgroup.map_subgroupOf_eq_of_le ((GGRootNorm.pCoreOf_le (H ⊓ M)).trans inf_le_left)

theorem ggCenter_map_map_of_injective {E : Type*} [Group E] (ι : E →* G)
    (hι : Function.Injective ι) (Q' : Subgroup E) :
    (Subgroup.center ↥(Q'.map ι)).map (Q'.map ι).subtype =
      ((Subgroup.center ↥Q').map Q'.subtype).map ι := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := Subgroup.mem_center_iff.mp hq
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp q.2
    refine Subgroup.mem_map.mpr ⟨c, ?_, hcq⟩
    refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro d
    have hval := congrArg Subtype.val (hq' ⟨ι d, Subgroup.mem_map.mpr ⟨d, d.2, rfl⟩⟩)
    simp at hval
    rw [← hcq] at hval
    apply Subtype.ext
    exact hι (by simpa [map_mul] using hval)
  · rintro ⟨e, he, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp he
    refine Subgroup.mem_map.mpr ⟨⟨ι c, Subgroup.mem_map.mpr ⟨c, c.2, rfl⟩⟩, ?_, ?_⟩
    · refine Subgroup.mem_center_iff.mpr ?_
      intro w
      obtain ⟨d, hd, hdw⟩ := Subgroup.mem_map.mp w.2
      apply Subtype.ext
      change (w : G) * ι c = ι c * (w : G)
      rw [← hdw]
      have hcd : (⟨d, hd⟩ : Q') * c = c * (⟨d, hd⟩ : Q') :=
        Subgroup.mem_center_iff.mp hc ⟨d, hd⟩
      simpa [map_mul] using (congrArg (fun x : Q' => ι (x : E)) hcd)
    · rfl

theorem ggCommute_of_commute_mul_centralizer {H : Subgroup G}
    (hZ : ∀ y ∈ H, y ∈ Subgroup.centralizer (H : Set G) → y = 1) {cx cd : G}
    (hcx : cx ∈ Subgroup.centralizer (H : Set G)) (hcd : cd ∈ Subgroup.centralizer (H : Set G))
    {x₀ g : H}
    (hcomm : (cd * (g : G)) * (cx * (x₀ : G)) = (cx * (x₀ : G)) * (cd * (g : G))) :
    g * x₀ = x₀ * g := by
  have hcxg : (g : G) * cx = cx * (g : G) :=
    Subgroup.mem_centralizer_iff.mp hcx g g.2
  have hcdx : (x₀ : G) * cd = cd * (x₀ : G) :=
    Subgroup.mem_centralizer_iff.mp hcd x₀ x₀.2
  have hkey : (cd * cx) * ((g : G) * (x₀ : G)) = (cx * cd) * ((x₀ : G) * (g : G)) := by
    calc (cd * cx) * ((g : G) * (x₀ : G))
        = cd * (cx * (g : G)) * (x₀ : G) := by group
      _ = cd * ((g : G) * cx) * (x₀ : G) := by rw [← hcxg]
      _ = (cd * (g : G)) * (cx * (x₀ : G)) := by group
      _ = (cx * (x₀ : G)) * (cd * (g : G)) := hcomm
      _ = cx * ((x₀ : G) * cd) * (g : G) := by group
      _ = cx * (cd * (x₀ : G)) * (g : G) := by rw [hcdx]
      _ = (cx * cd) * ((x₀ : G) * (g : G)) := by group
  have h1 : cd * cx =
      (cx * cd) * (((x₀ : G) * (g : G)) * ((g : G) * (x₀ : G))⁻¹) := by
    calc cd * cx = ((cd * cx) * ((g : G) * (x₀ : G))) * ((g : G) * (x₀ : G))⁻¹ := by group
      _ = ((cx * cd) * ((x₀ : G) * (g : G))) * ((g : G) * (x₀ : G))⁻¹ := by rw [hkey]
      _ = (cx * cd) * (((x₀ : G) * (g : G)) * ((g : G) * (x₀ : G))⁻¹) := by group
  have hw_eq : ((x₀ : G) * (g : G)) * ((g : G) * (x₀ : G))⁻¹ =
      (cx * cd)⁻¹ * (cd * cx) := by
    rw [h1]
    group
  have hwH : ((x₀ : G) * (g : G)) * ((g : G) * (x₀ : G))⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem x₀.2 g.2) (H.inv_mem (H.mul_mem g.2 x₀.2))
  have hwC : ((x₀ : G) * (g : G)) * ((g : G) * (x₀ : G))⁻¹ ∈
      Subgroup.centralizer (H : Set G) := by
    rw [hw_eq]
    exact (Subgroup.centralizer (H : Set G)).mul_mem
      ((Subgroup.centralizer (H : Set G)).inv_mem
        ((Subgroup.centralizer (H : Set G)).mul_mem hcx hcd))
      ((Subgroup.centralizer (H : Set G)).mul_mem hcd hcx)
  have hw1 := hZ _ hwH hwC
  have hxg : (x₀ : G) * (g : G) = (g : G) * (x₀ : G) := by
    rw [mul_inv_eq_one] at hw1
    exact hw1
  apply Subtype.ext
  exact hxg.symm

theorem ggPow_eq_one_of_mul_centralizer {H : Subgroup G}
    (hZ : ∀ y ∈ H, y ∈ Subgroup.centralizer (H : Set G) → y = 1) {c : G}
    (hc : c ∈ Subgroup.centralizer (H : Set G)) {g : H} {m : ℕ}
    (hd : (c * (g : G)) ^ m = 1) : g ^ m = 1 := by
  have hcomm : Commute c (g : G) :=
    (Subgroup.mem_centralizer_iff.mp hc g g.2).symm
  have h1 : c ^ m * (g : G) ^ m = 1 := by
    rw [← hcomm.mul_pow m]
    exact hd
  have h2 : (g : G) ^ m = (c ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hgH : (g : G) ^ m ∈ H := H.pow_mem g.2 m
  have hgC : (g : G) ^ m ∈ Subgroup.centralizer (H : Set G) := by
    rw [h2]
    exact (Subgroup.centralizer (H : Set G)).inv_mem
      ((Subgroup.centralizer (H : Set G)).pow_mem hc m)
  have hg1 : (g : G) ^ m = 1 := hZ _ hgH hgC
  apply Subtype.ext
  simpa [Subgroup.coe_pow] using hg1

end Subtype

end CFSG.StandardType
