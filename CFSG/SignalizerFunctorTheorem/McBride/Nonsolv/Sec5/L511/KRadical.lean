module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511

variable {G : Type*} [Group G]

theorem mem_lcal_of_le {X Y J : Subgroup G} (hJ : J ∈ lcal Y) (hJX : J ≤ X) (hXY : X ≤ Y) :
    J ∈ lcal X := by
  obtain ⟨-, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  refine mem_lcal_iff.mpr ⟨hJX, ?_, hs, hnc⟩
  have heq : (J.subgroupOf Y).comap (Subgroup.inclusion hXY) = J.subgroupOf X := by
    ext t
    rfl
  exact heq ▸ hsub.comap (Subgroup.inclusion hXY)

theorem le_oStar_of_mem_lcalOf {H : Type*} [Group H] [Finite H] {J : Subgroup H}
    (hJ : J ∈ lcalOf H) : J ≤ oStar H := by
  obtain ⟨hsub, hs, hnc⟩ := hJ
  refine le_oStar ?_
  rw [isSolComponent_iff_minimal]
  refine ⟨⟨hsub, fun hsolv => hnc (isMulCommutative_iff.mpr
    (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv))⟩, fun S hS hSJ => ?_⟩
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hS.1.subgroupOf with h | h
  · exfalso
    refine hS.2 ?_
    have hS1 : S = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall S).mpr fun x hx => ?_
      have hmem : (⟨x, hSJ hx⟩ : J) ∈ S.subgroupOf J := hx
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    rw [hS1]
    infer_instance
  · intro x hx
    have hmem : (⟨x, hx⟩ : J) ∈ S.subgroupOf J := by rw [h]; trivial
    exact hmem

variable [Finite G]

theorem le_kOf_of_mem_lcal {X J : Subgroup G} (hJ : J ∈ lcal X) : J ≤ kOf X := by
  obtain ⟨hJX, hJ'⟩ := hJ
  have h1 := le_oStar_of_mem_lcalOf hJ'
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at h2

theorem kOf_le_kOf_of_isSubnormal {X H : Subgroup G} (hHX : H ≤ X)
    (hH : (H.subgroupOf X).IsSubnormal) : kOf H ≤ kOf X := by
  let e := Subgroup.subgroupOfEquivOfLe hHX
  have h3 : (oStar ↥(H.subgroupOf X)).map e.toMonoidHom = oStar ↥H := oStar_map_mulEquiv e
  have hcomp : H.subtype.comp e.toMonoidHom = X.subtype.comp (H.subgroupOf X).subtype := rfl
  have h4 := Subgroup.map_mono (f := X.subtype) (oStar_map_subtype_le_oStar hH)
  calc kOf H = ((oStar ↥(H.subgroupOf X)).map e.toMonoidHom).map H.subtype := by rw [h3]; rfl
    _ = (oStar ↥(H.subgroupOf X)).map (H.subtype.comp e.toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = ((oStar ↥(H.subgroupOf X)).map (H.subgroupOf X).subtype).map X.subtype := by
        rw [hcomp, ← Subgroup.map_map]
    _ ≤ kOf X := h4

theorem kOf_ne_bot {X : Subgroup G} (hX : X ≠ ⊥) : kOf X ≠ ⊥ := by
  by_cases hsol : sol X = ⊥
  · intro hk
    have h := centralizer_kOf_eq_bot hsol
    rw [hk, Subgroup.centralizer_eq_top_iff_subset.mpr (by simp), inf_top_eq] at h
    exact hX h
  · exact fun hk => hsol (eq_bot_iff.mpr (hk ▸ sol_le_kOf X))

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_normal_chain {D M X : Subgroup G} (hDM : D ≤ M)
    (hMX : M ≤ X) (hD : (D.subgroupOf M).Normal) (hM : (M.subgroupOf X).Normal) :
    (D.subgroupOf X).IsSubnormal := by
  have hDX : D.subgroupOf X ≤ M.subgroupOf X := fun x hx => hDM hx
  refine Subgroup.IsSubnormal.trans hDX ?_ hM.isSubnormal
  let e := Subgroup.subgroupOfEquivOfLe hMX
  have heq : (D.subgroupOf X).subgroupOf (M.subgroupOf X) =
      (D.subgroupOf M).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact (hD.comap e.toMonoidHom).isSubnormal

omit [Finite G] in
theorem isSubnormal_inf_centralizer {K Z Y : Subgroup G} (hZK : Z ≤ K) (hKY : K ≤ Y)
    (hZ : (Z.subgroupOf K).Normal) (hK : (K.subgroupOf Y).Normal) (c : Set G) :
    ((Z ⊓ Subgroup.centralizer c).subgroupOf (Y ⊓ Subgroup.centralizer c)).IsSubnormal := by
  have hMX : K ⊓ Subgroup.centralizer c ≤ Y ⊓ Subgroup.centralizer c :=
    inf_le_inf_right _ hKY
  refine isSubnormal_subgroupOf_of_normal_chain (inf_le_inf_right _ hZK) hMX ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right _ hZK)]
    intro d m hd hm
    obtain ⟨hdZ, hdc⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hmK, hmc⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hZK).mp hZ d m hdZ hmK,
        mul_mem (mul_mem hmc hdc) (inv_mem hmc)⟩
  · rw [Subgroup.normal_subgroupOf_iff hMX]
    intro m x hm hx
    obtain ⟨hmK, hmc⟩ := Subgroup.mem_inf.mp hm
    obtain ⟨hxY, hxc⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hKY).mp hK m x hmK hxY,
        mul_mem (mul_mem hxc hmc) (inv_mem hxc)⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L511
