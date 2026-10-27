module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxMain

public section

open CFSG.SignalizerFunctorTheorem CFSG.SignalizerFunctorTheorem.Nonsolvable
  CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

theorem isSolvable_ker_subgroupMap {A B : Type*} [Group A] [Group B] (f : A →* B)
    [Group.IsSolvable f.ker] (H : Subgroup A) : Group.IsSolvable (f.subgroupMap H).ker := by
  let g : (f.subgroupMap H).ker →* f.ker :=
    ((H.subtype).comp (f.subgroupMap H).ker.subtype).codRestrict f.ker (fun x => by
      have hx := MonoidHom.mem_ker.mp x.2
      have := congrArg Subtype.val hx
      exact this)
  refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
  intro x y hxy
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext this)

section Quotient

variable {H : Type*} [Group H] [Finite H]

theorem mem_oStar_iff_map_mem_layer (x : H) :
    x ∈ oStar H ↔ QuotientGroup.mk' (CFSG.solvableRadical H) x ∈
      CFSG.layer (H ⧸ CFSG.solvableRadical H) := by
  rw [oStar_eq_comap_layer]
  rfl

theorem deg_layer_quotient :
    deg ↥(CFSG.layer (H ⧸ CFSG.solvableRadical H)) = deg ↥(oStar H) := by
  set R := CFSG.solvableRadical H with hR
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  let ψ : ↥(oStar H) →* ↥(CFSG.layer (H ⧸ R)) :=
    (π.comp (oStar H).subtype).codRestrict (CFSG.layer (H ⧸ R)) fun x =>
      (mem_oStar_iff_map_mem_layer x.1).mp x.2
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨h, hh⟩ := hπs y
    exact ⟨⟨h, (mem_oStar_iff_map_mem_layer h).mpr (by rw [hh]; exact y.2)⟩, Subtype.ext hh⟩
  have hψker : Group.IsSolvable ψ.ker := by
    let g : ψ.ker →* R := ((oStar H).subtype.comp ψ.ker.subtype).codRestrict R (fun x => by
      have hx := MonoidHom.mem_ker.mp x.2
      have := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp this)
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  exact (KAPI.deg_eq_of_surjective hψs hψker).symm

theorem hypB_components_quotient (hC : HypC H) :
    ∀ J ∈ lcal (⊤ : Subgroup (H ⧸ CFSG.solvableRadical H)), HypB ↥J := by
  intro J hJ
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have hsec : IsSectionOf ↥J H :=
    (IsSectionOf.of_subgroup J).trans
      (IsSectionOf.of_surjective (QuotientGroup.mk' (CFSG.solvableRadical H))
        (QuotientGroup.mk'_surjective _))
  refine KAPI.hypB_of_isSectionOf hC hsec hs ?_
  by_contra hcon
  push Not at hcon
  exact hnc (IsMulCommutative.of_comm hcon)

theorem map_quotient_props {Y : Subgroup H} (hY : oStar ↥Y = ⊤) :
    oStar ↥(Y.map (QuotientGroup.mk' (CFSG.solvableRadical H))) = ⊤ ∧
      deg ↥(Y.map (QuotientGroup.mk' (CFSG.solvableRadical H))) = deg ↥Y ∧
      Nat.card (↥(Y.map (QuotientGroup.mk' (CFSG.solvableRadical H))) ⧸
          CFSG.solvableRadical ↥(Y.map (QuotientGroup.mk' (CFSG.solvableRadical H)))) =
        Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y) := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical H) with hπ
  have hRs : Group.IsSolvable (CFSG.solvableRadical H) := isSolvable_solvableRadical
  have hπker : Group.IsSolvable π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hRs
  have hker := isSolvable_ker_subgroupMap π Y
  refine ⟨KAPI.oStar_eq_top_of_surjective hY (f := π.subgroupMap Y) (π.subgroupMap_surjective Y),
    (KAPI.deg_eq_of_surjective (π.subgroupMap_surjective Y) hker).symm, ?_⟩
  exact (Nat.card_congr (KAPI.solQuotEquiv (π.subgroupMap_surjective Y) hker).toEquiv).symm

theorem le_oStar_of_deg_le (hC : HypC H) {X : Subgroup H}
    (hX : oStar ↥X = ⊤) (hperf : Group.IsPerfect X) (hdeg : deg ↥(oStar H) ≤ deg ↥X) :
    X ≤ oStar H := by
  obtain ⟨hXbar, hdegX, -⟩ := map_quotient_props hX
  have hperfbar : Group.IsPerfect (X.map (QuotientGroup.mk' (CFSG.solvableRadical H))) := by
    have := hperf
    exact Group.IsPerfect.map (f := QuotientGroup.mk' (CFSG.solvableRadical H))
  have hle := le_layer_of_deg_le solvableRadical_quotient (hypB_components_quotient hC) hXbar
    hperfbar (by rw [deg_layer_quotient, hdegX]; exact hdeg)
  intro x hx
  exact (mem_oStar_iff_map_mem_layer x).mpr (hle ⟨x, hx, rfl⟩)

end Quotient

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
