module

public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.EmptyFaithful.E22NParam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N CFSG.Quasithin.Vol2.Ch11.SecB Subgroup
open CFSG.Quasithin (IsSylowIn)

private lemma fourFive_mk'_injective_on_le {Q : Type} [Group Q] {X Y C U : Subgroup Q}
    [(C.subgroupOf U).Normal] (hXC : X ⊓ C = ⊥) (hYX : Y ≤ X) :
    Function.Injective
      ((QuotientGroup.mk' (C.subgroupOf U)).comp (Y.subgroupOf U).subtype) := by
  have hX : Function.Injective
      ((QuotientGroup.mk' (C.subgroupOf U)).comp (X.subgroupOf U).subtype) := by
    intro a b hab
    have hmemX : ((a⁻¹ * b : ↥(X.subgroupOf U)) : ↥U) ∈ X.subgroupOf U :=
      (a⁻¹ * b).2
    have hmemC : ((a⁻¹ * b : ↥(X.subgroupOf U)) : ↥U) ∈ C.subgroupOf U := by
      rw [← QuotientGroup.ker_mk' (C.subgroupOf U), MonoidHom.mem_ker]
      have h1 : ((QuotientGroup.mk' (C.subgroupOf U)).comp (X.subgroupOf U).subtype)
          (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact h1
    have hQ : (((a⁻¹ * b : ↥(X.subgroupOf U)) : ↥U) : Q) ∈ X ⊓ C := ⟨hmemX, hmemC⟩
    rw [hXC, Subgroup.mem_bot] at hQ
    have h1U : ((a⁻¹ * b : ↥(X.subgroupOf U)) : ↥U) = 1 := by
      apply Subtype.ext
      simpa using hQ
    exact inv_mul_eq_one.mp (Subtype.ext h1U)
  intro a b hab
  have hYX' : (Y.subgroupOf U) ≤ (X.subgroupOf U) := Subgroup.comap_mono hYX
  refine Subgroup.inclusion_injective hYX' (hX ?_)
  simpa using hab

private noncomputable def fourFive_quotientEquiv {Q : Type} [Group Q]
    {X Y C U : Subgroup Q} [(C.subgroupOf U).Normal] (hXC : X ⊓ C = ⊥) (hXU : X ≤ U)
    (hYX : Y ≤ X) :
    ↥Y ≃* ↥((Y.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) :=
  let hYU : Y ≤ U := hYX.trans hXU
  let hinj : Function.Injective
      ((QuotientGroup.mk' (C.subgroupOf U)).comp (Y.subgroupOf U).subtype) :=
    fourFive_mk'_injective_on_le hXC hYX
  let e1 : ↥(Y.subgroupOf U) ≃*
      ↥((Y.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) :=
    (MonoidHom.domRestrict_range (Y.subgroupOf U) (QuotientGroup.mk' (C.subgroupOf U))) ▸
      MonoidHom.ofInjective hinj
  (Subgroup.subgroupOfEquivOfLe hYU).symm.trans e1

private lemma fourFive_commute_of_mem_centralizer_quotient {Q : Type} [Group Q]
    {X C U : Subgroup Q} [(C.subgroupOf U).Normal] [(X.subgroupOf U).Normal]
    (hXC : X ⊓ C = ⊥) (hXU : X ≤ U)
    {u : ↥U}
    (hub : (QuotientGroup.mk' (C.subgroupOf U)) u ∈
      Subgroup.centralizer (((X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) :
        Set (↥U ⧸ C.subgroupOf U)))
    {x : Q} (hx : x ∈ X) : (u : Q) * x = x * (u : Q) := by
  let xU : ↥U := ⟨x, hXU hx⟩
  have hxu : xU ∈ X.subgroupOf U := Subgroup.mem_subgroupOf.mpr hx
  have hc : (QuotientGroup.mk' (C.subgroupOf U)) xU * (QuotientGroup.mk' (C.subgroupOf U)) u
      = (QuotientGroup.mk' (C.subgroupOf U)) u
        * (QuotientGroup.mk' (C.subgroupOf U)) xU :=
    Subgroup.mem_centralizer_iff.mp hub _ (Subgroup.mem_map_of_mem _ hxu)
  have hmap1 : (QuotientGroup.mk' (C.subgroupOf U)) ((u * xU * u⁻¹) * xU⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have hmemC : (u * xU * u⁻¹) * xU⁻¹ ∈ C.subgroupOf U := by
    rw [← QuotientGroup.ker_mk' (C.subgroupOf U), MonoidHom.mem_ker]
    exact hmap1
  have hmemX : (u * xU * u⁻¹) * xU⁻¹ ∈ X.subgroupOf U :=
    (X.subgroupOf U).mul_mem
      ((inferInstance : (X.subgroupOf U).Normal).conj_mem xU hxu u)
      ((X.subgroupOf U).inv_mem hxu)
  have hmemQ : (((u * xU * u⁻¹) * xU⁻¹ : ↥U) : Q) ∈ X ⊓ C := ⟨hmemX, hmemC⟩
  rw [hXC, Subgroup.mem_bot] at hmemQ
  have hmem : (u * xU * u⁻¹) * xU⁻¹ = 1 := by
    apply Subtype.ext
    simpa using hmemQ
  have huxu : u * xU * u⁻¹ = xU := by
    calc u * xU * u⁻¹ = (u * xU * u⁻¹) * xU⁻¹ * xU := by group
      _ = 1 * xU := by rw [hmem]
      _ = xU := by group
  have hcommU : u * xU = xU * u := by
    calc u * xU = (u * xU * u⁻¹) * u := by group
      _ = xU * u := by rw [huxu]
  simpa using congrArg Subtype.val hcommU

theorem fourFive_reduced_quotient {Q : Type} [Group Q] {X T U C : Subgroup Q}
    (hTU : IsSylowIn 2 T U) (hU : U = X ⊔ T) [(X.subgroupOf U).Normal]
    (hmin : ∀ K : Subgroup Q, K ≤ X → (K.subgroupOf U).Normal → K = ⊥ ∨ K = X)
    (hnc : ¬ IsMulCommutative X) (hZ : X ⊓ Subgroup.centralizer (X : Set Q) = ⊥)
    (hC : C = U ⊓ Subgroup.centralizer (X : Set Q)) [(C.subgroupOf U).Normal] :
    E111Reduced (↥U ⧸ C.subgroupOf U)
      ((X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))
      ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) := by
  have hXU : X ≤ U := by rw [hU]; exact le_sup_left
  have hXC : X ⊓ C = ⊥ := by
    apply le_bot_iff.mp
    calc X ⊓ C ≤ X ⊓ Subgroup.centralizer (X : Set Q) := by
          rw [hC]; exact inf_le_inf_left X inf_le_right
      _ = ⊥ := hZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (C.subgroupOf U))
      (QuotientGroup.mk'_surjective _)
  · intro hbot
    have hle : X.subgroupOf U ≤ C.subgroupOf U := by
      have h' : X.subgroupOf U ≤ (QuotientGroup.mk' (C.subgroupOf U)).ker :=
        (Subgroup.map_eq_bot_iff (X.subgroupOf U)).mp hbot
      rwa [QuotientGroup.ker_mk' (C.subgroupOf U)] at h'
    have hCX : X ≤ C := by
      intro x hx
      have hxX : (⟨x, hXU hx⟩ : ↥U) ∈ X.subgroupOf U := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (hle hxX)
    have hC_le : C ≤ Subgroup.centralizer (X : Set Q) := by
      rw [hC]; exact inf_le_right
    have hcomm : IsMulCommutative X := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      have ha : (a : Q) ∈ Subgroup.centralizer (X : Set Q) := hC_le (hCX a.2)
      exact (Subgroup.mem_centralizer_iff.mp ha (b : Q) b.2).symm
    exact hnc hcomm
  · intro M hMnorm hMle
    let M' : Subgroup ↥U := M.comap (QuotientGroup.mk' (C.subgroupOf U))
    have hM'norm : M'.Normal := hMnorm.comap _
    let Kt : Subgroup ↥U := M' ⊓ X.subgroupOf U
    have hKtnorm : Kt.Normal := by
      show (M' ⊓ X.subgroupOf U).Normal
      infer_instance
    let K : Subgroup Q := Kt.map U.subtype
    have hKsub : K.subgroupOf U = Kt := by
      show (Kt.map U.subtype).comap U.subtype = Kt
      exact Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective Kt
    have hKnorm : (K.subgroupOf U).Normal := by rw [hKsub]; exact hKtnorm
    have hKleX : K ≤ X := by
      have h1 : K ≤ (X.subgroupOf U).map U.subtype := Subgroup.map_mono inf_le_right
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXU] at h1
    rcases hmin K hKleX hKnorm with hKbot | hKX
    · left
      have hKtbot : Kt = ⊥ := by rw [← hKsub, hKbot, Subgroup.bot_subgroupOf]
      apply le_bot_iff.mp
      intro m hm
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp (hMle hm)
      have hxM' : x ∈ M' := by rw [Subgroup.mem_comap, hxπ]; exact hm
      have hxKt : x ∈ Kt := ⟨hxM', hx⟩
      rw [hKtbot, Subgroup.mem_bot] at hxKt
      rw [Subgroup.mem_bot, ← hxπ, hxKt, map_one]
    · right
      have hKtX : Kt = X.subgroupOf U := by rw [← hKsub, hKX]
      have hle : X.subgroupOf U ≤ M' := by rw [← hKtX]; exact inf_le_left
      exact le_antisymm hMle (Subgroup.map_le_iff_le_comap.mpr hle)
  · have hnc' : ∃ a b : ↥X, a * b ≠ b * a := by
      by_contra h
      apply hnc
      rw [isMulCommutative_iff]
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    obtain ⟨a, b, hab⟩ := hnc'
    let e : ↥X ≃* ↥((X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) :=
      fourFive_quotientEquiv hXC hXU le_rfl
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  · apply le_bot_iff.mp
    intro ub hub
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf U) ub
    have huC : u ∈ C.subgroupOf U := by
      apply Subgroup.mem_subgroupOf.mpr
      rw [hC]
      refine ⟨u.2, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (fourFive_commute_of_mem_centralizer_quotient hXC hXU hub hx).symm
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff u).mpr huC
  · refine ⟨le_top, ?_, ?_⟩
    · have hTp : IsPGroup 2 (T.subgroupOf U : Subgroup ↥U) :=
        hTU.isPGroup.comap_subtype (K := U)
      simpa using hTp.map (QuotientGroup.mk' (C.subgroupOf U))
    · rw [Subgroup.relIndex_top_right]
      intro hdvd
      exact hTU.not_dvd_relIndex
        (hdvd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  · rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hXU hTU.le, ← hU, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem fourFive_isComp_quotient {Q : Type} [Group Q] {X J U C : Subgroup Q} (hXU : X ≤ U)
    [(C.subgroupOf U).Normal] (hXC : X ⊓ C = ⊥) (hJ : E111R.IsComp X J) :
    E111R.IsComp ((X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)))
      ((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) := by
  have hJU : J ≤ U := hJ.1.trans hXU
  have hJXU : (J.subgroupOf U) ≤ (X.subgroupOf U) := Subgroup.subgroupOf_mono U hJ.1
  have hJbar_le : (J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))
      ≤ (X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)) :=
    Subgroup.map_mono hJXU
  let e : ↥J ≃* ↥((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) :=
    fourFive_quotientEquiv hXC hXU hJ.1
  haveI : IsSimpleGroup ↥J := hJ.simple
  refine ⟨hJbar_le, ?_, e.symm.isSimpleGroup, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hJbar_le]
    intro h k hh hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    have hxN : (x : Q) ∈ Subgroup.normalizer (J : Set Q) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.1).mp hJ.2.1 hx
    have hconj : (x : Q) * (y : Q) * (x : Q)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp hxN (y : Q)).mp hy
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hconj)
  · obtain ⟨a, b, hab⟩ := hJ.nonabelian
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩

end CFSG.LocalAnalysis.WeakClosure81
