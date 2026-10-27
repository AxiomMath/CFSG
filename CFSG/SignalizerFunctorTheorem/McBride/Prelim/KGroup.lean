module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem inf_centralizer_generalizedFitting_le [Finite G] (X : Subgroup G) :
    X ⊓ Subgroup.centralizer (((CFSG.generalizedFitting ↥X).map X.subtype : Subgroup G) : Set G) ≤
      (CFSG.generalizedFitting ↥X).map X.subtype := by
  intro x hx
  obtain ⟨hxX, hxc⟩ := hx
  have hc : (⟨x, hxX⟩ : X) ∈
      Subgroup.centralizer ((CFSG.generalizedFitting ↥X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hxc (y : G) ⟨y, hy, rfl⟩
    exact Subtype.ext this
  exact ⟨⟨x, hxX⟩, CFSG.centralizer_generalizedFitting_le ↥X hc, rfl⟩

theorem map_kOf_eq_layer [Finite G] (X : Subgroup G) :
    ((kOf X).subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) =
      CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X) := by
  rw [subgroupOf_kOf, oStar_eq_comap_layer]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem layer_quotient_eq_generalizedFitting [Finite G] (X : Subgroup G) :
    CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X) =
      CFSG.generalizedFitting (↥X ⧸ CFSG.solvableRadical ↥X) :=
  (generalizedFitting_eq_layer_of_solvableRadical_eq_bot solvableRadical_quotient).symm

theorem isSemisimple_layer_quotient [Finite G] (X : Subgroup G) :
    IsSemisimple (CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X)) :=
  isSemisimple_layer solvableRadical_quotient

section IsoCompat

variable {A B : Type*} [Group A] [Group B]

theorem map_symm_map_mulEquiv (e : A ≃* B) (S : Subgroup B) :
    (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
  have := CFSG.LocalCores.map_map_symm e.symm S
  rwa [MulEquiv.symm_symm] at this

theorem isSolvable_map_mulEquiv (e : A ≃* B) {N : Subgroup A} (h : Group.IsSolvable N) :
    Group.IsSolvable (N.map e.toMonoidHom) :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap N)
    (MonoidHom.subgroupMap_surjective _ _)

theorem solvableRadical_map_mulEquiv (e : A ≃* B) :
    (CFSG.solvableRadical A).map e.toMonoidHom = CFSG.solvableRadical B := by
  change MulEquiv.mapSubgroup e (sSup {N : Subgroup A | N.Normal ∧ Group.IsSolvable N}) =
    sSup {N : Subgroup B | N.Normal ∧ Group.IsSolvable N}
  rw [OrderIso.map_sSup, ← sSup_image]
  refine congrArg sSup (Set.ext fun N' => ⟨?_, fun hN' => ?_⟩)
  · rintro ⟨N, ⟨hn, hs⟩, rfl⟩
    exact ⟨hn.map _ e.surjective, isSolvable_map_mulEquiv e hs⟩
  · refine ⟨N'.map e.symm.toMonoidHom, ⟨hN'.1.map _ e.symm.surjective,
      isSolvable_map_mulEquiv e.symm hN'.2⟩, ?_⟩
    exact CFSG.LocalCores.map_map_symm e.symm N' |> fun h => by simpa using h

theorem isSubnormal_not_isSolvable_map_mulEquiv (e : A ≃* B) {S : Subgroup A} :
    ((S.map e.toMonoidHom).IsSubnormal ∧ ¬ Group.IsSolvable (S.map e.toMonoidHom)) ↔
      (S.IsSubnormal ∧ ¬ Group.IsSolvable S) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun hs => h2 (isSolvable_map_mulEquiv e hs)⟩
    have := h1.map (f := e.symm.toMonoidHom) e.symm.surjective
    rwa [CFSG.LocalCores.map_map_symm] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1.map (f := e.toMonoidHom) e.surjective, fun hs => h2 ?_⟩
    have := isSolvable_map_mulEquiv e.symm hs
    rwa [CFSG.LocalCores.map_map_symm] at this

theorem isSolComponent_map_mulEquiv_iff [Finite A] (e : A ≃* B) {K : Subgroup A} :
    IsSolComponent (K.map e.toMonoidHom) ↔ IsSolComponent K := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  rw [isSolComponent_iff_minimal, isSolComponent_iff_minimal]
  constructor
  · rintro ⟨hK, hmin⟩
    refine ⟨(isSubnormal_not_isSolvable_map_mulEquiv e).mp hK, fun S hS hSK => ?_⟩
    have h1 := hmin ((isSubnormal_not_isSolvable_map_mulEquiv e).mpr hS)
      (Subgroup.map_mono hSK)
    have h2 := Subgroup.map_mono (f := e.symm.toMonoidHom) h1
    rwa [CFSG.LocalCores.map_map_symm, CFSG.LocalCores.map_map_symm] at h2
  · rintro ⟨hK, hmin⟩
    refine ⟨(isSubnormal_not_isSolvable_map_mulEquiv e).mpr hK, fun S hS hSK => ?_⟩
    have hS' := (isSubnormal_not_isSolvable_map_mulEquiv e.symm).mpr hS
    have hSK' : S.map e.symm.toMonoidHom ≤ K := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hSK
      rwa [CFSG.LocalCores.map_map_symm] at this
    have h1 := Subgroup.map_mono (f := e.toMonoidHom) (hmin hS' hSK')
    rwa [map_symm_map_mulEquiv] at h1

theorem solLayer_map_mulEquiv [Finite A] (e : A ≃* B) :
    (solLayer A).map e.toMonoidHom = solLayer B := by
  change MulEquiv.mapSubgroup e (sSup {K : Subgroup A | IsSolComponent K}) =
    sSup {K : Subgroup B | IsSolComponent K}
  rw [OrderIso.map_sSup, ← sSup_image]
  refine congrArg sSup (Set.ext fun K => ⟨?_, fun hK => ?_⟩)
  · rintro ⟨K', hK', rfl⟩
    exact (isSolComponent_map_mulEquiv_iff e).mpr hK'
  · have : Finite B := Finite.of_equiv A e.toEquiv
    have hback : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := map_symm_map_mulEquiv e K
    refine ⟨K.map e.symm.toMonoidHom, ?_, hback⟩
    exact (isSolComponent_map_mulEquiv_iff (K := K.map e.symm.toMonoidHom) e).mp
      (by rw [hback]; exact hK)

theorem oStar_map_mulEquiv [Finite A] (e : A ≃* B) :
    (oStar A).map e.toMonoidHom = oStar B := by
  change (CFSG.solvableRadical A ⊔ solLayer A).map e.toMonoidHom =
    CFSG.solvableRadical B ⊔ solLayer B
  rw [Subgroup.map_sup, solvableRadical_map_mulEquiv, solLayer_map_mulEquiv]

end IsoCompat

theorem isSolComponent_map_subtype_of_isSubnormal [Finite G] {H : Subgroup G}
    (hH : H.IsSubnormal) {K' : Subgroup H} (hK' : IsSolComponent K') :
    IsSolComponent (K'.map H.subtype) := by
  rw [isSolComponent_iff_minimal] at hK' ⊢
  obtain ⟨⟨hsub, hns⟩, hmin⟩ := hK'
  refine ⟨⟨Subgroup.IsSubnormal.trans' hsub hH, fun hs => hns ?_⟩, fun S hS hSK => ?_⟩
  · exact isSolvable_of_mulEquiv (K'.equivMapOfInjective H.subtype H.subtype_injective).symm
  · have hSH : S ≤ H := hSK.trans (Subgroup.map_subtype_le _)
    have hS' : (S.subgroupOf H).IsSubnormal := hS.1.subgroupOf
    have hns' : ¬ Group.IsSolvable (S.subgroupOf H) := fun hs =>
      hS.2 (isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSH))
    have hle : S.subgroupOf H ≤ K' := by
      intro x hx
      have hxS : (x : G) ∈ S := hx
      obtain ⟨y, hy, hyx⟩ := hSK hxS
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    have h1 := hmin ⟨hS', hns'⟩ hle
    rintro g ⟨k, hk, rfl⟩
    exact h1 hk

theorem map_subtype_solLayer_le [Finite G] {H : Subgroup G} (hH : H.IsSubnormal) :
    (solLayer H).map H.subtype ≤ solLayer G := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K' hK' => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_solLayer (isSolComponent_map_subtype_of_isSubnormal hH hK')

theorem oStar_map_subtype_le_oStar [Finite G] {H : Subgroup G} (hH : H.IsSubnormal) :
    (oStar H).map H.subtype ≤ oStar G := by
  change (CFSG.solvableRadical H ⊔ solLayer H).map H.subtype ≤
    CFSG.solvableRadical G ⊔ solLayer G
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ (map_subtype_solLayer_le hH)
  rw [map_subtype_solvableRadical_eq_inf hH]
  exact inf_le_right

theorem kOf_eq_of_kOf_le [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y) (h : kOf Y ≤ X) :
    kOf X = kOf Y := by
  have h1 : oStar ↥Y ≤ X.subgroupOf Y := by
    rw [← subgroupOf_kOf Y]
    exact Subgroup.subgroupOf_mono Y h
  have h2 := oStar_map_eq h1
  let e := Subgroup.subgroupOfEquivOfLe hXY
  have h3 : (oStar ↥(X.subgroupOf Y)).map e.toMonoidHom = oStar ↥X := oStar_map_mulEquiv e
  have hcomp : X.subtype.comp e.toMonoidHom = Y.subtype.comp (X.subgroupOf Y).subtype := rfl
  calc kOf X = ((oStar ↥(X.subgroupOf Y)).map e.toMonoidHom).map X.subtype := by rw [h3]; rfl
    _ = (oStar ↥(X.subgroupOf Y)).map (X.subtype.comp e.toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = ((oStar ↥(X.subgroupOf Y)).map (X.subgroupOf Y).subtype).map Y.subtype := by
        rw [hcomp, ← Subgroup.map_map]
    _ = kOf Y := by rw [h2]; rfl

theorem kOf_kOf [Finite G] (X : Subgroup G) : kOf (kOf X) = kOf X :=
  kOf_eq_of_kOf_le (kOf_le X) le_rfl

theorem mem_lcalOf_of_mem_simpleComponents_top {H : Type*} [Group H] {T : Subgroup H}
    (hT : T ∈ simpleComponents (⊤ : Subgroup H)) : T ∈ lcalOf H := by
  obtain ⟨-, hn, hs, x, hx, y, hy, hxy⟩ := hT
  have hnormal : T.Normal :=
    ⟨fun h hh g => (Subgroup.normal_subgroupOf_iff le_top).mp hn h g hh trivial⟩
  refine ⟨hnormal.isSubnormal, hs, fun hcomm => hxy ?_⟩
  exact congrArg Subtype.val ((isMulCommutative_iff.mp hcomm) ⟨x, hx⟩ ⟨y, hy⟩)

theorem kOf_eq_self_iff_oStar_eq_top (X : Subgroup G) : kOf X = X ↔ oStar ↥X = ⊤ := by
  constructor
  · intro h
    rw [← subgroupOf_kOf, h, Subgroup.subgroupOf_self]
  · intro h
    change (oStar ↥X).map X.subtype = X
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem oStar_eq_top_iff_layer_eq_top [Finite G] (X : Subgroup G) :
    oStar ↥X = ⊤ ↔ CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X) = ⊤ := by
  rw [oStar_eq_comap_layer]
  constructor
  · intro h
    have := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical ↥X))) h
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  · intro h
    rw [h, Subgroup.comap_top]

theorem isKSubgroup_iff_kOf_eq_self [Finite G] (X : Subgroup G) : IsKSubgroup X ↔ kOf X = X := by
  rw [kOf_eq_self_iff_oStar_eq_top, oStar_eq_top_iff_layer_eq_top]
  constructor
  · intro h
    refine top_unique ?_
    rw [← h.sSup_eq]
    refine sSup_le fun T hT => ?_
    have hT' := mem_lcalOf_of_mem_simpleComponents_top hT
    rw [lcalOf_eq_components solvableRadical_quotient] at hT'
    exact CFSG.LocalCores.component_le_layer hT'
  · intro h
    have := isSemisimple_layer_quotient X
    rwa [h] at this

theorem kOf_isKSubgroup [Finite G] (X : Subgroup G) : IsKSubgroup (kOf X) :=
  (isKSubgroup_iff_kOf_eq_self _).mpr (kOf_kOf X)

theorem le_kOf_of_isKSubgroup [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hK : IsKSubgroup N) : N ≤ kOf X := by
  have hNk : oStar ↥N = ⊤ :=
    (kOf_eq_self_iff_oStar_eq_top N).mp ((isKSubgroup_iff_kOf_eq_self N).mp hK)
  let e := Subgroup.subgroupOfEquivOfLe hNX
  have h1 : oStar ↥(N.subgroupOf X) = ⊤ := by
    have h2 := oStar_map_mulEquiv e
    rw [hNk] at h2
    exact Subgroup.map_injective e.injective
      (h2.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)
  have h3 := oStar_map_subtype_le_oStar hN.isSubnormal
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
  have h4 := Subgroup.map_mono (f := X.subtype) h3
  rwa [Subgroup.map_subgroupOf_eq_of_le hNX] at h4

theorem khat_eq_self_of_kOf_eq_self [Finite G] {X : Subgroup G} (h : kOf X = X) : khat X = X := by
  by_cases hX : Group.IsSolvable X
  · exact khat_eq_of_isSolvable hX
  · refine le_antisymm (khat_le X) ?_
    refine le_inf le_rfl (le_iInf₂ fun M hM => ?_)
    have hM' : M ∈ mcal X := by
      rcases hM with ⟨hs, -⟩ | ⟨-, hm⟩
      · exact absurd hs hX
      · exact hm
    obtain ⟨hMX, hsol, hbar⟩ := hM'
    have hlayer : CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X) = ⊤ :=
      (oStar_eq_top_iff_layer_eq_top X).mp ((kOf_eq_self_iff_oStar_eq_top X).mp h)
    have hdp := isDirectProduct_lcalOf_layer
      (solvableRadical_quotient (G := ↥X))
    rw [hlayer] at hdp
    have hnorm : Subgroup.normalizer
        (((M.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) :
          Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) : Set (↥X ⧸ CFSG.solvableRadical ↥X)) = ⊤ :=
      top_le_iff.mp (hdp.le_normalizer hbar)
    have hMnormal : ((M.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X))).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hnorm
    have hker : (QuotientGroup.mk' (CFSG.solvableRadical ↥X)).ker ≤ M.subgroupOf X := by
      rw [QuotientGroup.ker_mk', ← subgroupOf_sol]
      exact Subgroup.subgroupOf_mono X hsol
    have hcomap : (M.subgroupOf X) = ((M.subgroupOf X).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥X))).comap
          (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) :=
      (Subgroup.comap_map_eq_self hker).symm
    have hMn : (M.subgroupOf X).Normal := by
      rw [hcomap]
      exact hMnormal.comap _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).mp hMn

theorem sol_eq_bot_of_kDown_eq_bot {X A : Subgroup G} (h : kDown X A = ⊥) : sol X = ⊥ :=
  eq_bot_iff.mpr (h ▸ sol_le_kDown X A)

end CFSG.SignalizerFunctorTheorem.McBride
