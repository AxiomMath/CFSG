module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem fitting_eq_bot_of_solvableRadical_eq_bot {H : Type*} [Group H] [Finite H]
    (h : CFSG.solvableRadical H = ⊥) : CFSG.fittingSubgroup H = ⊥ := by
  have := (CFSG.LocalCores.fitting_nilpotent (G := H)).1
  rw [eq_bot_iff, ← h]
  exact Nonsolvable.le_solvableRadical inferInstance inferInstance

theorem generalizedFitting_eq_layer_of_solvableRadical_eq_bot {H : Type*} [Group H] [Finite H]
    (h : CFSG.solvableRadical H = ⊥) : CFSG.generalizedFitting H = CFSG.layer H := by
  rw [CFSG.generalizedFitting, fitting_eq_bot_of_solvableRadical_eq_bot h, bot_sup_eq]

private theorem not_isMulCommutative_iff {H : Type*} [Group H] {J : Subgroup H} :
    ¬ IsMulCommutative J ↔ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
  rw [isMulCommutative_iff]
  push Not
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, fun h' => h (Subtype.ext h')⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h' => h (congrArg Subtype.val h')⟩

theorem lcalOf_eq_components {H : Type*} [Group H] [Finite H]
    (h : CFSG.solvableRadical H = ⊥) : lcalOf H = {J | CFSG.IsComponent J} := by
  ext J
  constructor
  · rintro ⟨hsub, hsimple, hnab⟩
    have hnab' : ∃ a b : J, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      exact hnab (isMulCommutative_iff.mpr hc)
    exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').1, hsub⟩
  · rintro ⟨hq, hsub⟩
    have hZsub : ((Subgroup.center J).map J.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hsub
    have hZs : Group.IsSolvable ((Subgroup.center J).map J.subtype) :=
      Nonsolvable.isSolvable_of_mulEquiv
        (Subgroup.equivMapOfInjective (Subgroup.center J) J.subtype J.subtype_injective)
    have hZ : Subgroup.center J = ⊥ := by
      have := Nonsolvable.le_solvableRadical_of_isSubnormal hZsub hZs
      rw [h, le_bot_iff] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp this
    obtain ⟨-, hs, a, b, hab⟩ := hq
    let e : J ⧸ Subgroup.center J ≃* J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    refine ⟨hsub, e.symm.isSimpleGroup, fun hc => hab ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm' a b]

private theorem eq_one_of_mem_of_forall_commute {H : Type*} [Group H] {J : Subgroup H}
    (hs : IsSimpleGroup J) (hn : ¬ IsMulCommutative J) {x : H} (hxJ : x ∈ J)
    (hx : ∀ y ∈ J, y * x = x * y) : x = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := not_isMulCommutative_iff.mp hn
  have hZ : Subgroup.center J = ⊥ :=
    Diagonal.center_eq_bot ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hmem : (⟨x, hxJ⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    exact fun y => Subtype.ext (hx y y.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem isDirectProduct_lcalOf_layer {H : Type*} [Group H] [Finite H]
    (h : CFSG.solvableRadical H = ⊥) : IsDirectProduct (lcalOf H) (CFSG.layer H) := by
  have hL := lcalOf_eq_components h
  have hcomm : ∀ J ∈ lcalOf H, ∀ L ∈ lcalOf H, J ≠ L → ∀ x ∈ J, ∀ y ∈ L, Commute x y := by
    intro J hJ L hL' hne x hx y hy
    rw [hL] at hJ hL'
    rcases CFSG.LocalCores.distinct_components_commute hJ hL' with h' | h'
    · exact absurd h' hne
    · exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h' hx) y hy).symm
  refine ⟨hcomm, fun J hJ => ?_, by rw [hL]; rfl⟩
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxJ, hxL⟩
  have hle : sSup (lcalOf H \ {J}) ≤ Subgroup.centralizer (J : Set H) := by
    refine sSup_le fun L hL' y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun z hz => (hcomm J hJ L hL'.1 (fun h => hL'.2 h.symm) z hz y hy).eq
  have hx := Subgroup.mem_centralizer_iff.mp (hle hxL)
  obtain ⟨hs, hn⟩ : IsSimpleGroup J ∧ ¬ IsMulCommutative J := hJ.2
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_of_forall_commute hs hn hxJ hx)

theorem simpleComponents_layer {H : Type*} [Group H] [Finite H]
    (h : CFSG.solvableRadical H = ⊥) :
    Nonsolvable.simpleComponents (CFSG.layer H) = lcalOf H := by
  ext T
  constructor
  · rintro ⟨hTL, hTn, hTs, hTnab⟩
    have : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
    exact ⟨Subgroup.IsSubnormal.trans hTL (Subgroup.Normal.isSubnormal hTn)
      (Subgroup.Normal.isSubnormal inferInstance), hTs, not_isMulCommutative_iff.mpr hTnab⟩
  · intro hT
    have hc : CFSG.IsComponent T := (lcalOf_eq_components h).subset hT
    obtain ⟨-, hs, hn⟩ := hT
    obtain ⟨hle, hnorm⟩ := CFSG.LocalCores.components_normal_in_layer hc
    exact ⟨hle, hnorm, hs, not_isMulCommutative_iff.mp hn⟩

theorem isSemisimple_layer {H : Type*} [Group H] [Finite H] (h : CFSG.solvableRadical H = ⊥) :
    IsSemisimple (CFSG.layer H) := by
  show IsDirectProduct (Nonsolvable.simpleComponents (CFSG.layer H)) (CFSG.layer H)
  rw [simpleComponents_layer h]
  exact isDirectProduct_lcalOf_layer h

theorem map_layer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem kOf_eq_map_layer [Finite G] {X : Subgroup G} (h : sol X = ⊥) :
    kOf X = (CFSG.layer ↥X).map X.subtype := by
  have hR : CFSG.solvableRadical ↥X = ⊥ := (sol_eq_bot_iff X).mp h
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]
  let φ : ↥X ≃* (↥X ⧸ CFSG.solvableRadical ↥X) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.solvableRadical ↥X))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have h1 : (CFSG.layer ↥X).map φ.toMonoidHom = CFSG.layer (↥X ⧸ CFSG.solvableRadical ↥X) :=
    map_layer_mulEquiv φ
  unfold kOf
  rw [Nonsolvable.oStar_eq_comap_layer, ← h1]
  congr 1
  exact Subgroup.comap_map_eq_self_of_injective hinj _

theorem lcal_eq_image (X : Subgroup G) : lcal X = (Subgroup.map X.subtype) '' lcalOf ↥X := by
  ext J
  constructor
  · rintro ⟨hJX, hJ⟩
    exact ⟨J.subgroupOf X, hJ, Subgroup.map_subgroupOf_eq_of_le hJX⟩
  · rintro ⟨J', hJ', rfl⟩
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    change (J'.map X.subtype).comap X.subtype ∈ lcalOf ↥X
    rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]

theorem IsDirectProduct.map {H : Type*} [Group H] {f : H →* G} (hf : Function.Injective f)
    {S : Set (Subgroup H)} {K : Subgroup H} (hK : IsDirectProduct S K) :
    IsDirectProduct ((Subgroup.map f) '' S) (K.map f) where
  commute := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hK.commute J hJ L hL (fun h => hne (h ▸ rfl)) x hx y hy).map f
  indep := by
    rintro _ ⟨J, hJ, rfl⟩
    have h1 : (Subgroup.map f) '' S \ {J.map f} = (Subgroup.map f) '' (S \ {J}) := by
      ext L
      constructor
      · rintro ⟨⟨L', hL', rfl⟩, hne⟩
        exact ⟨L', ⟨hL', fun h => hne (h ▸ rfl)⟩, rfl⟩
      · rintro ⟨L', ⟨hL', hne⟩, rfl⟩
        exact ⟨⟨L', hL', rfl⟩, fun h => hne (Subgroup.map_injective hf h)⟩
    have h2 : sSup ((Subgroup.map f) '' (S \ {J})) = (sSup (S \ {J})).map f := by
      rw [sSup_image, (Subgroup.gc_map_comap f).l_sSup]
    rw [h1, h2, disjoint_iff, ← Subgroup.map_inf_eq _ _ f hf, disjoint_iff.mp (hK.indep hJ),
      Subgroup.map_bot]
  sSup_eq := by
    rw [sSup_image, ← (Subgroup.gc_map_comap f).l_sSup, hK.sSup_eq]

theorem simpleComponents_map {H : Type*} [Group H] {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup H) :
    Nonsolvable.simpleComponents (K.map f) =
      (Subgroup.map f) '' Nonsolvable.simpleComponents K := by
  ext T
  constructor
  · rintro ⟨hTK, hTn, hTs, hTnab⟩
    have hmap : (T.comap f).map f = T :=
      Subgroup.map_comap_eq_self (hTK.trans (Subgroup.map_le_range f K))
    have hle : T.comap f ≤ K := by
      have := Subgroup.comap_mono (f := f) hTK
      rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
    refine ⟨T.comap f, ⟨hle, ?_, ?_, ?_⟩, hmap⟩
    · rw [Subgroup.normal_subgroupOf_iff hle]
      intro h k hh hk
      have := (Subgroup.normal_subgroupOf_iff hTK).mp hTn (f h) (f k) hh
        (Subgroup.mem_map_of_mem f hk)
      simpa using this
    · have : IsSimpleGroup ↥((T.comap f).map f) := by rw [hmap]; exact hTs
      exact (Subgroup.equivMapOfInjective (T.comap f) f hf).isSimpleGroup
    · obtain ⟨x, hx, y, hy, hxy⟩ := hTnab
      rw [← hmap] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x', hx', y', hy', fun h => hxy (by rw [← map_mul, ← map_mul, h])⟩
  · rintro ⟨T', ⟨hT'K, hT'n, hT's, hT'nab⟩, rfl⟩
    refine ⟨Subgroup.map_mono hT'K, ?_, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hT'K)]
      rintro _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
      exact ⟨k * h * k⁻¹, (Subgroup.normal_subgroupOf_iff hT'K).mp hT'n h k hh hk, by simp⟩
    · exact (Subgroup.equivMapOfInjective T' f hf).symm.isSimpleGroup
    · obtain ⟨x, hx, y, hy, hxy⟩ := hT'nab
      exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩,
        fun h => hxy (hf (by rw [map_mul, map_mul, h]))⟩

theorem simpleComponents_kOf [Finite G] {X : Subgroup G} (h : sol X = ⊥) :
    Nonsolvable.simpleComponents (kOf X) = lcal X := by
  rw [kOf_eq_map_layer h, simpleComponents_map X.subtype_injective, lcal_eq_image,
    simpleComponents_layer ((sol_eq_bot_iff X).mp h)]

theorem isDirectProduct_lcal_kOf [Finite G] {X : Subgroup G} (h : sol X = ⊥) :
    IsDirectProduct (lcal X) (kOf X) := by
  rw [lcal_eq_image, kOf_eq_map_layer h]
  exact (isDirectProduct_lcalOf_layer ((sol_eq_bot_iff X).mp h)).map X.subtype_injective

theorem isSemisimple_kOf [Finite G] {X : Subgroup G} (h : sol X = ⊥) : IsSemisimple (kOf X) := by
  show IsDirectProduct (Nonsolvable.simpleComponents (kOf X)) (kOf X)
  rw [simpleComponents_kOf h]
  exact isDirectProduct_lcal_kOf h

theorem centralizer_kOf_eq_bot [Finite G] {X : Subgroup G} (h : sol X = ⊥) :
    X ⊓ Subgroup.centralizer (kOf X : Set G) = ⊥ := by
  have hC := Nonsolvable.centralizer_layer_eq_bot ((sol_eq_bot_iff X).mp h)
  rw [eq_bot_iff]
  rintro x ⟨hxX, hxC⟩
  have hx : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.layer ↥X : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (k : G) ∈ kOf X := by
      rw [kOf_eq_map_layer h]
      exact ⟨k, hk, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC k hk')
  rw [hC, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)

theorem kOf_inf_centralizer_eq_sSup_diff [Finite G] {X : Subgroup G} (h : sol X = ⊥)
    {J : Subgroup G} (hJ : J ∈ lcal X) :
    kOf X ⊓ Subgroup.centralizer (J : Set G) = sSup (lcal X \ {J}) := by
  have hK := isDirectProduct_lcal_kOf h
  have hP := hK.isDirectPair hJ
  obtain ⟨-, -, hs, hn⟩ : J ∈ Nonsolvable.simpleComponents (kOf X) :=
    (simpleComponents_kOf h).symm ▸ hJ
  apply le_antisymm
  · rintro z ⟨hzK, hzC⟩
    rw [← hP.sup_eq] at hzK
    obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute hP.commute).mp hzK
    have hjc : ∀ y ∈ J, y * j = j * y := by
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.mp hzC y hy
      have h2 := (hK.commute_sSup_diff hJ y hy l hl).eq
      have h3 : y * j * l = j * y * l := by
        calc y * j * l = y * (j * l) := mul_assoc _ _ _
          _ = j * l * y := h1
          _ = j * (l * y) := mul_assoc _ _ _
          _ = j * (y * l) := by rw [h2]
          _ = j * y * l := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    rw [eq_one_of_mem_of_forall_commute hs (not_isMulCommutative_iff.mpr hn) hj hjc, one_mul]
    exact hl
  · refine le_inf (hK.sSup_diff_le _ Set.sdiff_subset) fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => (hK.commute_sSup_diff hJ x hx y hy).eq

end CFSG.SignalizerFunctorTheorem.McBride
