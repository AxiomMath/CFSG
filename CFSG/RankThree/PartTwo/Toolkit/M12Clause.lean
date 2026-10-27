module

public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.Sporadic.J1

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Subgroup CFSG.RankThree.Asc83Table CFSG.Blueprint

universe u v

section Transport

variable {G : Type v} {G' : Type u} [Group G] [Group G'] (f : G ≃* G')

theorem centralizer_map_equiv (B : Subgroup G) :
    centralizer ((B.map f.toMonoidHom : Subgroup G') : Set G') =
      (centralizer (B : Set G)).map f.toMonoidHom :=
  (map_equiv_centralizer_eq f B).symm

theorem normalizer_map_equiv (B : Subgroup G) :
    normalizer ((B.map f.toMonoidHom : Subgroup G') : Set G') =
      (normalizer (B : Set G)).map f.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq B f).symm

theorem center_sub_map_equiv (P : Subgroup G) :
    (center (P.map f.toMonoidHom)).map (P.map f.toMonoidHom).subtype =
      ((center P).map P.subtype).map f.toMonoidHom := by
  rw [← CFSG.RankThree.PartOne.Torsion37.center_map_mulEquiv
    (P.equivMapOfInjective f.toMonoidHom f.injective), Subgroup.map_map, Subgroup.map_map]
  rfl

noncomputable def quotNormalizerCongr (P : Subgroup G) :
    (normalizer (P : Set G) ⧸ P.subgroupOf (normalizer (P : Set G))) ≃*
      (normalizer ((P.map f.toMonoidHom : Subgroup G') : Set G') ⧸
        (P.map f.toMonoidHom).subgroupOf
          (normalizer ((P.map f.toMonoidHom : Subgroup G') : Set G'))) :=
  QuotientGroup.congr _ _ (normalizerCongr f P) (by
    ext ⟨y, hy⟩
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨⟨x, hxN⟩, hx, hxy⟩
      rw [mem_subgroupOf] at hx
      refine ⟨x, hx, ?_⟩
      exact congrArg Subtype.val hxy
    · rintro ⟨x, hx, hxy⟩
      have hxN : x ∈ normalizer (P : Set G) := by
        rw [normalizer_map_equiv] at hy
        obtain ⟨x', hx', hxx'⟩ := mem_map.1 hy
        rwa [f.injective (hxy.trans hxx'.symm)]
      exact ⟨⟨x, hxN⟩, by rwa [mem_subgroupOf], Subtype.ext hxy⟩)

theorem map_conj_map (A : Subgroup G) (g : G) :
    (A.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem M12SylowData.map {P : Subgroup G} (h : M12SylowData P) :
    M12SylowData (P.map f.toMonoidHom) := by
  obtain ⟨hex, hcard, hexp, hQ, hQcard, hncard, hnine, E, F, A, A', hset, hE, hF, hA, hA',
    ⟨g, hg, hgA⟩, hautE, hautF, hcE, hcF, hautA, hautA', hNa, hNa'⟩ := h
  have himage : {B : Subgroup G' | B ≤ P.map f.toMonoidHom ∧ Nat.card B = 9} =
      (fun B : Subgroup G => B.map f.toMonoidHom) '' {B | B ≤ P ∧ Nat.card B = 9} := by
    ext B'
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hle, h9⟩
      refine ⟨B'.map f.symm.toMonoidHom, ⟨?_, ?_⟩, ?_⟩
      · have := Subgroup.map_mono (f := f.symm.toMonoidHom) hle
        rwa [Subgroup.map_map, show f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G by
          ext; simp, Subgroup.map_id] at this
      · rw [Subgroup.card_map_of_injective f.symm.injective, h9]
      · rw [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id G' by
          ext; simp, Subgroup.map_id]
    · rintro ⟨B, ⟨hle, h9⟩, rfl⟩
      exact ⟨Subgroup.map_mono hle, by rw [Subgroup.card_map_of_injective f.injective, h9]⟩
  have hinj : Function.Injective fun B : Subgroup G => B.map f.toMonoidHom :=
    Subgroup.map_injective f.injective
  refine ⟨CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (P.equivMapOfInjective f.toMonoidHom f.injective) hex,
    by rw [Subgroup.card_map_of_injective f.injective, hcard],
    by rw [← Monoid.exponent_eq_of_mulEquiv (P.equivMapOfInjective f.toMonoidHom f.injective),
      hexp],
    CFSG.GH74.M12.Hyp.isElementaryAbelian_of_mulEquiv (quotNormalizerCongr f P) hQ,
    by rw [← Nat.card_congr (quotNormalizerCongr f P).toEquiv, hQcard],
    by rw [himage, Set.ncard_image_of_injective _ hinj, hncard], ?_,
    E.map f.toMonoidHom, F.map f.toMonoidHom, A.map f.toMonoidHom, A'.map f.toMonoidHom,
    by rw [himage, hset]; simp [Set.image_insert_eq],
    ?_, ?_, ?_, ?_, ⟨f g, ?_, ?_⟩,
    ⟨(automizerCongr f E).symm.trans hautE.some⟩, ⟨(automizerCongr f F).symm.trans hautF.some⟩,
    by rw [centralizer_map_equiv, hcE], by rw [centralizer_map_equiv, hcF],
    ⟨(automizerCongr f A).symm.trans hautA.some⟩, ⟨(automizerCongr f A').symm.trans hautA'.some⟩,
    ?_, ?_⟩
  · intro B' hle h9
    have hB' : B' ∈ (fun B : Subgroup G => B.map f.toMonoidHom) '' {B | B ≤ P ∧ Nat.card B = 9} :=
      himage ▸ ⟨hle, h9⟩
    obtain ⟨B, ⟨hB, hB9⟩, rfl⟩ := hB'
    obtain ⟨hBe, hBz⟩ := hnine B hB hB9
    refine ⟨CFSG.GH74.M12.Hyp.isElementaryAbelian_of_mulEquiv
      (B.equivMapOfInjective f.toMonoidHom f.injective) hBe, ?_⟩
    rw [center_sub_map_equiv]
    exact Subgroup.map_mono hBz
  · rw [normalizer_map_equiv, normalizer_map_equiv]; exact Subgroup.map_mono hE
  · rw [normalizer_map_equiv, normalizer_map_equiv]; exact Subgroup.map_mono hF
  · rw [normalizer_map_equiv, normalizer_map_equiv,
      Subgroup.map_le_map_iff_of_injective f.injective]
    exact hA
  · rw [normalizer_map_equiv, normalizer_map_equiv,
      Subgroup.map_le_map_iff_of_injective f.injective]
    exact hA'
  · rw [normalizer_map_equiv]; exact Subgroup.mem_map_of_mem _ hg
  · rw [map_conj_map, hgA]
  · rintro _ ⟨a, ha, rfl⟩ hZ
    have hZ' : a ∉ (center P).map P.subtype := fun h' =>
      hZ (by rw [center_sub_map_equiv]; exact Subgroup.mem_map_of_mem _ h')
    obtain ⟨e⟩ := hNa a ha hZ'
    refine ⟨(MulEquiv.subgroupCongr ?_).trans ((normalizerCongr f (zpowers a)).symm.trans e)⟩
    rw [MonoidHom.map_zpowers]
  · rintro _ ⟨a, ha, rfl⟩ hZ
    have hZ' : a ∉ (center P).map P.subtype := fun h' =>
      hZ (by rw [center_sub_map_equiv]; exact Subgroup.mem_map_of_mem _ h')
    obtain ⟨e⟩ := hNa' a ha hZ'
    refine ⟨(MulEquiv.subgroupCongr ?_).trans ((normalizerCongr f (zpowers a)).symm.trans e)⟩
    rw [MonoidHom.map_zpowers]

end Transport

theorem m12ThreeLocalData (G : Type u) [Group G] (h : Nonempty (G ≃* NativeSporadic.M12)) :
    M12ThreeLocalData G := by
  obtain ⟨e⟩ := h
  intro P
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card G = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  have hP0 : Nat.card (M12.P0.map e.symm.toMonoidHom) = 3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, M12.card_P0, hcard,
      factorization_eq_of_eq Nat.prime_three (show 95040 = 3 ^ 3 * 3520 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := exists_sylow_eq_map hP0 P
  rw [hg, Subgroup.map_map]
  exact M12SylowData.map (e.symm.trans (MulAut.conj g)) M12.m12SylowData_P0

theorem j1ThreeRank (G : Type u) [Group G] (h : Nonempty (G ≃* NativeSporadic.J1)) :
    Nat.card G = 175560 ∧ CFSG.pRank 3 G = 1 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card G = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨hcard, ?_⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcard]; norm_num)
  have hE : IsElementaryAbelian 3 (zpowers x) := by
    rw [isElementaryAbelian_iff]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
        one_zpow]
  refine pRank_eq (by norm_num) hE (by rw [Nat.card_zpowers, hx, pow_one]) fun A hA => ?_
  obtain ⟨k, hk⟩ := (isPGroup_of_isElementaryAbelian hA).exists_card_eq
  have hdvd : 3 ^ k ∣ 175560 := hk ▸ hcard ▸ Subgroup.card_subgroup_dvd_card A
  rw [hk, pow_one]
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra h2
    push Not at h2
    interval_cases k <;> norm_num at hlt
  have : 3 ^ 2 ∣ 175560 := (pow_dvd_pow 3 hk2).trans hdvd
  norm_num at this

theorem toolkit_clause5 : M12J1ThreeLocal.{u} :=
  ⟨m12ThreeLocalData, j1ThreeRank⟩

end CFSG.RankThree.PartTwo.Toolkit
