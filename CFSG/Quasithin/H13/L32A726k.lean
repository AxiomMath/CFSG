module

public import CFSG.Quasithin.H13.L32A726j
public import CFSG.Quasithin.H13.L32A726R
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem not_isCyclic_of_elem_726 {E : Subgroup G} (he : IsElemAbelian 3 E)
    (hc : Nat.card E = 9) : ¬ IsCyclic ↥E := by
  intro hcyc
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using he.2 g g.2)
  have h := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hc] at h
  norm_num at h

omit [Finite G] in
theorem conj_mem_centralizer_726 {M : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (hc : c ∈ Subgroup.centralizer (M : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro m hm
  have hm' : g⁻¹ * m * g ∈ M := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) m).mp hm
    simpa using this
  have h := hc _ hm'
  calc m * (g * c * g⁻¹) = g * ((g⁻¹ * m * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * m * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * m := by group

section Ctx

variable {T L V H D : Subgroup G}

theorem three_dvd_card_of_isComponentIn_726 (h121 : Id2519.Prop121Three)
    (hlist : Lemma115_3_List) (hSz : KG14726Sz) (hc : Ctx726 G T L V H D) {d : G}
    (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {z : G}
    (hyp : Lemma115Hyp (Subgroup.centralizer ({d} : Set G))
      (T ⊓ Subgroup.centralizer ({d} : Set G)) H z)
    {x : G} {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Ld : Subgroup G} (hLd : IsComponentIn Ld (Subgroup.centralizer ({d} : Set G))) :
    3 ∣ Nat.card Ld := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hc.setting.hyp.fsu.simple
  obtain ⟨-, -, hnotle, hcases⟩ := hlist.component_cases hc.setting.hyp.fsu.simple
    hc.setting.hyp.fsu.nonabelian
    (QuasithinUnique.qtkeCore_of_cat hc.setting.hyp.fsu.nonabelian hc.setting.hyp.fsu.qtke) hyp
    hLd
  have hKN := k_le_normalizer_of_mem_cComp_726 h121 hc hdD hdV hd2 inf_le_right le_rfl
    (Id2519.mem_cComp_of_isComponentIn hLd)
  by_contra h3
  have hYN : Y ≤ Subgroup.normalizer (Ld : Set G) := hX.y_le.trans hKN
  set f : ↥Y →* MulAut ↥Ld := (Subgroup.normalizerMonoidHom Ld).comp (Subgroup.inclusion hYN)
    with hf
  have hcyc : IsCyclic ↥f.range := hSz G Ld z hcases
    (BenderBranch.isQuasisimple_of_isComponentIn hLd) h3 f.range
    (hX.y_pgroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
    let e : ↥Y ≃* ↥f.range := MulEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
    have hYc : IsCyclic ↥Y := isCyclic_of_surjective e.symm e.symm.surjective
    exact not_isCyclic_of_elem_726 hX.e₁_elem hX.e₁_card
      (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX.e₁_le)
        (Subgroup.subgroupOfEquivOfLe hX.e₁_le).surjective)
  obtain ⟨y, hyk, hyx⟩ := mem_of_normal_y_726 hc hX (Subgroup.map_subtype_le f.ker)
    (le_normalizer_map_726 f.normal_ker)
    (fun h => hker ((Subgroup.map_eq_bot_iff_of_injective f.ker Y.subtype_injective).mp h))
  have hxC : x ∈ Subgroup.centralizer (Ld : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    have h1 : ((f y ⟨ℓ, hℓ⟩ : ↥Ld) : G) = ℓ := by
      rw [MonoidHom.mem_ker.mp hyk]
      rfl
    have h2 : ((f y ⟨ℓ, hℓ⟩ : ↥Ld) : G) = x * ℓ * x⁻¹ := by
      rw [← hyx]
      rfl
    rw [h2] at h1
    calc ℓ * x = (x * ℓ * x⁻¹) * x := by rw [h1]
      _ = x * ℓ := by group
  have hL1C : L32A.l1 T L V ≤ Subgroup.centralizer (Ld : Set G) := by
    refine (l1_le_conjClosure_726 hc hX.x_mem hX.x_order).trans
      (conjClosure_le fun p hp w hw => ?_)
    exact conj_mem_centralizer_726 (hKN ((l1_le_k_726 hc) (pCoreOf_le 2 _ hp)))
      ((Subgroup.zpowers_le.mpr hxC) hw)
  exact hnotle ((Subgroup.le_centralizer_iff.mp hL1C).trans
    ((Subgroup.centralizer_le_normalizer _).trans (normalizer_l1_le_726 hc)))

theorem exists_normal_component_726 (hC129 : ASC129Statement G) (h121 : Id2519.Prop121Three)
    (hC27 : KG14726C27C) (h3x : NQCore.Prop134ThreeExtraspecial) (hlist : Lemma115_3_List)
    (hSz : KG14726Sz) (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V)
    (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t)
    (hGdH : ¬ Subgroup.centralizer ({d} : Set G) ≤ H) {x : G} {Y E₁ E₂ : Subgroup G}
    (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂) :
    ∃ Ld : Subgroup G, IsComponentIn Ld (Subgroup.centralizer ({d} : Set G)) ∧ x ∈ Ld ∧
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (Ld : Set G) := by
  obtain ⟨Ld, hLd⟩ := exists_component_726 hC129 h121 hC27 h3x hc hdD hdV hd2 htT htd hGdH
  obtain ⟨z, -, hz1, hz2, hzT, hzc, hzH⟩ := exists_z_726 hc hdD hdV
  have hyp := lemma115Hyp_726 hc hdD hdV hd2 htT htd hz1 hz2 hzT hzc hzH
  have hodd := oddCoreModTwoTrivial_gd_726 hC129 h3x hc hdD hdV hd2 htT htd hGdH
  have hLdc := Id2519.mem_cComp_of_isComponentIn hLd
  have h3 := three_dvd_card_of_isComponentIn_726 h121 hlist hSz hc hdD hdV hd2 hyp hX hLd
  have hxLd := mem_of_mem_cComp_of_three_dvd_726 h121 hc hdD hdV hd2 inf_le_right le_rfl hX hLdc
    h3
  refine ⟨Ld, hLd, hxLd, fun h hh => ?_⟩
  have hc' : CFSG.conjugate Ld h ∈ cComp (Subgroup.centralizer ({d} : Set G)) :=
    C2Nine.conjByElt_mem_cComp hLdc (Subgroup.le_normalizer (Subgroup.inv_mem _ hh))
  have h3' : 3 ∣ Nat.card (CFSG.conjugate Ld h) := by
    rw [show Nat.card (CFSG.conjugate Ld h) = Nat.card Ld from
      Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact h3
  exact conjugate_eq_self_iff_726.mp (eq_of_mem_cComp_726 hodd hc' hLdc hX.x_order
    (mem_of_mem_cComp_of_three_dvd_726 h121 hc hdD hdV hd2 inf_le_right le_rfl hX hc' h3') hxLd)

end Ctx

end CFSG.Quasithin.H13.L32A
