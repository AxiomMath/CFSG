module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15pcr_false_of_comm {A : Type*} [Group A] {J : Subgroup A}
    (hJperf : ⁅J, J⁆ = J) (hJnt : Nontrivial ↥J)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) : False := by
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJperf
  have hnt : Nontrivial ↥J := hJnt
  have hcommut : IsMulCommutative ↥J := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  exact @Group.IsPerfect.not_isMulCommutative ↥J inferInstance hnt hperf hcommut

omit [Finite G] in
private theorem s15pcr_false_of_le_inf {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : MulAut (Vtil V₀ V hV)} {J : Subgroup (MulAut (Vtil V₀ V hV))}
    (hJperf : ⁅J, J⁆ = J) (hJnt : Nontrivial ↥J)
    (hJbar : J ≤ lBar V₀ V hV L)
    (hJx : J ≤ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom)
    (hcent : lBar V₀ V hV L ≤
      Subgroup.centralizer
        ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom : Set _)) : False := by
  refine s15pcr_false_of_comm hJperf hJnt ?_
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hcent (hJbar ha)) b (hJx hb)).symm

private theorem s15pcr_actual_component {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hH : IsComponentOf H (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥H) (hthree : 3 ∣ Nat.card ↥H)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
        c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) :
    ∃ C : Subgroup (Bar2 D.M), CFSG.IsComponent C ∧ C.map ψ = H ∧
      ∃ e ∈ C, orderOf e = 3 ∧ ∃ c ∈ C, e * c ≠ c * e := by
  obtain ⟨K, hK, hbarK, ⟨eK⟩⟩ :=
    exists_calC_cover_of_simple_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hH hsimple
  refine ⟨UC22.barImage D.M K, UC22.uc22p22l_barImage_isComponent hK, ?_, ?_⟩
  · exact barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbarK ψ hψ
  · have h3K : 3 ∣ Nat.card (Bar2 K) := by
      have hcard : Nat.card (Bar2 K) =
          Nat.card ↥H * Nat.card (Subgroup.center (Bar2 K)) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Bar2 K)),
          Nat.card_congr eK.toEquiv]
      rw [hcard]
      exact dvd_mul_of_dvd_left hthree _
    obtain ⟨eC⟩ := UC22.uc22p22l_barImage_equiv hK
    have h3C : 3 ∣ Nat.card ↥(UC22.barImage D.M K) := by
      rw [← Nat.card_congr eC.toEquiv]
      exact h3K
    have hqC : CFSG.Open.IsQuasisimple ↥(UC22.barImage D.M K) :=
      CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
        (UC22.uc22p22l_barImage_isComponent hK).1
    obtain ⟨e, heord, hecent⟩ :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
        hqC Nat.prime_three (by norm_num) h3C
    rw [Subgroup.mem_center_iff] at hecent
    push Not at hecent
    obtain ⟨c, hcne⟩ := hecent
    have hcne' : ((c : Bar2 D.M) * (e : Bar2 D.M)) ≠ ((e : Bar2 D.M) * (c : Bar2 D.M)) := by
      intro h
      exact hcne (Subtype.ext h)
    exact ⟨(e : Bar2 D.M), e.2, (Subgroup.orderOf_coe e).trans heord,
      (c : Bar2 D.M), c.2, fun h => hcne' h.symm⟩

theorem s15_eq_one_of_two_conj_simple_components_of_three_dvd_card
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hsimple : IsSimpleGroup ↥K)
    (hthree : 3 ∣ Nat.card ↥K) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  obtain ⟨_t, _htM, _ht2, _ht1, _htrk, hW⟩ := c.conc
  by_contra hsne
  have h1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have h2 : 2 ≤ s15 D.M V₀ V hV L := by omega
  have hs15 : (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard = s15 D.M V₀ V hV L := rfl
  obtain ⟨Hx, hHxmem, hHxne⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
      (by rw [hs15]; omega) (lBar V₀ V hV L)
  obtain ⟨x, hxM, hxHx⟩ := hHxmem
  have hxmap : (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ≠ lBar V₀ V hV L :=
    hxHx ▸ hHxne
  have hxnot : x ∉ Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    fun h => hxmap (Subgroup.mem_normalizer_iff_map_conj_eq.mp h)
  have hcrossBot : ⁅lBar V₀ V hV L,
      (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom⁆ = ⊥ :=
    (hW.2.1 x hxM hxnot).1
  have hcentH : lBar V₀ V hV L ≤
      Subgroup.centralizer
        ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcrossBot
  have hH2comp : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
      (Mbar D.M V₀ V hV) := CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK hg
  have hH3comp : IsComponentOf (K.map (MulAut.conj x).toMonoidHom)
      (Mbar D.M V₀ V hV) := CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK hxM
  have hH4comp : IsComponentOf ((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) (Mbar D.M V₀ V hV) :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hH2comp hxM
  have hsimple2 : IsSimpleGroup ↥(K.map (MulAut.conj g).toMonoidHom) :=
    (K.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).isSimpleGroup_congr.mp hsimple
  have hsimple3 : IsSimpleGroup ↥(K.map (MulAut.conj x).toMonoidHom) :=
    (K.equivMapOfInjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).isSimpleGroup_congr.mp hsimple
  have hsimple4 : IsSimpleGroup ↥((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) :=
    ((K.map (MulAut.conj g).toMonoidHom).equivMapOfInjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).isSimpleGroup_congr.mp hsimple2
  have hp1 : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hK.2.2.1)
  have hp2 : ⁅K.map (MulAut.conj g).toMonoidHom,
      K.map (MulAut.conj g).toMonoidHom⁆ = K.map (MulAut.conj g).toMonoidHom :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hH2comp.2.2.1)
  have hp3 : ⁅K.map (MulAut.conj x).toMonoidHom,
      K.map (MulAut.conj x).toMonoidHom⁆ = K.map (MulAut.conj x).toMonoidHom :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hH3comp.2.2.1)
  have hp4 : ⁅(K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom,
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom⁆ =
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hH4comp.2.2.1)
  have hnt1 : Nontrivial ↥K := hsimple.toNontrivial
  have hnt2 : Nontrivial ↥(K.map (MulAut.conj g).toMonoidHom) := hsimple2.toNontrivial
  have hnt3 : Nontrivial ↥(K.map (MulAut.conj x).toMonoidHom) := hsimple3.toNontrivial
  have hnt4 : Nontrivial ↥((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) := hsimple4.toNontrivial
  have hH1le : K ≤ lBar V₀ V hV L := by rw [hL]; exact le_sup_left
  have hH2le : K.map (MulAut.conj g).toMonoidHom ≤ lBar V₀ V hV L := by
    rw [hL]; exact le_sup_right
  have hHxeq : (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj x).toMonoidHom ⊔
        (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [hL, Subgroup.map_sup]
  have hH3le : K.map (MulAut.conj x).toMonoidHom ≤
      (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom := by
    rw [hHxeq]; exact le_sup_left
  have hH4le : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom ≤
      (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom := by
    rw [hHxeq]; exact le_sup_right
  have h12 : K ≠ K.map (MulAut.conj g).toMonoidHom := hne
  have h13 : K ≠ K.map (MulAut.conj x).toMonoidHom := by
    intro heq
    refine s15pcr_false_of_le_inf hp1 hnt1 hH1le ?_ hcentH
    rw [heq]; exact hH3le
  have h14 : K ≠ (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro heq
    refine s15pcr_false_of_le_inf hp1 hnt1 hH1le ?_ hcentH
    rw [heq]; exact hH4le
  have h23 : K.map (MulAut.conj g).toMonoidHom ≠ K.map (MulAut.conj x).toMonoidHom := by
    intro heq
    refine s15pcr_false_of_le_inf hp2 hnt2 hH2le ?_ hcentH
    rw [heq]; exact hH3le
  have h24 : K.map (MulAut.conj g).toMonoidHom ≠
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro heq
    refine s15pcr_false_of_le_inf hp2 hnt2 hH2le ?_ hcentH
    rw [heq]; exact hH4le
  have h34 : K.map (MulAut.conj x).toMonoidHom ≠
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro heq
    apply hne
    have hle1 : K ≤ K.map (MulAut.conj g).toMonoidHom :=
      (Subgroup.map_le_map_iff_of_injective (MulAut.conj x).injective).mp heq.le
    have hle2 : K.map (MulAut.conj g).toMonoidHom ≤ K :=
      (Subgroup.map_le_map_iff_of_injective (MulAut.conj x).injective).mp heq.ge
    exact le_antisymm hle1 hle2
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  have hcard2 : Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcard3 : Nat.card ↥(K.map (MulAut.conj x).toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcard4 : Nat.card ↥((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) =
      Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have h3H2 : 3 ∣ Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) := hcard2.symm ▸ hthree
  have h3H3 : 3 ∣ Nat.card ↥(K.map (MulAut.conj x).toMonoidHom) := hcard3.symm ▸ hthree
  have h3H4 : 3 ∣ Nat.card ↥((K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) := (hcard4.trans hcard2).symm ▸ hthree
  obtain ⟨D1, hD1c, hD1map, e1, he1, hord1, c1, hc1, hnc1⟩ :=
    s15pcr_actual_component c hK hsimple hthree ψ hψ
  obtain ⟨D2, hD2c, hD2map, e2, he2, hord2, c2, hc2, hnc2⟩ :=
    s15pcr_actual_component c hH2comp hsimple2 h3H2 ψ hψ
  obtain ⟨D3, hD3c, hD3map, e3, he3, hord3, c3, hc3, hnc3⟩ :=
    s15pcr_actual_component c hH3comp hsimple3 h3H3 ψ hψ
  obtain ⟨D4, hD4c, hD4map, e4, he4, hord4, c4, hc4, hnc4⟩ :=
    s15pcr_actual_component c hH4comp hsimple4 h3H4 ψ hψ
  have hD12 : D1 ≠ D2 := by
    intro heq
    exact h12 (hD1map.symm.trans ((by rw [heq] : D1.map ψ = D2.map ψ).trans hD2map))
  have hD13 : D1 ≠ D3 := by
    intro heq
    exact h13 (hD1map.symm.trans ((by rw [heq] : D1.map ψ = D3.map ψ).trans hD3map))
  have hD14 : D1 ≠ D4 := by
    intro heq
    exact h14 (hD1map.symm.trans ((by rw [heq] : D1.map ψ = D4.map ψ).trans hD4map))
  have hD23 : D2 ≠ D3 := by
    intro heq
    exact h23 (hD2map.symm.trans ((by rw [heq] : D2.map ψ = D3.map ψ).trans hD3map))
  have hD24 : D2 ≠ D4 := by
    intro heq
    exact h24 (hD2map.symm.trans ((by rw [heq] : D2.map ψ = D4.map ψ).trans hD4map))
  have hD34 : D3 ≠ D4 := by
    intro heq
    exact h34 (hD3map.symm.trans ((by rw [heq] : D3.map ψ = D4.map ψ).trans hD4map))
  have hmem : ∀ C ∈ ({D1, D2, D3, D4} : Finset (Subgroup (Bar2 D.M))),
      CFSG.IsComponent C ∧ ∃ e ∈ C, orderOf e = 3 ∧ ∃ c ∈ C, e * c ≠ c * e := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · exact ⟨hD1c, e1, he1, hord1, c1, hc1, hnc1⟩
    · exact ⟨hD2c, e2, he2, hord2, c2, hc2, hnc2⟩
    · exact ⟨hD3c, e3, he3, hord3, c3, hc3, hnc3⟩
    · exact ⟨hD4c, e4, he4, hord4, c4, hc4, hnc4⟩
  have hcard : ({D1, D2, D3, D4} : Finset (Subgroup (Bar2 D.M))).card = 4 :=
    Finset.card_eq_four.mpr
      ⟨D1, D2, D3, D4, hD12, hD13, hD14, hD23, hD24, hD34, rfl⟩
  have h4bar : 4 ≤ CFSG.pRank 3 (⊤ : Subgroup (Bar2 D.M)) := by
    have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_le_pRank_of_components
      Nat.prime_three ({D1, D2, D3, D4} : Finset (Subgroup (Bar2 D.M))) hmem
    rwa [hcard] at h
  have h4open : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (Bar2 D.M))]
    exact h4bar
  have h4M : 4 ≤ CFSG.Open.pRank 3 D.M := by
    rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
    exact h4open
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3
    Nat.prime_three (by norm_num) D.M D.maxLocal.1
  have h3 := c.std.h3
  omega


theorem s15_eq_one_of_two_conj_l2_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK2 : UC22.IsL2 ↥K 2) :
    s15 D.M V₀ V hV L = 1 :=
  s15_eq_one_of_two_conj_simple_components_of_three_dvd_card c hK hg hne hL
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK2)
    (by
      rw [UC22.uc22p22r_L2_card hK2]
      norm_num)

theorem s15_eq_one_of_two_conj_l3_two
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {g : MulAut (Vtil V₀ V hV)}
    (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hg : g ∈ Mbar D.M V₀ V hV)
    (hne : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hL : lBar V₀ V hV L = K ⊔ K.map (MulAut.conj g).toMonoidHom)
    (hK3 : IsL3 ↥K 1) :
    s15 D.M V₀ V hV L = 1 :=
  s15_eq_one_of_two_conj_simple_components_of_three_dvd_card c hK hg hne hL
    (isSimpleGroup_of_isL3 hK3)
    (by
      rw [card_eq_of_isL3 hK3]
      norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
