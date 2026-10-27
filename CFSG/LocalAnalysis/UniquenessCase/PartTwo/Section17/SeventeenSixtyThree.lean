module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem false_of_two_tori
    {D : Data G} {V₀ V L K : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hk1 : D.k = 1)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hThin : ThinList13)
    (hK : K ∈ calC D.M) (hKne : K ≠ L)
    {AK : Subgroup G} (hAKK : AK ≤ K) (hAKel : CFSG.Open.IsElemAbelian 3 AK)
    (hAKrank : 1 ≤ CFSG.Open.pRank 3 AK) (hAKperm : Permutes AK D.T) : False := by
  classical
  have hKM : K ≤ D.M := hK.1.le
  have hLM : L ≤ D.M := ctx.memC.1.le
  have hAKM : AK ≤ D.M := hAKK.trans hKM
  obtain ⟨A₀, hA₀L, hA₀el, hA₀rank, hA₀perm⟩ :=
    exists_elemAbelian_permutes_of_isL3 ctx.memC.1.le (ctx.hyp54.2 L ctx.memC).1 ctx.shapeL
  have hA₀M : A₀ ≤ D.M := hA₀L.trans hLM
  haveI hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent ctx.memC
  have hKcomp : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hK
  have hneComp : barImage D.M K ≠ barImage D.M L := by
    intro heq
    exact hKne (barImage_injOn_calC hK ctx.memC heq)
  have hcent : barImage D.M L ≤ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) :=
    s13_components_commute hns hLcomp hKcomp (Ne.symm hneComp)
  have hinf : barImage D.M L ⊓ barImage D.M K = ⊥ := by
    have h := s13_inf_iSup_eq_bot hns hLcomp {barImage D.M K} (by
      intro K' hK'
      rw [Finset.mem_singleton] at hK'
      subst hK'
      exact ⟨hKcomp, hneComp⟩)
    simpa using h
  have hcomm : ⁅A₀, AK⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haM : a ∈ D.M := hA₀M ha
    have hbM : b ∈ D.M := hAKM hb
    have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a, haM⟩ ∈ barImage D.M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hA₀L ha))
    have himgK : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ ∈ barImage D.M K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hAKK hb))
    have hc := Subgroup.mem_centralizer_iff.mp (hcent himg) _ himgK
    have hM : (a * b * a⁻¹ * b⁻¹) ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem haM hbM) (D.M.inv_mem haM)) (D.M.inv_mem hbM)
    have himg1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a * b * a⁻¹ * b⁻¹, hM⟩ = 1 := by
      have heq : (⟨a * b * a⁻¹ * b⁻¹, hM⟩ : ↥D.M) =
          ⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ := Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a, haM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a, haM⟩ from hc.symm]
      group
    have hker : (⟨a * b * a⁻¹ * b⁻¹, hM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
      rw [← QuotientGroup.eq_one_iff]; exact himg1
    exact Subgroup.mem_map_of_mem D.M.subtype hker
  have hdisj : A₀ ⊓ (AK ⊔ CFSG.Open.pCoreOf 2 D.M) = ⊥ := by
    have hmembar : ∀ {Y : Subgroup (Bar2 D.M)} {x : G}, x ∈ barPreimage D.M Y ↔
        ∃ hx : x ∈ D.M,
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hx⟩ ∈ Y := by
      intro Y x
      rw [barPreimage, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        subst hyx
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, hmk⟩
        exact ⟨⟨x, hx⟩, hmk, rfl⟩
    have hsup : AK ⊔ CFSG.Open.pCoreOf 2 D.M ≤ barPreimage D.M (barImage D.M K) := by
      rw [sup_le_iff]
      constructor
      · intro x hx
        rw [hmembar]
        exact ⟨hAKM hx, Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (hAKK hx))⟩
      · intro x hx
        rw [hmembar]
        have hxM : x ∈ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M hx
        refine ⟨hxM, ?_⟩
        have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ = 1 := by
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
          have hy2 : (⟨x, hxM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
            have hyx' : y = (⟨x, hxM⟩ : ↥D.M) := Subtype.ext hyx
            rwa [hyx'] at hy
          exact (QuotientGroup.eq_one_iff _).mpr hy2
        rw [h1]
        exact (barImage D.M K).one_mem
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxA₀, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ L := hA₀L hxA₀
    have hxM : x ∈ D.M := hLM hxL
    have hxpre0 : x ∈ barPreimage D.M (barImage D.M K) := hsup hxsup
    have hxpre : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ barImage D.M K := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxpre0
      have hy2 : y = (⟨x, hxM⟩ : ↥D.M) := Subtype.ext hyx
      rwa [hy2] at hy
    have hxK : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ barImage D.M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)
    have hxbot : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈
        barImage D.M L ⊓ barImage D.M K := ⟨hxK, hxpre⟩
    rw [hinf, Subgroup.mem_bot] at hxbot
    have hxO : x ∈ CFSG.Open.pCoreOf 2 D.M := by
      have hker : (⟨x, hxM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
        rw [← QuotientGroup.eq_one_iff]; exact hxbot
      exact Subgroup.mem_map_of_mem D.M.subtype hker
    have hcop : Nat.Coprime (Nat.card A₀) (Nat.card (CFSG.Open.pCoreOf 2 D.M)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA₀el.isPGroup
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
      rw [hk, hm]
      exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 2)).pow_right m
    have hdisjAO : A₀ ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hmem' : x ∈ A₀ ⊓ CFSG.Open.pCoreOf 2 D.M := ⟨hxA₀, hxO⟩
    rw [hdisjAO, Subgroup.mem_bot] at hmem'
    exact hmem'
  obtain ⟨n, hnO, hEel, hrankE, hpermE⟩ :=
    exists_conj_sup_isElemAbelian_permutes (D := D) hA₀M hAKM hA₀el hAKel
      hA₀perm hAKperm hcomm hdisj (by omega)
  have hnM : n ∈ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M hnO
  have hE'M : A₀ ⊔ AK.map (MulAut.conj n).toMonoidHom ≤ D.M := by
    refine sup_le hA₀M ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    exact D.M.mul_mem (D.M.mul_mem hnM (hAKM hy)) (D.M.inv_mem hnM)
  exact false_of_permuting_elemAbelian_rank_two_of_k_one (D := D) (h1 ctx.hyp125) hk1
    hE'M hEel hpermE hrankE

theorem false_of_bad_shape
    {D : Data G} {V₀ V L K : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hk1 : D.k = 1)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hThin : ThinList13)
    (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hshape : IsL3 (Bar2 K) 2 ∨ (∃ a : ℕ, Even a ∧ IsL2 (Bar2 K) a) ∨
      (∃ n : ℕ, Even n ∧ IsSU3 (Bar2 K) n)) : False := by
  have hKM : K ≤ D.M := hK.1.le
  have hKn : (K.subgroupOf D.M).Normal := (ctx.hyp54.2 K hK).1
  rcases hshape with hL3 | ⟨a, ha, hL2⟩ | ⟨n, hn, hU3⟩
  · obtain ⟨AK, hAKK, hAKel, hAKrank, hAKperm⟩ :=
      exists_elemAbelian_permutes_of_isL3 hKM hKn hL3
    exact false_of_two_tori ctx hk1 h1 hThin hK hKne hAKK hAKel hAKrank hAKperm
  · obtain ⟨AK, hAKK, hAKel, hAKrank, hAKperm⟩ :=
      exists_elemAbelian_permutes_of_isL2_even hKM hKn ha hL2
    exact false_of_two_tori ctx hk1 h1 hThin hK hKne hAKK hAKel hAKrank hAKperm
  · obtain ⟨AK, hAKK, hAKel, hAKrank, hAKperm⟩ :=
      exists_elemAbelian_permutes_of_isSU3_even hKM hKn hn hU3
    exact false_of_two_tori ctx hk1 h1 hThin hK hKne hAKK hAKel hAKrank hAKperm

theorem false_of_three_dvd_inf_map_conj {D : Data G} {K : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (hK : K ≤ D.M)
    {g : G} (hg : g ∉ D.M)
    (h3 : 3 ∣ Nat.card ↥(K ⊓ D.M.map (MulAut.conj g).toMonoidHom)) : False := by
  have hle : K ⊓ D.M.map (MulAut.conj g).toMonoidHom ≤
      D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := le_inf (inf_le_left.trans hK) inf_le_right
  exact (hsp.2.2 g hg) (h3.trans (Subgroup.card_dvd_of_le hle))

theorem seventeen_sixtythree
    (D : Data G) {V₀ V : Subgroup G}
    (h62 : R17_62At D V₀ V)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (h6_2 : R17_6_2At D V₀ V)
    (h17 : R17_17At D V₀ V)
    (h33 : R17_33_2At D V₀ V)
    (hThin : ThinList13) : R17_63At D V₀ V := by
  intro L p ctx K hK hKne
  have hk1 : D.k = 1 := h62 L p ctx
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    have hk2 : D.k = 2 := (Data.k_eq_two_iff D).2 h
    omega
  have hKM : K ≤ D.M := hK.1.le
  rcases shape_of_hyp1754 D ctx.hyp54 h33 K hK with hthin | ⟨n, hnEven, hU3⟩ | hL3
  · obtain ⟨-, hlist⟩ := s13_list_bar hThin D hK hthin
    rcases hlist with ⟨a, hL2⟩ | ⟨q, hq, hq2, hL2odd⟩ | ⟨a, hSz⟩ | hJ1
    · by_cases ha : Even a
      · exfalso
        exact false_of_bad_shape (D := D) ctx hk1 h1 hThin hK hKne
          (Or.inr (Or.inl ⟨a, ha, hL2⟩))
      · exact ⟨a, Nat.not_even_iff_odd.mp ha, Or.inl hL2⟩
    · by_cases hq5 : q = 5
      · have hL2 : IsL2 (Bar2 K) 2 := by
          rw [hq5] at hL2odd
          exact s13_isL2_two_of_isL2Odd_five hL2odd
        exfalso
        exact false_of_bad_shape (D := D) ctx hk1 h1 hThin hK hKne
          (Or.inr (Or.inl ⟨2, ⟨1, by norm_num⟩, hL2⟩))
      · have hq5' : 5 < q := by
          have := s13_five_le_of_isL2Odd hL2odd
          omega
        have hmodel := hL2odd
        have hLover : IsL2Over17 (Bar2 K) q :=
          ⟨q, 1, hq, hq2, (pow_one q).symm, le_rfl, hmodel⟩
        obtain ⟨e⟩ := SeventeenFourteen.barInf_equiv_bar2 hK hLover
        have hchev : IsChev (BarInf K) q :=
          ⟨.PSL, 2, 1, hmodel.admissible, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hmodel⟩
        obtain ⟨g, hgM, h3⟩ := h6_2 K hK q hq2 hchev hq5'
        exfalso
        exact false_of_three_dvd_inf_map_conj hsp hKM hgM h3.2
    · obtain ⟨haodd, -⟩ := s13_odd_three_le_of_isSz hSz
      exact ⟨a, haodd, Or.inr hSz⟩
    · obtain ⟨s, hs⟩ := isSpor_barInf_of_isJ1 hK hJ1
      obtain ⟨-, -, -, g, hgM, h3⟩ := h17 K hK ⟨s, hs⟩
      have hg' : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
      exfalso
      exact false_of_three_dvd_inf_map_conj hsp hKM hg'
        (by simpa [CFSG.Quasithin.conjSubgroup] using h3)
  · have hSU3 : IsSU3 (Bar2 K) n := uc22p22d_isSU3_of_isU3 hK.2.2 hU3
    exact (false_of_bad_shape (D := D) ctx hk1 h1 hThin hK hKne
      (Or.inr (Or.inr ⟨n, hnEven, hSU3⟩))).elim
  · exact (false_of_bad_shape (D := D) ctx hk1 h1 hThin hK hKne
      (Or.inl hL3)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

