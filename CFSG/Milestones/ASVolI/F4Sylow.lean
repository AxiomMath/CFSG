module

public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.ASVolI.ChF

section Sylow

theorem burnsideF45_pCoreOf_eq_of_isLieParabolics {E : Type} [Group E] [Finite E] {p : ℕ}
    (hp : p.Prime) {H B P₁ P₂ : Subgroup E} (h : IsLieParabolics p H B P₁ P₂) :
    ∃ S : Subgroup E, IsSylowOf p S H ∧ pCoreOf p B = S := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨S, ⟨hSH, hSp, hSidx⟩, hB⟩, -⟩ := h
  refine ⟨S, ⟨hSH, hSp, hSidx⟩, ?_⟩
  have hSB : S ≤ B := by
    rw [hB]; exact le_inf hSH Subgroup.le_normalizer
  have hBH : B ≤ H := by
    rw [hB]; exact inf_le_left
  have hBN : B ≤ Subgroup.normalizer (S : Set E) := by
    rw [hB]; exact inf_le_right
  set T : Subgroup ↥B := S.subgroupOf B with hT
  have hTn : T.Normal := by
    refine ⟨fun t ht b => ?_⟩
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    have hb : (b : E) ∈ Subgroup.normalizer (S : Set E) := hBN b.2
    have := (Subgroup.mem_normalizer_iff.mp hb (t : E)).mp ht
    simpa using this
  have hTp : IsPGroup p T := hSp.comap_subtype
  have hTidx : ¬ p ∣ T.index := by
    intro hdvd
    apply hSidx
    have hmul := Subgroup.relIndex_mul_relIndex S B H hSB hBH
    have : p ∣ S.relIndex B := hdvd
    exact hmul ▸ Dvd.dvd.mul_right this _
  let TS : Sylow p ↥B := hTp.toSylow hTidx
  have hcore : CFSG.pCore p ↥B = T := by
    apply le_antisymm
    · haveI : (CFSG.pCore p ↥B).Normal := CFSG.pCore_normal
      have := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p) (G := ↥B)) TS
      simpa [TS] using this
    · exact le_sSup ⟨hTn, hTp⟩
  show (CFSG.pCore p ↥B).map B.subtype = S
  rw [hcore, hT, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr hSB

theorem burnsideF45_sylow
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) : IsSylowOf p (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
  haveI := hyp.finite
  have hp := burnsideF4a_prime_of_isGenLie hyp.model
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (ChF.nativeChartCompatibility κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  obtain ⟨S, hS, hcore⟩ := burnsideF45_pCoreOf_eq_of_isLieParabolics hp hlp
  rw [hcore]
  exact hS

end Sylow

section QValues

theorem burnsideF45_qOne_eq {E : Type} [Group E] (M₁ M₂ : Subgroup E) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = (M₁ ⊓ M₂).relIndex M₁ - 1 := by
  show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index - 1 = _
  rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range = (M₁ ⊓ M₂).subgroupOf M₁ from
    Subgroup.inclusion_range (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
  rfl

theorem burnsideF45_qTwo_eq {E : Type} [Group E] (M₁ M₂ : Subgroup E) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = (M₁ ⊓ M₂).relIndex M₂ - 1 := by
  show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range.index - 1 = _
  rw [show (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range = (M₁ ⊓ M₂).subgroupOf M₂ from
    Subgroup.inclusion_range (inf_le_right : M₁ ⊓ M₂ ≤ M₂)]
  rfl

theorem burnsideF45_relIndex_chart {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (chart : NativeChart κ p f Gp) (hm : chart.Matches M₁ M₂)
    (hGp : Gp = ⊤) :
    (M₁ ⊓ M₂).relIndex M₁ = chart.borel.relIndex chart.points ∧
      (M₁ ⊓ M₂).relIndex M₂ = chart.borel.relIndex chart.lines := by
  obtain ⟨h1, h2, h3⟩ := hm
  subst hGp
  rw [top_inf_eq] at h1 h2 h3
  rw [← h1, ← h2, ← h3]
  exact ⟨rfl, rfl⟩

theorem burnsideF45_relIndex_map_map {E M : Type} [Group E] [Group M] {core : Subgroup E}
    (marking : M ≃* core) (A B : Subgroup M) :
    ((A.map marking.toMonoidHom).map core.subtype).relIndex
        ((B.map marking.toMonoidHom).map core.subtype) = A.relIndex B := by
  rw [Subgroup.relIndex_map_map_of_injective _ _ core.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ marking.injective]

theorem burnsideF45_relIndex_inf_index_two {G : Type*} [Group G] {R B P : Subgroup G}
    (hR : R.index = 2) (hBP : B ≤ P) (hB : ¬ B ≤ R) :
    (R ⊓ B).relIndex (R ⊓ P) = B.relIndex P := by
  have hP : ¬ P ≤ R := fun h => hB (hBP.trans h)
  have e1 := Subgroup.relIndex_mul_relIndex (R ⊓ B) (R ⊓ P) P (inf_le_inf_left R hBP) inf_le_right
  have e2 := Subgroup.relIndex_mul_relIndex (R ⊓ B) B P inf_le_right hBP
  rw [Subgroup.inf_relIndex_right, burnsideF4h_g2_relIndex_eq_two hR hP] at e1
  rw [Subgroup.inf_relIndex_right, burnsideF4h_g2_relIndex_eq_two hR hB] at e2
  omega

end QValues

section G2d

open CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431.BN


theorem burnsideF45_card_g2_sys_root (K : Type) [Field K] [Finite K] {i : ℤ} (h1 : 1 ≤ i)
    (h6 : i ≤ 6) : Nat.card ((burnsideF4h_g2_sys K).root i) = Nat.card K := by
  show Nat.card ((hexGroup (g2Roots K) i).map (hexProj _)) = _
  rw [card_hexQuotGroup (g2Data K) h1 h6]
  exact card_g2Roots (isRoot_hexPos (by omega) (by omega))

theorem burnsideF45_g2_full_relIndex (K : Type) [Field K] [Finite K] :
    (G2Native.fullLocal K (G2Native.positiveBorel K)).relIndex
        (G2Native.fullLocal K (G2Native.pointParabolic K)) = Nat.card K + 1 ∧
      (G2Native.fullLocal K (G2Native.positiveBorel K)).relIndex
        (G2Native.fullLocal K (G2Native.lineParabolic K)) = Nat.card K + 1 := by
  have h6 : Nat.card ((burnsideF4h_g2_sys K).root ((6 : ℕ) : ℤ)) = Nat.card K :=
    burnsideF45_card_g2_sys_root K (by norm_num) (by norm_num)
  rw [burnsideF4h_g2_fullLocal_borel, burnsideF4h_g2_fullLocal_point,
    burnsideF4h_g2_fullLocal_line, burnsideF4h_ree_relIndex_P₁, burnsideF4h_ree_relIndex_P₂,
    burnsideF45_card_g2_sys_root K le_rfl (by norm_num), h6]
  exact ⟨add_comm _ _, add_comm _ _⟩


theorem burnsideF45_g2_small_relIndex (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    (G2Native.smallLocal K (G2Native.positiveBorel K)).relIndex
        (G2Native.smallLocal K (G2Native.pointParabolic K)) = 3 ∧
      (G2Native.smallLocal K (G2Native.positiveBorel K)).relIndex
        (G2Native.smallLocal K (G2Native.lineParabolic K)) = 3 := by
  have hR := burnsideF4h_g2_incl_index hK
  have hB := burnsideF4h_g2_borel_not_le_range hK
  obtain ⟨hp, hl⟩ := burnsideF45_g2_full_relIndex K
  have key : ∀ L : Subgroup (G2Native.Parent K), G2Native.positiveBorel K ≤ L →
      (G2Native.smallLocal K (G2Native.positiveBorel K)).relIndex (G2Native.smallLocal K L) =
        (G2Native.fullLocal K (G2Native.positiveBorel K)).relIndex (G2Native.fullLocal K L) := by
    intro L hL
    rw [← burnsideF4h_g2_comap_incl hK, ← burnsideF4h_g2_comap_incl hK,
      ← Subgroup.relIndex_map_map_of_injective _ _ (burnsideF4h_g2_incl_injective hK),
      Subgroup.map_comap_eq, Subgroup.map_comap_eq]
    exact burnsideF45_relIndex_inf_index_two hR (Subgroup.map_mono hL) hB
  refine ⟨?_, ?_⟩
  · rw [key (G2Native.pointParabolic K) le_sup_left, hp, hK]
  · rw [key (G2Native.lineParabolic K) le_sup_left, hl, hK]

theorem burnsideF45_q_G2d {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2d p f Gp M₁ M₂) (hGp : Gp = ⊤) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 2 ∧ (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2 := by
  obtain ⟨chart, hm⟩ := hyp.toHypF_4_4g.lie_amalgam
  obtain ⟨e1, e2⟩ := burnsideF45_relIndex_chart chart hm hGp
  rw [burnsideF45_qOne_eq, burnsideF45_qTwo_eq, e1, e2]
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, -, -, K, fK, finK, card, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · letI := fK
    haveI := finK
    obtain ⟨s1, s2⟩ := burnsideF45_g2_small_relIndex K card
    rw [h1, h2, h3]
    unfold G2Native.smallImage
    rw [burnsideF45_relIndex_map_map, burnsideF45_relIndex_map_map, s1, s2]
    exact ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

end G2d

section Tits

open CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF45_q_Tits {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits p f Gp M₁ M₂) (hGp : Gp = ⊤) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 4 ∧ (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2 := by
  obtain ⟨chart, hm⟩ := hyp.toHypF_4_4g.lie_amalgam
  obtain ⟨e1, e2⟩ := burnsideF45_relIndex_chart chart hm hGp
  rw [burnsideF45_qOne_eq, burnsideF45_qTwo_eq, e1, e2]
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨-, -, he, marking, h1, h2, h3, -, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · subst he
    letI := fK
    haveI := finK
    haveI := charK
    obtain ⟨-, i1, i2, -⟩ := burnsideF4h_titsParentAssembly K scope
    have i1' : (derivedImage (reeGroup K 0) (reeBorel K 0)).relIndex
        (derivedImage (reeGroup K 0) (reeParabolic K 0 1)) = 5 := i1
    have i2' : (derivedImage (reeGroup K 0) (reeBorel K 0)).relIndex
        (derivedImage (reeGroup K 0) (reeParabolic K 0 0)) = 3 := i2
    rw [h1, h2, h3, burnsideF45_relIndex_map_map, burnsideF45_relIndex_map_map, i1', i2']
    exact ⟨rfl, rfl⟩


theorem as_F_4_4 : F_4_4 := by
  intro κ p f E _ Gp M₁ M₂ hyp
  refine ⟨burnsideF45_sylow hyp, ?_, ?_⟩
  · rintro ⟨hGp, rfl⟩
    exact burnsideF45_q_G2d hyp hGp
  · rintro ⟨hGp, rfl⟩
    exact burnsideF45_q_Tits hyp hGp

end Tits

end CFSG.ASVolI
