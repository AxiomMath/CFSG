module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CentralizerTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62FusionPointwise
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62FusionCenter
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem uniqueFourConj_conj {G : Type} [Group G] (k g : G) (X : Subgroup G) :
    CFSG.Open.uniqueFourConj k (CFSG.Open.uniqueFourConj g X) =
      CFSG.Open.uniqueFourConj (g * k) X := by
  unfold CFSG.Open.uniqueFourConj
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private theorem ne_bot_of_two_le_pRank {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hLrank : 2 ≤ CFSG.Open.pRank 3 L) :
    Q ≠ ⊥ := by
  intro hbot
  have hpQ : CFSG.Open.pRank 3 Q = CFSG.Open.pRank 3 L :=
    CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow Nat.prime_three hQ
  have h0 : CFSG.Open.pRank 3 Q ≤ 0 := by
    rw [hbot]
    refine CFSG.SectionRank.pRank_le (p := 3) (H := ⊥) (k := 0) (by norm_num) ?_
    intro E hE _
    rw [le_bot_iff] at hE
    rw [hE, Subgroup.card_bot]
    norm_num
  omega

private theorem mem_uniqueSet_of_inU {G : Type} [Group G] {M X : Subgroup G}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC6.InU M X) :
    X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  refine ⟨h.1, ?_⟩
  intro k hk
  have hk' : X ≤ CFSG.Open.uniqueFourConj k⁻¹ M := by
    simpa [CFSG.Open.uniqueFourConj] using hk
  have hconj := h.2 k⁻¹ hk'
  simpa [CFSG.Open.uniqueFourConj] using hconj

theorem inU_inf_center_of_centralizer_transport
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hQn : (Q.subgroupOf P).Normal)
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L)) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M (Q ⊓ (Subgroup.center ↥P).map P.subtype) := by
  have hQ1 : Q ≠ ⊥ := ne_bot_of_two_le_pRank hQ hLrank
  obtain ⟨Z, hZQ, hZcent, hZcard⟩ :=
    exists_card_three_le_inf_center_of_normal hP.isPGroup hQP hQn hQ1
  have hZInU : CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M Z :=
    inU_of_card_three_le_Q h63 hLM hQ hP hLrank hΓ h61 hZQ hZcard
  have hZZ' : Z ≤ Q ⊓ (Subgroup.center ↥P).map P.subtype := le_inf hZQ hZcent
  have hZ'M : Q ⊓ (Subgroup.center ↥P).map P.subtype ≤ D.M :=
    inf_le_left.trans (hQP.trans hP.le)
  exact ⟨hZ'M, fun g hg => hZInU.2 g (hZZ'.trans hg)⟩

theorem inf_center_mem_uniqueSet_of_centralizer_transport
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L)) :
    Q ⊓ (Subgroup.center ↥P).map P.subtype ∈
      CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  have hQn : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hQ hQP hP.isPGroup hPL
  exact mem_uniqueSet_of_inU
    (inU_inf_center_of_centralizer_transport h63 hLM hQ hQP hP hLrank hΓ hQn h61)

theorem fusion_control_of_centralizer_transport
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L))
    {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P)
    (hconj : ∃ g : G, Y = X.map (MulAut.conj g⁻¹).toMonoidHom) :
    ∃ m ∈ D.M, Y = X.map (MulAut.conj m⁻¹).toMonoidHom := by
  have hZU := inf_center_mem_uniqueSet_of_centralizer_transport h63 hLM hQ hQP hP hLrank hΓ hPL h61
  obtain ⟨g, hg⟩ := hconj
  exact exists_mem_conj_of_le_of_center D.maxLocal hP.isPGroup
    (inf_le_left.trans hQP) inf_le_right hZU hX hY hg

theorem exists_mem_conj_forall_of_centralizer_transport
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L))
    {X : Subgroup G} (hX : X ≤ P) {g : G}
    (hg : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ P) :
    ∃ m ∈ D.M, ∀ x ∈ X, g⁻¹ * x * g = m⁻¹ * x * m := by
  have hZU := inf_center_mem_uniqueSet_of_centralizer_transport h63 hLM hQ hQP hP hLrank hΓ hPL h61
  exact exists_mem_conj_forall_of_center D.maxLocal hP.isPGroup
    (inf_le_left.trans hQP) inf_le_right hZU hX hg

theorem inU_of_normalizer_le_of_centralizer_transport
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G} {L Q P : Subgroup G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D) (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hLrank : 2 ≤ CFSG.Open.pRank 3 L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (h61 : ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L))
    {X : Subgroup G} (hXP : X ≤ P) (hN : Subgroup.normalizer (X : Set G) ≤ D.M) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M X := by
  have h3prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZU := inf_center_mem_uniqueSet_of_centralizer_transport h63 hLM hQ hQP hP hLrank hΓ hPL h61
  refine CFSG.LocalAnalysis.UniquenessCase.UC6.inU_of_normalizer_le_of_fusion
    (M := D.M) (X := X)
    (CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal)
    (hXP.trans hP.le) hN ?_
  intro g hg
  have hXg3 : IsPGroup 3 (CFSG.Open.uniqueFourConj g X) :=
    (hP.isPGroup.to_le hXP).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨k, hkM, hkP⟩ :=
    CFSG.GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hP hg hXg3
  have hkP' : CFSG.Open.uniqueFourConj k (CFSG.Open.uniqueFourConj g X) ≤ P := by
    intro y hy
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_uniqueFourConj_iff] at hy
    have h := hkP (k * y * k⁻¹) hy
    simpa [mul_assoc] using h
  have hconj' : CFSG.Open.uniqueFourConj k (CFSG.Open.uniqueFourConj g X) =
      CFSG.Open.uniqueFourConj (g * k) X := uniqueFourConj_conj k g X
  have hY : CFSG.Open.uniqueFourConj (g * k) X ≤ P := hconj' ▸ hkP'
  obtain ⟨m, hmM, hm⟩ := fusion_control_of_centralizer_transport
    h63 hLM hQ hQP hP hLrank hΓ hPL h61 hXP hY ⟨g * k, rfl⟩
  have h1 : CFSG.Open.uniqueFourConj k (CFSG.Open.uniqueFourConj g X) =
      CFSG.Open.uniqueFourConj m X := by
    rw [hconj']
    exact hm
  have h2 : CFSG.Open.uniqueFourConj g X =
      CFSG.Open.uniqueFourConj (m * k⁻¹) X := by
    have h4 : CFSG.Open.uniqueFourConj k⁻¹ (CFSG.Open.uniqueFourConj m X) =
        CFSG.Open.uniqueFourConj (m * k⁻¹) X := uniqueFourConj_conj k⁻¹ m X
    rw [← h1] at h4
    rwa [CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_inv_conj] at h4
  exact ⟨m * k⁻¹, D.M.mul_mem hmM (D.M.inv_mem hkM), h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
