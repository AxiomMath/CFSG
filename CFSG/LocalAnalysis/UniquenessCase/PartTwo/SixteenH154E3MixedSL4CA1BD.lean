module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BC
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_threeElem_mem_of_two_normalizes {A : Type*} [Group A] {B T : Subgroup A}
    (hT : IsPGroup 2 ↥T) (hTB : T ≤ Subgroup.normalizer (B : Set A)) {r : A} (hr : r ^ 3 = 1)
    (hrBT : r ∈ B ⊔ T) : r ∈ B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBH : B ≤ B ⊔ T := le_sup_left
  have hTH : T ≤ B ⊔ T := le_sup_right
  have hHN : B ⊔ T ≤ Subgroup.normalizer (B : Set A) := sup_le Subgroup.le_normalizer hTB
  haveI hnorm : (B.subgroupOf (B ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2 hHN
  let π : ↥(B ⊔ T) →* ↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T) := QuotientGroup.mk' _
  have hsup : B.subgroupOf (B ⊔ T) ⊔ T.subgroupOf (B ⊔ T) = ⊤ :=
    codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup B T)
  have hmap : (T.subgroupOf (B ⊔ T)).map π = ⊤ := by
    have h1 : (B.subgroupOf (B ⊔ T) ⊔ T.subgroupOf (B ⊔ T)).map π = ⊤ := by
      rw [hsup, Subgroup.map_top, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [Subgroup.map_sup] at h1
    have h0 : (B.subgroupOf (B ⊔ T)).map π = ⊥ := QuotientGroup.map_mk'_self _
    rwa [h0, bot_sup_eq] at h1
  have hT' : IsPGroup 2 ↥(T.subgroupOf (B ⊔ T)) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hQ : IsPGroup 2 (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) := by
    refine hT'.of_surjective (π.comp (T.subgroupOf (B ⊔ T)).subtype) ?_
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hr' : (π ⟨r, hrBT⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨r, hrBT⟩ : ↥(B ⊔ T)) ^ 3 = 1 := Subtype.ext (by simpa using hr)
    rw [h3, map_one]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) (π ⟨r, hrBT⟩)
  have hdvd : orderOf (π ⟨r, hrBT⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one hr'
  have h2k : 2 ^ k ∣ 3 := hk ▸ hdvd
  have h1 : 2 ^ k = 1 := by
    have hcop : Nat.Coprime (2 ^ k) 3 := (by norm_num : Nat.Coprime 2 3).pow_left k
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    rwa [Nat.gcd_eq_left h2k] at hg
  have hq1 : π ⟨r, hrBT⟩ = 1 := orderOf_eq_one_iff.mp (hk.trans h1)
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)

theorem s16h_sl4_frame_normalizes_sup {W : Type} [CommGroup W]
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T) :
    X ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (L ⊔ L').map (MulAut.conj x).toMonoidHom = L ⊔ L'
  rw [Subgroup.map_sup]
  rcases F.perm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem s16h_sl4_lBar_conj_eq_of_frame (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {L' : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))}
    (F : s16h_SL4TwoFrame (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
      (lBar ⊥ V h.hyp151.isElemAbelian L) L' (barSub ⊥ V h.hyp151.isElemAbelian D.T))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) = L' := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil ⊥ V := hMs hxM
  have hconj := s15_Infra_barSub_conjSubgroup ⊥ V hV hxs L
  have hinv : (actTil ⊥ V hV ⟨x, hxs⟩)⁻¹ ∈ Mbar D.M ⊥ V hV :=
    Subgroup.inv_mem _ (actTil_mem_barSub ⊥ V hV hxM hxs)
  show barSub ⊥ V hV (conjSubgroup L x) = L'
  rw [hconj]
  rcases F.perm _ hinv with ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso
    apply hxn
    rw [s15_Infra_mem_nBar_iff h.hyp151.hyp125 hV hxM, hconj]
    exact h1
  · exact h1

theorem s16h_sl4_barSub_threeElem_le (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hYL : barSub ⊥ V h.hyp151.isElemAbelian Y ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))
    {r : G} (hrY : r ∈ Y ⊔ D.T) (hr3 : r ^ 3 = 1) :
    barSub ⊥ V h.hyp151.isElemAbelian (Subgroup.zpowers r) ≤
      lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  classical
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨L', -, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  have hconj := s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn
  rw [hconj] at hYL ⊢
  have hrM : r ∈ D.M := (sup_le hYM D.sylowM.le) hrY
  have hrs : r ∈ stabTil ⊥ V := hMs hrM
  have hTbar : IsPGroup 2 (barSub ⊥ V hV D.T) := by
    have h0 : IsPGroup 2 (D.T.subgroupOf (stabTil ⊥ V)) := D.sylowM.isPGroup.comap_subtype
    exact h0.map (actTil ⊥ V hV)
  have hTnorm : barSub ⊥ V hV D.T ≤
      Subgroup.normalizer ((lBar ⊥ V hV L ⊔ L' : Subgroup (MulAut (Vtil ⊥ V hV))) :
        Set (MulAut (Vtil ⊥ V hV))) := fun t ht =>
    s16h_sl4_frame_normalizes_sup F (F.t_le ht)
  have hrbar : actTil ⊥ V hV ⟨r, hrs⟩ ∈ lBar ⊥ V hV L ⊔ L' := by
    refine s16h_threeElem_mem_of_two_normalizes hTbar hTnorm ?_ ?_
    · rw [← map_pow]
      have h3 : (⟨r, hrs⟩ : ↥(stabTil ⊥ V)) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
      rw [h3, map_one]
    · let ψ : ↥D.M →* MulAut (Vtil ⊥ V hV) := (actTil ⊥ V hV).comp (Subgroup.inclusion hMs)
      have hsub : (⟨r, hrM⟩ : ↥D.M) ∈ Y.subgroupOf D.M ⊔ D.T.subgroupOf D.M := by
        rw [← Subgroup.subgroupOf_sup hYM D.sylowM.le]
        exact hrY
      have hmem : ψ ⟨r, hrM⟩ ∈ (Y.subgroupOf D.M).map ψ ⊔ (D.T.subgroupOf D.M).map ψ := by
        rw [← Subgroup.map_sup]
        exact Subgroup.mem_map_of_mem ψ hsub
      have hle1 : (Y.subgroupOf D.M).map ψ ≤ barSub ⊥ V hV Y := by
        rintro _ ⟨z, hz, rfl⟩
        exact actTil_mem_barSub ⊥ V hV hz (hMs z.2)
      have hle2 : (D.T.subgroupOf D.M).map ψ ≤ barSub ⊥ V hV D.T := by
        rintro _ ⟨z, hz, rfl⟩
        exact actTil_mem_barSub ⊥ V hV hz (hMs z.2)
      exact sup_le_sup (hle1.trans hYL) hle2 hmem
  rintro e he
  obtain ⟨g, hg, rfl⟩ := (mem_barSub ⊥ V hV _ e).1 he
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hgn : g = (⟨r, hrs⟩ : ↥(stabTil ⊥ V)) ^ n := Subtype.ext (by simp [← hn])
  rw [hgn, map_zpow]
  exact Subgroup.zpow_mem _ hrbar n

theorem s16h_sl4_barSub_T_isPGroup (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsPGroup 2 (barSub V₀ V hV D.T) := by
  have h0 : IsPGroup 2 (D.T.subgroupOf (stabTil V₀ V)) := D.sylowM.isPGroup.comap_subtype
  exact h0.map (actTil V₀ V hV)

theorem s16h_sl4_barSub_T_normalizes_sup (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    barSub ⊥ V h.hyp151.isElemAbelian D.T ≤
      Subgroup.normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
          Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) := by
  obtain ⟨L', -, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  rw [s16h_sl4_lBar_conj_eq_of_frame D h F hxM hxn]
  exact fun t ht => s16h_sl4_frame_normalizes_sup F (F.t_le ht)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
