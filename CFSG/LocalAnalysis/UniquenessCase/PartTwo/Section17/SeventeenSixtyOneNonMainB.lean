module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneNonMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13b
public import CFSG.GroupTheory.SylowSupCentralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HBasic
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.SupCentralizerCancel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
public import CFSG.RankThree.ThinCatalog.OuterThreeFree
public import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.PartOne (pElementSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_seven_dvd_card_outer_of_isL3 {X : Type} [Group X] (hX : IsL3 X 2) :
    ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
  not_dvd_card_outer_of_isL3 hX (by norm_num) (by norm_num) (by norm_num)

theorem not_seven_dvd_card_outer_of_isL2_three {X : Type} [Group X] (hX : IsL2 X 3) :
    ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hm : CFSG.Open.StatedClassicalModel X .PSL 2 2 3 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 2) (p := 2) (f := 3)
      (by decide)).mp hX
  have hdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣
      3 * Nat.gcd 2 (2 ^ 3 - 1) :=
    CFSG.RankThree.ThinCatalog.outer_card_dvd_of_psl_two hm
  have h3 : 3 * Nat.gcd 2 (2 ^ 3 - 1) = 3 := by norm_num
  rw [h3] at hdvd
  intro h7
  have h : 7 ∣ 3 := h7.trans hdvd
  norm_num at h

theorem not_seven_dvd_card_outer_of_isSz_three
    {X : Type} [Group X] (hX : IsSz X 3) :
    ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hS : CFSG.Blueprint.SuzukiModel X 2 3 :=
    (CFSG.Blueprint.LieModel.twistedB2_iff (n := 0) (p := 2) (f := 3)).mp hX |>.2
  obtain ⟨-, hdvd, -⟩ :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} X 2 3 hS).1
  intro h7
  have h : 7 ∣ 3 := h7.trans hdvd
  norm_num at h


open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan in
private theorem barImage_LK_data (D : Data G)
    {V₀ V L : Subgroup G} {p : ℕ} (ctx : Ctx17_58 D V₀ V L p)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p)) (hKne : K ≠ L)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) :
    (barImage D.M L).Normal ∧ (barImage D.M K).Normal ∧
    Nat.card ↥(barImage D.M L) = 2 ^ 6 * 3 ^ 2 * 5 * 7 ∧
    (barImage D.M L ⊓ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) = ⊥) ∧
    (barImage D.M K ⊓ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) = ⊥) ∧
    barImage D.M L ≤ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) ∧
    ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(barImage D.M L)) ∧
    ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(barImage D.M K)) := by
  classical
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hLbN : (barImage D.M L).Normal := s13_barImage_normal (ctx.hyp54.2 L ctx.memC).1
  have hKbN : (barImage D.M K).Normal := s13_barImage_normal (ctx.hyp54.2 K hKcalM).1
  have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent ctx.memC
  have hKcomp : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hKcalM
  have hneLbKb : barImage D.M L ≠ barImage D.M K := fun h =>
    hKne (barImage_injOn_calC hKcalM ctx.memC h.symm)
  have hL3b : IsL3 (barImage D.M L) 2 := by
    obtain ⟨e⟩ := s13_bar_equiv ctx.memC
    exact CFSG.Blueprint.LieModel.of_mulEquiv e ctx.shapeL
  have hLbsimple : IsSimpleGroup ↥(barImage D.M L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3b
  have hcardLb : Nat.card ↥(barImage D.M L) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
    rw [card_barImage_eq_card_bar ctx.memC]
    exact card_bar_of_isL3 ctx.shapeL
  have hZfbL : barImage D.M L ⊓
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) = ⊥ := by
    have hc : Subgroup.center ↥(barImage D.M L) = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_not_prime_card
        (by rw [hcardLb]; norm_num)
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hcent : (⟨z, hz.1⟩ : ↥(barImage D.M L)) ∈ Subgroup.center ↥(barImage D.M L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hz.2 (y : Bar2 D.M) y.2
    rw [hc] at hcent
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcent)
  have hKbsimple : IsSimpleGroup ↥(barImage D.M K) := by
    obtain ⟨e⟩ := s13_bar_equiv hKcalM
    exact (MulEquiv.isSimpleGroup_congr e).1 (isSimpleGroup_bar_of_isL2_or_isSz hshape)
  have hKshape' : IsL2 ↥(barImage D.M K) 3 ∨ IsSz ↥(barImage D.M K) 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hKcalM
    rcases hshape with h | h
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  have hneKbcard : ¬ (Nat.card ↥(barImage D.M K)).Prime := by
    rcases hshape with h | h
    · have hc : Nat.card ↥(barImage D.M K) = 504 := by
        rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 h]
        norm_num
      rw [hc]; norm_num
    · have hc : Nat.card ↥(barImage D.M K) = 29120 := by
        rw [card_barImage_eq_card_bar hKcalM,
          CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]
        norm_num
      rw [hc]; norm_num
  have hZfbK : barImage D.M K ⊓
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) = ⊥ := by
    have hc : Subgroup.center ↥(barImage D.M K) = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_not_prime_card hneKbcard
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hcent : (⟨z, hz.1⟩ : ↥(barImage D.M K)) ∈ Subgroup.center ↥(barImage D.M K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hz.2 (y : Bar2 D.M) y.2
    rw [hc] at hcent
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcent)
  have hLKcomm : barImage D.M L ≤
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) := by
    rcases CFSG.LocalCores.distinct_components_commute hLcomp hKcomp with h | h
    · exact absurd h hneLbKb
    · rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have houtLb : ¬ 7 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(barImage D.M L)) :=
    not_seven_dvd_card_outer_of_isL3 hL3b
  have houtKb : ¬ 7 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(barImage D.M K)) := by
    rcases hKshape' with h | h
    · exact not_seven_dvd_card_outer_of_isL2_three h
    · exact not_seven_dvd_card_outer_of_isSz_three h
  exact ⟨hLbN, hKbN, hcardLb, hZfbL, hZfbK, hLKcomm, houtLb, houtKb⟩

omit [Finite G] in
theorem pow_eq_one_of_mem_sup_centralizer_pow {L K : Subgroup G} {p k : ℕ} {m e : G}
    (hm : m ∈ L ⊔ K) (heL : e ∈ Subgroup.centralizer (L : Set G))
    (heK : e ∈ Subgroup.centralizer (K : Set G))
    (hcomm : m * e = e * m) (hxp : (m * e) ^ p ^ k = 1)
    (hZ : ∀ z : G, z ∈ L ⊔ K → z ∈ Subgroup.centralizer (L : Set G) →
      z ∈ Subgroup.centralizer (K : Set G) → z = 1) :
    e ^ p ^ k = 1 := by
  have hp1 : m ^ p ^ k * e ^ p ^ k = 1 := by
    rw [← Commute.mul_pow hcomm, hxp]
  have hepowL : e ^ p ^ k ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ heL _
  have hepowK : e ^ p ^ k ∈ Subgroup.centralizer (K : Set G) := Subgroup.pow_mem _ heK _
  have hpow : m ^ p ^ k ∈ L ⊔ K := Subgroup.pow_mem _ hm _
  have hmL : m ^ p ^ k ∈ Subgroup.centralizer (L : Set G) := by
    rw [eq_inv_of_mul_eq_one_left hp1]
    exact Subgroup.inv_mem _ hepowL
  have hmK : m ^ p ^ k ∈ Subgroup.centralizer (K : Set G) := by
    rw [eq_inv_of_mul_eq_one_left hp1]
    exact Subgroup.inv_mem _ hepowK
  have hmp1 : m ^ p ^ k = 1 := hZ _ hpow hmL hmK
  rw [hmp1, one_mul] at hp1
  exact hp1

omit [Finite G] in
theorem exists_primeMem_centralizer_of_pow_eq_one {L K : Subgroup G} {p k : ℕ}
    (hLK : L ≤ Subgroup.centralizer (K : Set G))
    (hZ : (L ⊔ K) ⊓ (Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (K : Set G)) = ⊥)
    {x : G} (hxL : x ∈ L ⊔ Subgroup.centralizer (L : Set G))
    (hxK : x ∈ K ⊔ Subgroup.centralizer (K : Set G)) (hxp : x ^ p ^ k = 1)
    (hx : x ∉ L ⊔ K) :
    ∃ w : G, w ∈ Subgroup.centralizer (L : Set G) ∧ w ∈ Subgroup.centralizer (K : Set G) ∧
      w ≠ 1 ∧ w ^ p ^ k = 1 := by
  obtain ⟨l, hl, c, hc, hlc⟩ :=
    CFSG.RankThree.PartOne.PlaneInner.exists_mul_of_mem_sup_centralizer hxL
  obtain ⟨k', hk', d, hd, hkd⟩ :=
    CFSG.RankThree.PartOne.PlaneInner.exists_mul_of_mem_sup_centralizer hxK
  have heq : l * c = k' * d := hlc.symm.trans hkd
  have he : l⁻¹ * d ∈ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (K : Set G) :=
    CFSG.GroupTheory.mul_mem_centralizer_inf_of_eq hLK hl hk' hc hd heq
  have heL : l⁻¹ * d ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp he).1
  have heK : l⁻¹ * d ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp he).2
  have hkl : k' * l = l * k' := Subgroup.mem_centralizer_iff.mp (hLK hl) k' hk'
  have hme : l * k' * (l⁻¹ * d) = x := by
    calc l * k' * (l⁻¹ * d) = k' * l * (l⁻¹ * d) := by rw [hkl]
      _ = k' * (l * (l⁻¹ * d)) := by rw [mul_assoc]
      _ = k' * d := by rw [mul_inv_cancel_left]
      _ = x := hkd.symm
  have hm : l * k' ∈ L ⊔ K :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hk')
  have hcl : l * (l⁻¹ * d) = (l⁻¹ * d) * l :=
    (Subgroup.mem_centralizer_iff.mp heL l hl)
  have hck : k' * (l⁻¹ * d) = (l⁻¹ * d) * k' :=
    (Subgroup.mem_centralizer_iff.mp heK k' hk')
  have hcomm : l * k' * (l⁻¹ * d) = (l⁻¹ * d) * (l * k') := by
    calc l * k' * (l⁻¹ * d) = l * (k' * (l⁻¹ * d)) := mul_assoc _ _ _
      _ = l * ((l⁻¹ * d) * k') := by rw [hck]
      _ = (l * (l⁻¹ * d)) * k' := (mul_assoc _ _ _).symm
      _ = ((l⁻¹ * d) * l) * k' := by rw [hcl]
      _ = (l⁻¹ * d) * (l * k') := mul_assoc _ _ _
  have hZ' : ∀ z : G, z ∈ L ⊔ K → z ∈ Subgroup.centralizer (L : Set G) →
      z ∈ Subgroup.centralizer (K : Set G) → z = 1 := by
    intro z hz1 hz2 hz3
    have hmem : z ∈ (L ⊔ K) ⊓ (Subgroup.centralizer (L : Set G) ⊓
        Subgroup.centralizer (K : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hz1, Subgroup.mem_inf.mpr ⟨hz2, hz3⟩⟩
    rw [hZ] at hmem
    exact (Subgroup.mem_bot).mp hmem
  have hxp' : (l * k' * (l⁻¹ * d)) ^ p ^ k = 1 := by rw [hme]; exact hxp
  have hep : (l⁻¹ * d) ^ p ^ k = 1 :=
    pow_eq_one_of_mem_sup_centralizer_pow hm heL heK hcomm hxp' hZ'
  have hne : l⁻¹ * d ≠ 1 := by
    intro h1
    apply hx
    rw [← hme, h1, mul_one]
    exact hm
  exact ⟨l⁻¹ * d, heL, heK, hne, hep⟩

omit [Finite G] in
theorem mem_sup_sup_centralizer_inf_of_mem_sup_centralizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) {x : G}
    (hxA : x ∈ A ⊔ Subgroup.centralizer (A : Set G))
    (hxB : x ∈ B ⊔ Subgroup.centralizer (B : Set G)) :
    x ∈ (A ⊔ B) ⊔ (Subgroup.centralizer (A : Set G) ⊓
      Subgroup.centralizer (B : Set G)) := by
  obtain ⟨l, hl, c, hc, hlc⟩ :=
    CFSG.RankThree.PartOne.PlaneInner.exists_mul_of_mem_sup_centralizer hxA
  obtain ⟨k, hk, d, hd, hkd⟩ :=
    CFSG.RankThree.PartOne.PlaneInner.exists_mul_of_mem_sup_centralizer hxB
  have heq : l * c = k * d := hlc.symm.trans hkd
  have hw : l⁻¹ * d ∈ Subgroup.centralizer (A : Set G) ⊓
      Subgroup.centralizer (B : Set G) :=
    CFSG.GroupTheory.mul_mem_centralizer_inf_of_eq hAB hl hk hc hd heq
  have hkl : k * l = l * k := Subgroup.mem_centralizer_iff.mp (hAB hl) k hk
  have hx : l * k * (l⁻¹ * d) = x := by
    calc l * k * (l⁻¹ * d) = k * l * (l⁻¹ * d) := by rw [hkl]
      _ = k * (l * (l⁻¹ * d)) := by rw [mul_assoc]
      _ = k * d := by rw [mul_inv_cancel_left]
      _ = x := hkd.symm
  have hlk : l * k ∈ A ⊔ B :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hk)
  rw [← hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlk) (Subgroup.mem_sup_right hw)

theorem pRank_seven_zpowers_eq_one {w : G} (hw : w ≠ 1) (hwp : ∃ k : ℕ, w ^ 7 ^ k = 1) :
    CFSG.Open.pRank 7 (Subgroup.zpowers w) = 1 := by
  refine le_antisymm
    (CFSG.SectionRank.pRank_le_one_of_isCyclic (by norm_num) (Subgroup.isCyclic_zpowers w)) ?_
  obtain ⟨k, hk⟩ := hwp
  have hdvdZ : Nat.card ↥(Subgroup.zpowers w) ∣ 7 ^ k := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hneZ : Nat.card ↥(Subgroup.zpowers w) ≠ 1 := by
    rw [Nat.card_zpowers]
    intro h
    exact hw (orderOf_eq_one_iff.mp h)
  have h7dvdZ : 7 ∣ Nat.card ↥(Subgroup.zpowers w) := by
    rcases (Nat.dvd_prime_pow Nat.prime_seven (m := k)).mp hdvdZ with ⟨j, -, hjeq⟩
    rw [hjeq]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero] at hjeq
      exact absurd hjeq hneZ
    · exact dvd_pow_self 7 (by omega)
  obtain ⟨g, hgord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers w)) 7 h7dvdZ
  have hg'ord : orderOf (g : G) = 7 := by
    rw [Subgroup.orderOf_coe, hgord]
  have hzgle : Subgroup.zpowers (g : G) ≤ Subgroup.zpowers w :=
    Subgroup.zpowers_le.mpr g.2
  have hzcard : Nat.card ↥(Subgroup.zpowers (g : G)) = 7 := by
    rw [Nat.card_zpowers, hg'ord]
  have hel : CFSG.Open.IsElemAbelian 7 (Subgroup.zpowers (g : G)) :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime hzcard
  have h := CFSG.SectionRank.le_pRank (p := 7) (by norm_num) hzgle hel
    (k := 1) (by rw [hzcard]; norm_num)
  simpa using h

private theorem exists_centralizer_seven_power (D : Data G)
    {V₀ V L : Subgroup G} {p : ℕ} (ctx : Ctx17_58 D V₀ V L p)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p)) (hKne : K ≠ L)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    {x : G} (hxM : x ∈ D.M) (hxord : ∃ k : ℕ, orderOf x = 7 ^ k)
    (hxnot : x ∉ L ⊔ K) :
    ∃ w : Bar2 D.M, w ∈ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ∧
      w ∈ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) ∧
      w ≠ 1 ∧ ∃ k : ℕ, w ^ 7 ^ k = 1 := by
  classical
  obtain ⟨k, hxord⟩ := hxord
  obtain ⟨hLbN, hKbN, -, hZfbL, hZfbK, hLKcomm, houtLb, houtKb⟩ :=
    barImage_LK_data D ctx hK hKne hshape
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let xbar : Bar2 D.M := π ⟨x, hxM⟩
  have hxbar7 : xbar ^ 7 ^ k = 1 := by
    have hx7 : (⟨x, hxM⟩ : ↥D.M) ^ 7 ^ k = 1 := by
      apply Subtype.ext
      show x ^ 7 ^ k = 1
      rw [← hxord]
      exact pow_orderOf_eq_one x
    have := congrArg π hx7
    rw [map_pow, map_one] at this
    simpa [xbar] using this
  have hxbar_not : xbar ∉ barImage D.M L ⊔ barImage D.M K := by
    intro hmem
    have hbar : xbar ∈ barImage D.M (L ⊔ K) := by
      rw [s13_barImage_sup hLM hKM]
      exact hmem
    have hx7' : ∃ j : ℕ, x ^ 7 ^ j = 1 := ⟨k, by rw [← hxord]; exact pow_orderOf_eq_one x⟩
    exact hxnot (mem_sup_of_mem_barImage_sup_of_sevenPow hLM hKM
      (ctx.hyp54.2 L ctx.memC).1 (ctx.hyp54.2 K hKcalM).1 hxM hx7' hbar)
  have hxLnorm : xbar ∈ Subgroup.normalizer (barImage D.M L : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLbN]
    exact Subgroup.mem_top _
  have hxKnorm : xbar ∈ Subgroup.normalizer (barImage D.M K : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKbN]
    exact Subgroup.mem_top _
  have hxbarL : xbar ∈ barImage D.M L ⊔
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) :=
    CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer (p := 7) (k := k)
      Nat.prime_seven houtLb hxLnorm hxbar7
  have hxbarK : xbar ∈ barImage D.M K ⊔
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) :=
    CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer (p := 7) (k := k)
      Nat.prime_seven houtKb hxKnorm hxbar7
  have hZprod : (barImage D.M L ⊔ barImage D.M K) ⊓
      (Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M))) = ⊥ :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_bot hLKcomm hZfbL hZfbK
  obtain ⟨w, hwL, hwK, hwne, hw7⟩ :=
    exists_primeMem_centralizer_of_pow_eq_one hLKcomm hZprod hxbarL hxbarK hxbar7 hxbar_not
  exact ⟨w, hwL, hwK, hwne, ⟨k, hw7⟩⟩

theorem three_le_pRank_seven_of_not_mem_sup
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hKne : K ≠ L) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K) :
    3 ≤ CFSG.Open.pRank 7 D.M := by
  classical
  obtain ⟨x, hxM, ⟨k, hxord⟩, hxnot⟩ :=
    exists_sevenPower_not_mem_sup D ctx hK hshape hnotmain

  obtain ⟨w, hwL, hwK, hwne, k, hw7⟩ :=
    exists_centralizer_seven_power D ctx hK hKne hshape hxM ⟨k, hxord⟩ hxnot
  obtain ⟨-, -, hcardLb, hZfbL, hZfbK, hLKcomm, -, -⟩ :=
    barImage_LK_data D ctx hK hKne hshape
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hZprod : (barImage D.M L ⊔ barImage D.M K) ⊓
      (Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M))) = ⊥ :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_bot hLKcomm hZfbL hZfbK

  have h7Lb : 7 ∣ Nat.card ↥(barImage D.M L) := by
    rw [hcardLb]; norm_num
  have h7Kb : 7 ∣ Nat.card ↥(barImage D.M K) := by
    rw [card_barImage_eq_card_bar hKcalM]
    exact seven_dvd_card_bar_of_isL2_or_isSz hshape
  obtain ⟨gL, hgLord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barImage D.M L)) 7 h7Lb
  obtain ⟨gK, hgKord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barImage D.M K)) 7 h7Kb
  let Zb : Subgroup (Bar2 D.M) := Subgroup.zpowers (gL : Bar2 D.M)
  let Xb : Subgroup (Bar2 D.M) := Subgroup.zpowers (gK : Bar2 D.M)
  let Wb : Subgroup (Bar2 D.M) := Subgroup.zpowers w
  have hZb_le : Zb ≤ barImage D.M L := Subgroup.zpowers_le.mpr gL.2
  have hXb_le : Xb ≤ barImage D.M K := Subgroup.zpowers_le.mpr gK.2
  have hZbcard : Nat.card Zb = 7 := by
    rw [show Zb = Subgroup.zpowers (gL : Bar2 D.M) from rfl, Nat.card_zpowers,
      Subgroup.orderOf_coe, hgLord]
  have hXbcard : Nat.card Xb = 7 := by
    rw [show Xb = Subgroup.zpowers (gK : Bar2 D.M) from rfl, Nat.card_zpowers,
      Subgroup.orderOf_coe, hgKord]
  have hXZcomm : ∀ a ∈ Xb, ∀ b ∈ Zb, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hLKcomm (hZb_le hb)) a (hXb_le ha)
  have hXZdisj : Xb ⊓ Zb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzK : z ∈ barImage D.M K := hXb_le hz.1
    have hzC : z ∈ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) :=
      hLKcomm (hZb_le hz.2)
    have hmem := Subgroup.mem_inf.mpr ⟨hzK, hzC⟩
    rw [hZfbK] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hZprod_sup : (barImage D.M L ⊔ barImage D.M K) ⊓
      Subgroup.centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
        Set (Bar2 D.M)) = ⊥ := by
    rw [CFSG.centralizer_sup_eq]
    exact hZprod
  have hXZ_W_disj : (Xb ⊔ Zb) ⊓ Wb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzLK : z ∈ barImage D.M L ⊔ barImage D.M K := by
      have hle : Xb ⊔ Zb ≤ barImage D.M L ⊔ barImage D.M K :=
        sup_le (hXb_le.trans le_sup_right) (hZb_le.trans le_sup_left)
      exact hle hz.1
    have hzC : z ∈ Subgroup.centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
      rw [CFSG.centralizer_sup_eq]
      exact ⟨Subgroup.zpowers_le.mpr hwL hz.2, Subgroup.zpowers_le.mpr hwK hz.2⟩
    have hmem := Subgroup.mem_inf.mpr ⟨hzLK, hzC⟩
    rw [hZprod_sup] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hXZ_le_CW : Xb ⊔ Zb ≤ Subgroup.centralizer (Wb : Set (Bar2 D.M)) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.zpowers_le.mpr hwK hb) a (hXb_le ha)).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.zpowers_le.mpr hwL hb) a (hZb_le ha)).symm
  have hXZ_W_comm : ∀ a ∈ Xb ⊔ Zb, ∀ b ∈ Wb, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hXZ_le_CW ha) b hb).symm
  have hrankXZ : 2 ≤ CFSG.Open.pRank 7 (Xb ⊔ Zb) := by
    have h := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_seven hXZcomm hXZdisj
    rw [s13_pRank_of_card_prime _ Nat.prime_seven hXbcard,
      s13_pRank_of_card_prime _ Nat.prime_seven hZbcard] at h
    omega
  have hrankW : CFSG.Open.pRank 7 Wb = 1 :=
    pRank_seven_zpowers_eq_one hwne ⟨k, hw7⟩
  have hrank3 : 3 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 D.M)) := by
    have h := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_seven hXZ_W_comm hXZ_W_disj
    rw [hrankW] at h
    have h2 : 3 ≤ CFSG.Open.pRank 7 ((Xb ⊔ Zb) ⊔ Wb) := by omega
    exact h2.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcop : ¬ 7 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    obtain ⟨m, hm⟩ :=
      IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hm]
    intro hd
    have h2 : 7 ∣ 2 := Nat.prime_seven.dvd_of_dvd_pow hd
    norm_num at h2
  have hquot : CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 D.M)) =
      CFSG.Open.pRank 7 (⊤ : Subgroup ↥D.M) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 7) (G := ↥D.M)
      (CFSG.pCore 2 ↥D.M) hcop
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M, ← hquot]
  exact hrank3


theorem pRank_seven_eq_three_of_not_mem_sup
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hKne : K ≠ L) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (h7not : 7 ∉ D.sig) :
    CFSG.Open.pRank 7 D.M = 3 := by
  have h3 : 3 ≤ CFSG.Open.pRank 7 D.M :=
    three_le_pRank_seven_of_not_mem_sup D ctx hK hKne hshape hnotmain
  have hle : CFSG.Open.pRank 7 D.M ≤ 3 := by
    by_contra hle
    have h4 : 4 ≤ CFSG.Open.pRank 7 D.M := by omega
    exact h7not (hSg.four_mem 7 Nat.prime_seven (by norm_num) h4)
  omega

theorem three_lt_pRank_p_and_ne_seven
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hKne : K ≠ L) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D) (h7not : 7 ∉ D.sig) :
    3 < CFSG.Open.pRank p D.M ∧ p ≠ 7 ∧ CFSG.Open.pRank 7 D.M = 3 := by
  have h7eq : CFSG.Open.pRank 7 D.M = 3 :=
    pRank_seven_eq_three_of_not_mem_sup D ctx hK hKne hshape hnotmain hSg h7not
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have h3le : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpmem
  have h3lt : 3 < CFSG.Open.pRank p D.M := by
    rcases lt_or_eq_of_le h3le with h | h
    · exact h
    · exfalso
      have h7mem : 7 ∈ D.sig :=
        h13 ⟨p, hpmem, h.symm⟩ 7 Nat.prime_seven (by norm_num) (by omega)
      exact h7not h7mem
  have hp7 : p ≠ 7 := by
    intro hp
    rw [hp, h7eq] at h3lt
    omega
  exact ⟨h3lt, hp7, h7eq⟩

theorem pRank_M_eq_pRank_Lp_add_pRank_Sp (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hns : s13_NormalSimple (Bar2 D.M))
    (h56 : R17_56At D V₀ V) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p D.M =
      CFSG.Open.pRank p (Lp D p) + CFSG.Open.pRank p (Sp D p) := by
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hOpp : Opp p D.M = Lp D p ⊔ Sp D p := by
    rcases h56 p ctx.hyp54 with h | h
    · exact h
    · exact absurd h.1 hp3
  have hLpF : Lp D p = F13.Lp D.M p := rfl
  have hSpF : Sp D p = F13.Sp D.M p := sp_eq_f13Sp D p
  have hle : Lp D p ⊔ Sp D p ≤ D.M := by
    rw [hLpF, hSpF]
    exact sup_le (s13_Lp_le D.M p) (s13_Sp_le D.M p)
  rw [← s13_pRank_pElementSubgroup hpp D.M]
  change CFSG.Open.pRank p (Opp p D.M) = _
  rw [hOpp]
  rw [← s13_pRank_barImage hpp hp2 hle]
  rw [hLpF, hSpF]
  rw [s13_barImage_sup (s13_Lp_le D.M p) (s13_Sp_le D.M p)]
  set A : Subgroup (Bar2 D.M) := barImage D.M (F13.Lp D.M p) with hA
  set B : Subgroup (Bar2 D.M) := barImage D.M (F13.Sp D.M p) with hB
  have hAeq : A = pElementSubgroup p (CFSG.layer (Bar2 D.M)) := by
    rw [hA]
    exact s13_barImage_Lp D.M hpp
  have hBeq : B = pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) := by
    rw [hB]
    exact s13_barImage_Sp D.M hpp
  have hBcent : B ≤ Subgroup.centralizer (A : Set (Bar2 D.M)) := by
    rw [hAeq, hBeq]
    exact s13_Thirteen2_pElementSubgroup_le p _
  have hdisj : A ⊓ B = ⊥ := by
    rw [hAeq] at hBcent ⊢
    exact le_bot_iff.mp ((inf_le_inf_left _ hBcent).trans
      (le_of_eq (s13_inf_centralizer_eq_bot hns hpp)))
  change CFSG.Open.pRank p (A ⊔ B) = CFSG.Open.pRank p (F13.Lp D.M p) +
    CFSG.Open.pRank p (F13.Sp D.M p)
  rw [s13_pRank_sup_eq_add hpp hBcent hdisj]
  rw [← s13_pRank_barImage hpp hp2 (s13_Lp_le D.M p),
    ← s13_pRank_barImage hpp hp2 (s13_Sp_le D.M p)]

theorem pRank_Lp_le_one_of_p13
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L →
      p ∣ Nat.card (barImage D.M K') → K' = K)
    (hp13 : p = 13) :
    CFSG.Open.pRank p (Lp D p) ≤ 1 := by
  classical
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have : Fact p.Prime := ⟨hpp⟩
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hLpF : Lp D p = F13.Lp D.M p := rfl
  have hbase : CFSG.Open.pRank p (Lp D p) =
      ∑ J ∈ s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J := by
    rw [hLpF, ← s13_pRank_barImage hpp hp2 (s13_Lp_le D.M p)]
    rw [s13_barImage_Lp D.M hpp]
    exact s13_pRank_pElementSubgroup_layer hns hpp hpp
  have hKle : CFSG.Open.pRank p (barImage D.M K) ≤ 1 := by
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hpp (k := 1) ?_
    subst hp13
    rw [card_barImage_eq_card_bar hKcalM]
    rcases hshape with h | h
    · rw [card_of_isL2 h]; norm_num
    · rw [CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num
  have hJ0 : barImage D.M K ∈ s13_compsP (Bar2 D.M) p :=
    s13_mem_compsP.mpr ⟨s13_barImage_isComponent hKcalM, hdvd⟩
  have hsingle : ∑ J ∈ s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J =
      CFSG.Open.pRank p (barImage D.M K) := by
    refine Finset.sum_eq_single_of_mem (barImage D.M K) hJ0 ?_
    intro J hJ hJne
    obtain ⟨hJcomp, hJdvd⟩ := s13_mem_compsP.mp hJ
    obtain ⟨K', hK', hK'bar⟩ := s13_exists_calC_of_component D.M hJcomp
    have hK'Lp : K' ∈ calC (Lp D p) :=
      mem_calC_Lp_of_dvd_card_barImage D ctx.hyp54 hns hK' (hK'bar ▸ hJdvd)
    have hK'neL : K' ≠ L := by
      intro h
      have hpdvdL : p ∣ Nat.card (barImage D.M L) := by
        rw [← h, hK'bar]
        exact hJdvd
      have hnot : ¬ p ∣ Nat.card (barImage D.M L) := by
        subst hp13
        rw [card_barImage_eq_card_bar ctx.memC, card_bar_of_isL3 ctx.shapeL]
        norm_num
      exact hnot hpdvdL
    have hK'eq : K' = K := hunique K' hK'Lp hK'neL (hK'bar ▸ hJdvd)
    exact False.elim (hJne (by rw [← hK'bar, hK'eq]))
  rw [hbase, hsingle]
  exact hKle

theorem p_eq_three_of_not_mem_sup
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L → p ∣ Nat.card (barImage D.M K') → K' = K)
    (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V)
    (hThin : ThinList13) (hp7 : p ≠ 7)
    (h3lt : 3 < CFSG.Open.pRank p D.M) :
    p = 3 := by
  classical
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have hp_cases : p = 3 ∨ p = 5 ∨ p = 13 := by
    rcases hshape with hL2 | hSz
    · exact Or.inl (p_eq_three_of_isL2_three hKcalM hpp hp2 hp7 hL2 hdvd)
    · rcases p_eq_five_or_thirteen_of_isSz_three hKcalM hpp hp2 hp7 hSz hdvd with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  by_contra hpne3
  have hp513 : p = 5 ∨ p = 13 := by
    rcases hp_cases with h | h | h
    · exact absurd h hpne3
    · exact Or.inl h
    · exact Or.inr h
  have hKrank : CFSG.Open.pRank p (barImage D.M K) ≤ 1 := by
    refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hpp (k := 1) ?_
    rcases hp513 with rfl | rfl
    · rcases hshape with hL2 | hSz
      · rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 hL2]; norm_num
      · rw [card_barImage_eq_card_bar hKcalM,
          CFSG.GH74.card_of_lieModel_twistedB2 hSz, CFSG.Open.ordSuzuki]; norm_num
    · rcases hshape with hL2 | hSz
      · rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 hL2]; norm_num
      · rw [card_barImage_eq_card_bar hKcalM,
          CFSG.GH74.card_of_lieModel_twistedB2 hSz, CFSG.Open.ordSuzuki]; norm_num
  have hMrank : CFSG.Open.pRank p D.M =
      CFSG.Open.pRank p (F13.Lp D.M p) + CFSG.Open.pRank p (F13.Sp D.M p) := by
    have h := pRank_M_eq_pRank_Lp_add_pRank_Sp D ctx hns h56 hpne3
    rwa [show Lp D p = F13.Lp D.M p from rfl, sp_eq_f13Sp D p] at h
  have hSp1 : CFSG.Open.pRank p (F13.Sp D.M p) ≤ 1 := by
    rw [← sp_eq_f13Sp D p]
    exact h57 p ctx.hyp54
  have hbase : CFSG.Open.pRank p (F13.Lp D.M p) =
      ∑ J ∈ s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J := by
    rw [← s13_pRank_barImage hpp hp2 (s13_Lp_le D.M p)]
    rw [s13_barImage_Lp D.M hpp]
    exact s13_pRank_pElementSubgroup_layer hns hpp hpp
  have hmem_or : ∀ J ∈ s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J ≤ 1 := by
    intro J hJ
    obtain ⟨hJcomp, hJdvd⟩ := s13_mem_compsP.mp hJ
    obtain ⟨K', hK', hK'bar⟩ := s13_exists_calC_of_component D.M hJcomp
    have hK'Lp : K' ∈ calC (Lp D p) :=
      mem_calC_Lp_of_dvd_card_barImage D ctx.hyp54 hns hK' (hK'bar ▸ hJdvd)
    by_cases hK'L : K' = L
    · rw [hK'L] at hK'bar
      rw [← hK'bar]
      rcases hp513 with h5 | h13
      · rw [h5]
        refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (by norm_num) (k := 1) ?_
        rw [card_barImage_eq_card_bar ctx.memC, card_bar_of_isL3 ctx.shapeL]; norm_num
      · rw [h13]
        refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (by norm_num) (k := 1) ?_
        rw [card_barImage_eq_card_bar ctx.memC, card_bar_of_isL3 ctx.shapeL]; norm_num
    · have hK'eq : K' = K := hunique K' hK'Lp hK'L (hK'bar ▸ hJdvd)
      rw [← hK'bar, hK'eq]
      exact hKrank
  have hsub : s13_compsP (Bar2 D.M) p ⊆
      ({barImage D.M L, barImage D.M K} : Finset (Subgroup (Bar2 D.M))) := by
    intro J hJ
    obtain ⟨hJcomp, hJdvd⟩ := s13_mem_compsP.mp hJ
    obtain ⟨K', hK', hK'bar⟩ := s13_exists_calC_of_component D.M hJcomp
    have hK'Lp : K' ∈ calC (Lp D p) :=
      mem_calC_Lp_of_dvd_card_barImage D ctx.hyp54 hns hK' (hK'bar ▸ hJdvd)
    by_cases hK'L : K' = L
    · rw [hK'L] at hK'bar
      rw [← hK'bar]
      exact Finset.mem_insert_self _ _
    · have hK'eq : K' = K := hunique K' hK'Lp hK'L (hK'bar ▸ hJdvd)
      rw [← hK'bar, hK'eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases hp513 with h5 | h13
  · subst h5
    have hAle : CFSG.Open.pRank 5 (F13.Lp D.M 5) ≤ 2 := by
      rw [hbase]
      calc ∑ J ∈ s13_compsP (Bar2 D.M) 5, CFSG.Open.pRank 5 J
          ≤ ∑ J ∈ s13_compsP (Bar2 D.M) 5, 1 := Finset.sum_le_sum hmem_or
        _ = (s13_compsP (Bar2 D.M) 5).card :=
            (Finset.card_eq_sum_ones (s13_compsP (Bar2 D.M) 5)).symm
        _ ≤ (2 : ℕ) := (Finset.card_le_card hsub).trans (by
            calc ({barImage D.M L, barImage D.M K} : Finset (Subgroup (Bar2 D.M))).card
                ≤ ({barImage D.M K} : Finset (Subgroup (Bar2 D.M))).card + 1 :=
                  Finset.card_insert_le _ _
              _ = 2 := by simp)
    omega
  · subst h13
    have hAle : CFSG.Open.pRank 13 (F13.Lp D.M 13) ≤ 1 := by
      have h := pRank_Lp_le_one_of_p13 D ctx hThin hK hdvd hshape hunique (by norm_num)
      rwa [show Lp D 13 = F13.Lp D.M 13 from rfl] at h
    omega


theorem isL2_three_of_p_eq_three
    (D : Data G) {p : ℕ} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hp3 : p = 3)
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) :
    IsL2 (Bar2 K) 3 := by
  subst hp3
  rcases hshape with h | h
  · exact h
  · exfalso
    have hcard : Nat.card (barImage D.M K) = 29120 := by
      rw [card_barImage_eq_card_bar hK, CFSG.GH74.card_of_lieModel_twistedB2 h,
        CFSG.Open.ordSuzuki]
      norm_num
    rw [hcard] at hdvd
    norm_num at hdvd

theorem isMulCommutative_of_isSylowOf_seven_nonMain
    (D : Data G) {V₀ V L : Subgroup G}
    {p : ℕ} (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hKne : K ≠ L) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K)
    (h55 : R17_55At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 7 P D.M → IsMulCommutative P := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  obtain ⟨hAbN, hBbN, hcardLb, hZfbL, hZfbK, hLKcomm, houtLb, houtKb⟩ :=
    barImage_LK_data D ctx hK hKne hshape
  have h7Lb : 7 ∣ Nat.card ↥(barImage D.M L) := by rw [hcardLb]; norm_num
  have h7sqLb : ¬ 7 ^ 2 ∣ Nat.card ↥(barImage D.M L) := by rw [hcardLb]; norm_num
  have h7Kb : 7 ∣ Nat.card ↥(barImage D.M K) := by
    rcases hshape with h | h
    · rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 h]; norm_num
    · rw [card_barImage_eq_card_bar hKcalM,
        CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num
  have h7sqKb : ¬ 7 ^ 2 ∣ Nat.card ↥(barImage D.M K) := by
    rcases hshape with h | h
    · rw [card_barImage_eq_card_bar hKcalM, card_of_isL2 h]; norm_num
    · rw [card_barImage_eq_card_bar hKcalM,
        CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num
  have h7not : 7 ∉ D.sig :=
    seven_notMem_sig D ctx h55 hSg hK hshape
  have h7eq : CFSG.Open.pRank 7 D.M = 3 :=
    pRank_seven_eq_three_of_not_mem_sup D ctx hK hKne hshape hnotmain hSg h7not
  have hLbrk : CFSG.Open.pRank 7 (barImage D.M L) = 1 := by
    have hle : CFSG.Open.pRank 7 (barImage D.M L) ≤ 1 :=
      CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ Nat.prime_seven (k := 1) (by
        simpa using h7sqLb)
    have h1 : 1 ≤ CFSG.Open.pRank 7 (barImage D.M L) := by
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(barImage D.M L)) 7 h7Lb
      have hz : CFSG.Open.pRank 7 (Subgroup.zpowers (g : Bar2 D.M)) = 1 :=
        s13_pRank_of_card_prime _ Nat.prime_seven (by
          rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg])
      exact hz ▸ CFSG.SectionRank.pRank_mono (by norm_num)
        (Subgroup.zpowers_le.mpr g.2)
    omega
  have hKbrk : CFSG.Open.pRank 7 (barImage D.M K) = 1 := by
    have hle : CFSG.Open.pRank 7 (barImage D.M K) ≤ 1 :=
      CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ Nat.prime_seven (k := 1) (by
        simpa using h7sqKb)
    have h1 : 1 ≤ CFSG.Open.pRank 7 (barImage D.M K) := by
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(barImage D.M K)) 7 h7Kb
      have hz : CFSG.Open.pRank 7 (Subgroup.zpowers (g : Bar2 D.M)) = 1 :=
        s13_pRank_of_card_prime _ Nat.prime_seven (by
          rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg])
      exact hz ▸ CFSG.SectionRank.pRank_mono (by norm_num)
        (Subgroup.zpowers_le.mpr g.2)
    omega
  intro P hP
  obtain ⟨Q, rfl⟩ := hP
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let S : Subgroup (Bar2 D.M) := (Q : Subgroup ↥D.M).map π
  have hSbareq : (Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M)) Q :
      Subgroup (Bar2 D.M)) = S := by
    rw [Sylow.coe_mapSurjective]
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 7 S (⊤ : Subgroup (Bar2 D.M)) := by
    refine ⟨(Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M)) Q).subtype
      le_top, ?_⟩
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]
    exact hSbareq
  let A : Subgroup (Bar2 D.M) := barImage D.M L
  let B : Subgroup (Bar2 D.M) := barImage D.M K
  let X : Subgroup (Bar2 D.M) := A ⊔ B
  let C : Subgroup (Bar2 D.M) := Subgroup.centralizer (X : Set (Bar2 D.M))
  have hAnorm : A.Normal := hAbN
  have hBnorm : B.Normal := hBbN
  have hXnorm : X.Normal := Subgroup.sup_normal A B
  have hCnorm : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer
  have hBCnorm : (B ⊔ C).Normal := Subgroup.sup_normal B C
  have hCeq : C = Subgroup.centralizer (A : Set (Bar2 D.M)) ⊓
      Subgroup.centralizer (B : Set (Bar2 D.M)) := by
    dsimp [C, X]
    rw [CFSG.centralizer_sup_eq]
  have hC_le_CA : C ≤ Subgroup.centralizer (A : Set (Bar2 D.M)) := by
    rw [hCeq]; exact inf_le_left
  have hC_le_CB : C ≤ Subgroup.centralizer (B : Set (Bar2 D.M)) := by
    rw [hCeq]; exact inf_le_right
  have hKLcomm : B ≤ Subgroup.centralizer (A : Set (Bar2 D.M)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hLKcomm ha) b hb).symm
  have hABdisj : A ⊓ B = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (A : Set (Bar2 D.M)) := hKLcomm hz.2
    have hmem : z ∈ A ⊓ Subgroup.centralizer (A : Set (Bar2 D.M)) := ⟨hz.1, hzC⟩
    rw [hZfbL] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hXdisjC : X ⊓ C = ⊥ := by
    rw [hCeq]
    dsimp [X]
    exact CFSG.GroupTheory.inf_centralizer_sup_eq_bot hLKcomm hZfbL hZfbK
  have hXbrk : CFSG.Open.pRank 7 X = 2 := by
    dsimp [X]
    rw [s13_pRank_sup_eq_add Nat.prime_seven hKLcomm hABdisj, hLbrk, hKbrk]
  have hcommXC : ∀ x ∈ X, ∀ c ∈ C, x * c = c * x := by
    intro x hx c hc
    exact Subgroup.mem_centralizer_iff.mp hc x hx
  have hadd := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
    Nat.prime_seven hcommXC hXdisjC
  have hcop : ¬ 7 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    obtain ⟨m, hm⟩ :=
      IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hm]
    intro hd
    have h2 : 7 ∣ 2 := Nat.prime_seven.dvd_of_dvd_pow hd
    norm_num at h2
  have hquot : CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 D.M)) =
      CFSG.Open.pRank 7 (⊤ : Subgroup ↥D.M) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 7) (G := ↥D.M)
      (CFSG.pCore 2 ↥D.M) hcop
  have htop3 : CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 D.M)) = 3 := by
    rw [hquot, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M, h7eq]
  have hHrank : CFSG.Open.pRank 7 (X ⊔ C) ≤ 3 := by
    calc CFSG.Open.pRank 7 (X ⊔ C)
        ≤ CFSG.Open.pRank 7 (⊤ : Subgroup (Bar2 D.M)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = 3 := htop3
  have hCrank : CFSG.Open.pRank 7 C ≤ 1 := by
    rw [hXbrk] at hadd
    omega
  have hS_le_H : S ≤ A ⊔ (B ⊔ C) := by
    intro x hxS
    obtain ⟨k, hk⟩ := hS_sylow.isPGroup ⟨x, hxS⟩
    have hxpow : x ^ 7 ^ k = 1 := congrArg Subtype.val hk
    have hxNA : x ∈ Subgroup.normalizer (A : Set (Bar2 D.M)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hAnorm]
      exact Subgroup.mem_top _
    have hxNB : x ∈ Subgroup.normalizer (B : Set (Bar2 D.M)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hBnorm]
      exact Subgroup.mem_top _
    have hxAC : x ∈ A ⊔ Subgroup.centralizer (A : Set (Bar2 D.M)) :=
      CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer (p := 7) (k := k)
        Nat.prime_seven houtLb hxNA hxpow
    have hxBC : x ∈ B ⊔ Subgroup.centralizer (B : Set (Bar2 D.M)) :=
      CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer (p := 7) (k := k)
        Nat.prime_seven houtKb hxNB hxpow
    have hmem := mem_sup_sup_centralizer_inf_of_mem_sup_centralizer hLKcomm hxAC hxBC
    rw [← hCeq] at hmem
    simpa [sup_assoc] using hmem
  have hS_A : S ≤ Subgroup.normalizer (A : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hAnorm]
    exact le_top
  have hS_BC : S ≤ Subgroup.normalizer ((B ⊔ C : Subgroup (Bar2 D.M)) :
      Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBCnorm]
    exact le_top
  have hA_BC : A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup (Bar2 D.M)) :
      Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBCnorm]
    exact le_top
  have hBC_le_CA : (B ⊔ C) ≤ Subgroup.centralizer (A : Set (Bar2 D.M)) :=
    sup_le hKLcomm hC_le_CA
  have hABCbot : A ⊓ (B ⊔ C) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzCA : z ∈ Subgroup.centralizer (A : Set (Bar2 D.M)) := hBC_le_CA hz.2
    have hmem : z ∈ A ⊓ Subgroup.centralizer (A : Set (Bar2 D.M)) := ⟨hz.1, hzCA⟩
    rw [hZfbL] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcop1 : Nat.Coprime 7 (Nat.card ↥(A ⊓ (B ⊔ C) : Subgroup (Bar2 D.M))) := by
    rw [hABCbot, Subgroup.card_bot]; simp
  have hSyl1 : CFSG.ABGLocalTools.IsSylowOf 7 (S ⊓ A) A :=
    hS_sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hAnorm])
  have hjoin1 : (S ⊓ A) ⊔ (S ⊓ (B ⊔ C)) = S :=
    CFSG.GroupTheory.sup_inf_eq_of_isSylowOf_inf (p := 7) (S := S) (Y := A)
      (C := B ⊔ C) hS_sylow.isPGroup hS_le_H hS_A hS_BC hA_BC hcop1 hSyl1
  have hSp' : IsPGroup 7 ↥(S ⊓ (B ⊔ C) : Subgroup (Bar2 D.M)) :=
    IsPGroup.to_inf_left (p := 7) (H := S) (K := B ⊔ C) hS_sylow.isPGroup
  have hS'_sylow : CFSG.ABGLocalTools.IsSylowOf 7 (S ⊓ (B ⊔ C)) (B ⊔ C) :=
    hS_sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hBCnorm])
  have hBCbot : B ⊓ C = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzCB : z ∈ Subgroup.centralizer (B : Set (Bar2 D.M)) := hC_le_CB hz.2
    have hmem : z ∈ B ⊓ Subgroup.centralizer (B : Set (Bar2 D.M)) := ⟨hz.1, hzCB⟩
    rw [hZfbK] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcop2 : Nat.Coprime 7 (Nat.card ↥(B ⊓ C : Subgroup (Bar2 D.M))) := by
    rw [hBCbot, Subgroup.card_bot]; simp
  have hS'_B : (S ⊓ (B ⊔ C)) ≤ Subgroup.normalizer (B : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBnorm]
    exact le_top
  have hS'_C : (S ⊓ (B ⊔ C)) ≤ Subgroup.normalizer (C : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCnorm]
    exact le_top
  have hB_C : B ≤ Subgroup.normalizer (C : Set (Bar2 D.M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCnorm]
    exact le_top
  have hSyl2 : CFSG.ABGLocalTools.IsSylowOf 7 ((S ⊓ (B ⊔ C)) ⊓ B) B :=
    hS'_sylow.inf_of_le_normalizer le_sup_left (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hBnorm]
      exact le_top)
  have hjoin2 : ((S ⊓ (B ⊔ C)) ⊓ B) ⊔ ((S ⊓ (B ⊔ C)) ⊓ C) = S ⊓ (B ⊔ C) :=
    CFSG.GroupTheory.sup_inf_eq_of_isSylowOf_inf (p := 7) (S := S ⊓ (B ⊔ C))
      (Y := B) (C := C) hSp' inf_le_right hS'_B hS'_C hB_C hcop2 hSyl2
  let W : Subgroup (Bar2 D.M) := ((S ⊓ (B ⊔ C)) ⊓ B) ⊔ ((S ⊓ (B ⊔ C)) ⊓ C)
  have hSdecomp : S = (S ⊓ A) ⊔ W := by
    calc S = (S ⊓ A) ⊔ (S ⊓ (B ⊔ C)) := hjoin1.symm
      _ = (S ⊓ A) ⊔ W := by
          dsimp [W]
          rw [hjoin2]
  have h7A : 7 ∣ Nat.card A := h7Lb
  have h7sqA : ¬ 7 ^ 2 ∣ Nat.card A := h7sqLb
  have h7B : 7 ∣ Nat.card B := h7Kb
  have h7sqB : ¬ 7 ^ 2 ∣ Nat.card B := h7sqKb
  have hQLcard : Nat.card ↥(S ⊓ A) = 7 := by
    rw [hSyl1.card_eq,
      CFSG.GroupTheory.factorization_eq_one_of_dvd_of_not_sq_dvd Nat.prime_seven
        (Nat.card_pos.ne') h7A h7sqA, pow_one]
  have hQKcard : Nat.card ↥((S ⊓ (B ⊔ C)) ⊓ B) = 7 := by
    rw [hSyl2.card_eq,
      CFSG.GroupTheory.factorization_eq_one_of_dvd_of_not_sq_dvd Nat.prime_seven
        (Nat.card_pos.ne') h7B h7sqB, pow_one]
  have hQLabel : IsMulCommutative (S ⊓ A : Subgroup (Bar2 D.M)) := by
    have : IsCyclic ↥(S ⊓ A) := isCyclic_of_prime_card hQLcard
    exact IsCyclic.isMulCommutative
  have hQKabel : IsMulCommutative ((S ⊓ (B ⊔ C)) ⊓ B : Subgroup (Bar2 D.M)) := by
    have : IsCyclic ↥((S ⊓ (B ⊔ C)) ⊓ B) := isCyclic_of_prime_card hQKcard
    exact IsCyclic.isMulCommutative
  have hQCp : IsPGroup 7 ↥(((S ⊓ (B ⊔ C)) ⊓ C) : Subgroup (Bar2 D.M)) :=
    IsPGroup.to_inf_left (p := 7) (H := S ⊓ (B ⊔ C)) (K := C) hSp'
  have hQCrank : CFSG.Open.pRank 7 (((S ⊓ (B ⊔ C)) ⊓ C)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num)
      (inf_le_right : ((S ⊓ (B ⊔ C)) ⊓ C) ≤ C)).trans hCrank
  have hQCCyc : IsCyclic ↥(((S ⊓ (B ⊔ C)) ⊓ C)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H.isCyclic_of_pRank_le_one
      Nat.prime_seven (by norm_num) hQCp hQCrank
  have hQCabel : IsMulCommutative (((S ⊓ (B ⊔ C)) ⊓ C) : Subgroup (Bar2 D.M)) := by
    have := hQCCyc
    exact IsCyclic.isMulCommutative
  have hQKQCbot : ((S ⊓ (B ⊔ C)) ⊓ B) ⊓ ((S ⊓ (B ⊔ C)) ⊓ C) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hmem : z ∈ B ⊓ C := ⟨hz.1.2, hz.2.2⟩
    rw [hBCbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hWcomm : IsMulCommutative W := by
    dsimp [W]
    let e := CFSG.GorensteinWalter.subgroup_sup_equiv_prod_of_commute_of_disjoint
      ((S ⊓ (B ⊔ C)) ⊓ B) ((S ⊓ (B ⊔ C)) ⊓ C) hQKQCbot
      (fun u v hu hv => Subgroup.mem_centralizer_iff.mp (hC_le_CB hv.2) u hu.2)
    have : IsMulCommutative (↥((S ⊓ (B ⊔ C)) ⊓ B) ×
        ↥((S ⊓ (B ⊔ C)) ⊓ C)) := inferInstance
    refine IsMulCommutative.of_comm fun x y => e.injective ?_
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := ↥((S ⊓ (B ⊔ C)) ⊓ B) ×
      ↥((S ⊓ (B ⊔ C)) ⊓ C))).comm (e x) (e y)
  have hW_le_CA : W ≤ Subgroup.centralizer (S ⊓ A : Set (Bar2 D.M)) := by
    dsimp [W]
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hLKcomm hy.2) x hx.2).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (hC_le_CA hx.2) y hy.2
  have hQLWbot : (S ⊓ A) ⊓ W = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzA : z ∈ A := hz.1.2
    have hWle : W ≤ B ⊔ C := by
      dsimp [W]
      exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
    have hzBC : z ∈ B ⊔ C := hWle hz.2
    have hmem : z ∈ A ⊓ (B ⊔ C) := ⟨hzA, hzBC⟩
    rw [hABCbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hScomm : IsMulCommutative S := by
    rw [hSdecomp]
    let e := CFSG.GorensteinWalter.subgroup_sup_equiv_prod_of_commute_of_disjoint
      (S ⊓ A) W hQLWbot
      (fun a w ha hw => Subgroup.mem_centralizer_iff.mp (hW_le_CA hw) a ha)
    have : IsMulCommutative (↥(S ⊓ A) × ↥W) := inferInstance
    refine IsMulCommutative.of_comm fun x y => e.injective ?_
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := ↥(S ⊓ A) × ↥W)).comm (e x) (e y)
  have hQcomm : IsMulCommutative (Q : Subgroup ↥D.M) := by
    have hcopQ : Nat.Coprime (Nat.card ↥(Q : Subgroup ↥D.M))
        (Nat.card ↥(CFSG.pCore 2 ↥D.M)) := by
      obtain ⟨a, ha⟩ := Q.isPGroup'.exists_card_eq
      obtain ⟨b, hb⟩ :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
      rw [ha, hb]
      exact (by norm_num : Nat.Coprime 7 2).pow a b
    have hdisjQ : (Q : Subgroup ↥D.M) ⊓ CFSG.pCore 2 ↥D.M = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopQ)
    have hker : ∀ x : (Q : Subgroup ↥D.M), π (x : ↥D.M) = 1 → x = 1 := by
      intro x hx
      have hxpc : (x : ↥D.M) ∈ CFSG.pCore 2 ↥D.M :=
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥D.M) _).mp hx
      have hxinf : (x : ↥D.M) ∈ (Q : Subgroup ↥D.M) ⊓ CFSG.pCore 2 ↥D.M :=
        ⟨x.2, hxpc⟩
      rw [hdisjQ] at hxinf
      exact Subtype.ext (Subgroup.mem_bot.mp hxinf)
    have hinj : ∀ x y : (Q : Subgroup ↥D.M),
        π (x : ↥D.M) = π (y : ↥D.M) → x = y := by
      intro x y hxy
      have h1 : π ((x * y⁻¹ : (Q : Subgroup ↥D.M)) : ↥D.M) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hxy, mul_inv_cancel]
      have h2 := hker (x * y⁻¹) h1
      calc x = x * y⁻¹ * y := by group
        _ = y := by rw [h2, one_mul]
    refine IsMulCommutative.of_comm fun a b => ?_
    apply hinj
    have h := hScomm.is_comm.comm
      (⟨π (a : ↥D.M), Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩⟩ : S)
      (⟨π (b : ↥D.M), Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩⟩ : S)
    simpa [map_mul] using congrArg Subtype.val h
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
  have h := congrArg Subtype.val (hQcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc x.1 * y.1 = D.M.subtype a * D.M.subtype b := by rw [← hax, ← hby]
    _ = D.M.subtype (a * b) := (map_mul _ _ _).symm
    _ = D.M.subtype (b * a) := by simpa using congrArg Subtype.val h
    _ = D.M.subtype b * D.M.subtype a := map_mul _ _ _
    _ = y.1 * x.1 := by rw [← hby, ← hax]

theorem exists_orderOf_seven_centralizing_bar
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hKne : K ≠ L) (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K) :
    ∃ w : Bar2 D.M, orderOf w = 7 ∧ w ∉ barImage D.M L ⊔ barImage D.M K ∧
      w ∈ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ∧
      w ∈ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) := by
  classical
  obtain ⟨x, hxM, ⟨k, hxord⟩, hxnot⟩ :=
    exists_sevenPower_not_mem_sup D ctx hK hshape hnotmain

  obtain ⟨w, hwL, hwK, hwne, k, hw7⟩ :=
    exists_centralizer_seven_power D ctx hK hKne hshape hxM ⟨k, hxord⟩ hxnot
  obtain ⟨-, -, -, hZfbL, hZfbK, hLKcomm, -, -⟩ :=
    barImage_LK_data D ctx hK hKne hshape
  have hZprod : (barImage D.M L ⊔ barImage D.M K) ⊓
      (Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M))) = ⊥ :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_bot hLKcomm hZfbL hZfbK
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp
    (orderOf_dvd_of_pow_eq_one hw7)
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      apply hwne
      rw [← orderOf_eq_one_iff, hj, h0, pow_zero]
    · exact h0
  let w0 : Bar2 D.M := w ^ 7 ^ (j - 1)
  have hw0pow : w0 ^ 7 = 1 := by
    change (w ^ 7 ^ (j - 1)) ^ 7 = 1
    rw [← pow_mul, show 7 ^ (j - 1) * 7 = 7 ^ j by
      rw [← pow_succ, Nat.sub_add_cancel hjpos], ← hj]
    exact pow_orderOf_eq_one w
  have hw0ne : w0 ≠ 1 := by
    intro h1
    have hdvd : orderOf w ∣ 7 ^ (j - 1) := orderOf_dvd_of_pow_eq_one (by
      simpa [w0] using h1)
    rw [hj] at hdvd
    have hle : 7 ^ j ≤ 7 ^ (j - 1) := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
    have hlt : 7 ^ (j - 1) < 7 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨w0, orderOf_eq_prime_iff.mpr ⟨hw0pow, hw0ne⟩, ?_,
    Subgroup.pow_mem _ hwL _, Subgroup.pow_mem _ hwK _⟩
  intro hmem
  have hbot : w0 ∈ (barImage D.M L ⊔ barImage D.M K) ⊓
      (Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M))) :=
    Subgroup.mem_inf.mpr ⟨hmem, Subgroup.mem_inf.mpr
      ⟨Subgroup.pow_mem _ hwL _, Subgroup.pow_mem _ hwK _⟩⟩
  rw [hZprod] at hbot
  exact hw0ne (Subgroup.mem_bot.mp hbot)

theorem exists_orderOf_seven_mem_of_bar (D : Data G) {wbar : Bar2 D.M}
    (hw : orderOf wbar = 7) :
    ∃ (w : G) (hwM : w ∈ D.M) (m : ℕ), orderOf w = 7 ∧ Nat.Coprime m 7 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hwM⟩ = wbar ^ m := by
  classical
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D.M) wbar
  have hg7ker : (g : ↥D.M) ^ 7 ∈ CFSG.pCore 2 ↥D.M := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥D.M)]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ((g : ↥D.M) ^ 7) = 1
    rw [map_pow, hg, ← hw, pow_orderOf_eq_one]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)))
    ⟨(g : ↥D.M) ^ 7, hg7ker⟩
  let m : ℕ := orderOf ((g : ↥D.M) ^ 7)
  have hm_eq : m = 2 ^ a := by
    change orderOf ((g : ↥D.M) ^ 7) = 2 ^ a
    have hcoe : orderOf (⟨(g : ↥D.M) ^ 7, hg7ker⟩ : ↥(CFSG.pCore 2 ↥D.M)) =
        orderOf ((g : ↥D.M) ^ 7) := (Subgroup.orderOf_coe _).symm
    rw [← hcoe]
    exact ha
  have hcop : Nat.Coprime m 7 := by
    rw [hm_eq]
    exact (by norm_num : Nat.Coprime 2 7).pow_left a
  have h7dvd : 7 ∣ orderOf (g : ↥D.M) := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) g
    have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) g) = 7 := by
      rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) g = wbar from hg]
      exact hw
    rwa [h2] at h
  have hdiv : orderOf (g : ↥D.M) / 7 = m := by
    have h1 := orderOf_pow (x := (g : ↥D.M)) (n := 7)
    rw [Nat.gcd_eq_right h7dvd] at h1
    change orderOf (g : ↥D.M) / 7 = m
    exact h1.symm
  have hordg : orderOf (g : ↥D.M) = 7 * m := by
    rw [← Nat.mul_div_cancel' h7dvd, hdiv]
  have hmpos : 0 < m := orderOf_pos _
  let w : G := (g : G) ^ m
  have hwM : w ∈ D.M := D.M.pow_mem g.2 m
  have hordw : orderOf w = 7 := by
    have hgmord : orderOf ((g : ↥D.M) ^ m) = 7 := by
      refine orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩
      · rw [← pow_mul, mul_comm, ← hordg, pow_orderOf_eq_one]
      · intro h1
        have hdvd : orderOf (g : ↥D.M) ∣ m := orderOf_dvd_of_pow_eq_one h1
        rw [hordg] at hdvd
        have hle : 7 * m ≤ m := Nat.le_of_dvd hmpos hdvd
        omega
    have hcoe : w = ((g : ↥D.M) ^ m : ↥D.M) := rfl
    rw [hcoe, Subgroup.orderOf_coe]
    exact hgmord
  refine ⟨w, hwM, m, hordw, hcop, ?_⟩
  have hsub : (⟨w, hwM⟩ : ↥D.M) = (g : ↥D.M) ^ m := Subtype.ext rfl
  rw [hsub, map_pow, hg]

theorem card_sylow_seven_eq_seven {K A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 7 A K)
    (h7dvd : 7 ∣ Nat.card (Bar2 K)) (h7sq : ¬ 7 ^ 2 ∣ Nat.card (Bar2 K)) :
    Nat.card A = 7 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcardK : Nat.card K = Nat.card (Bar2 K) * Nat.card ↥(CFSG.pCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have hK7dvd : 7 ∣ Nat.card K := by
    rw [hcardK]
    exact dvd_mul_of_dvd_left h7dvd _
  have hK7sq : ¬ 7 ^ 2 ∣ Nat.card K := by
    intro hd
    rw [hcardK] at hd
    apply h7sq
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [ha] at hd
    exact (by norm_num : Nat.Coprime (7 ^ 2) 2).pow_right a |>.dvd_of_dvd_mul_right hd
  have hfac : (Nat.card K).factorization 7 = 1 :=
    CFSG.GroupTheory.factorization_eq_one_of_dvd_of_not_sq_dvd Nat.prime_seven
      (Nat.card_pos.ne') hK7dvd hK7sq
  rw [hA.card_eq, hfac, pow_one]

theorem exists_elemAbelian_fortyNine_central
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p)) (hKne : K ≠ L)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K)
    (h55 : R17_55At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    ∃ (P E : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 7 P D.M ∧ E ≤ P ∧
      CFSG.Open.IsElemAbelian 7 E ∧ Nat.card E = 49 ∧
      E ≤ Subgroup.centralizer (P : Set G) ∧
      E ≤ centSection D.M L (CFSG.Open.pCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (ctx.hyp54.2 L ctx.memC).1
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp (ctx.hyp54.2 K hKcalM).1
  obtain ⟨wbar, hword, hwbar_out, hwbarL, hwbarK⟩ :=
    exists_orderOf_seven_centralizing_bar D ctx hK hKne hshape hnotmain
  obtain ⟨w, hwM, m, hwordw, hcop, himg⟩ := exists_orderOf_seven_mem_of_bar D hword
  have hzcard : Nat.card (Subgroup.zpowers w) = 7 := by
    rw [Nat.card_zpowers, hwordw]
  have hzp : IsPGroup 7 (Subgroup.zpowers w) :=
    IsPGroup.of_card (p := 7) (n := 1) (by rw [hzcard]; norm_num)
  obtain ⟨P, hP, hwP⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge
    (K := D.M) (Q := Subgroup.zpowers w) (Subgroup.zpowers_le.mpr hwM) hzp
  have hPcomm : IsMulCommutative P :=
    isMulCommutative_of_isSylowOf_seven_nonMain D ctx hK hKne hshape hnotmain
      h55 hSg P hP
  have hwP' : w ∈ P := hwP (Subgroup.mem_zpowers w)
  let A : Subgroup G := P ⊓ K
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 7 A K := hP.inf_of_le_normalizer hKM hMK
  have h7dvdK : 7 ∣ Nat.card (Bar2 K) := seven_dvd_card_bar_of_isL2_or_isSz hshape
  have h7sqK : ¬ 7 ^ 2 ∣ Nat.card (Bar2 K) := by
    rcases hshape with h | h
    · rw [card_of_isL2 h]; norm_num
    · rw [CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num
  have hAcard : Nat.card A = 7 := card_sylow_seven_eq_seven hAsyl h7dvdK h7sqK
  have hAK : A ≤ K := inf_le_right
  have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent ctx.memC
  have hKcomp : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hKcalM
  have hneLbKb : barImage D.M L ≠ barImage D.M K := fun h =>
    hKne (barImage_injOn_calC hKcalM ctx.memC h.symm)
  have hLKcomm : barImage D.M L ≤
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) := by
    rcases CFSG.LocalCores.distinct_components_commute hLcomp hKcomp with h | h
    · exact absurd h hneLbKb
    · rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hKcM : K ≤ F13.cMStar D.M L := by
    intro k hk
    refine uc22s13b_mem_cMStar (hKM hk) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hkbar : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨k, hKM hk⟩ ∈ barImage D.M K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    exact (Subgroup.mem_centralizer_iff.mp (hLKcomm hy) _ hkbar).symm
  have hAcent : A ≤ centSection D.M L (CFSG.Open.pCoreOf 2 L) := by
    rw [centSection_eq_cMStar hLM hML]
    exact hAK.trans hKcM
  have hwcL : w ∈ centSection D.M L (CFSG.Open.pCoreOf 2 L) := by
    rw [centSection_eq_cMStar hLM hML]
    refine uc22s13b_mem_cMStar hwM ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [himg]
    exact (Commute.pow_right (Subgroup.mem_centralizer_iff.mp hwbarL y hy) m).eq
  have hAw : ∀ a ∈ A, a * w = w * a := by
    intro a ha
    exact congrArg Subtype.val (hPcomm.is_comm.comm ⟨a, ha.1⟩ ⟨w, hwP'⟩)
  have hwA : w ∉ A := by
    intro hwA'
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hwM⟩ ∈ barImage D.M K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwA'.2)
    rw [himg] at hmk
    have hcyc : wbar ∈ Subgroup.zpowers (wbar ^ m) := by
      rw [mem_zpowers_pow_iff, hword]
      exact hcop
    exact hwbar_out (Subgroup.mem_sup_right (Subgroup.zpowers_le.mpr hmk hcyc))
  let E : Subgroup G := A ⊔ Subgroup.zpowers w
  have hEel : CFSG.Open.IsElemAbelian 7 E :=
    (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hAcard hwordw hwA hAw).1
  have hEcard : Nat.card E = 49 := by
    have := (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hAcard hwordw hwA hAw).2
    rw [this]; norm_num
  have hEP : E ≤ P := sup_le inf_le_left (Subgroup.zpowers_le.mpr hwP')
  have hEcentP : E ≤ Subgroup.centralizer (P : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (congrArg Subtype.val (hPcomm.is_comm.comm ⟨e, hEP he⟩ ⟨p, hp⟩)).symm
  have hEcentL : E ≤ centSection D.M L (CFSG.Open.pCoreOf 2 L) :=
    sup_le hAcent (Subgroup.zpowers_le.mpr hwcL)
  exact ⟨P, E, hP, hEP, hEel, hEcard, hEcentP, hEcentL⟩

theorem false_of_nonMain_17_61
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13)
    (h55 : R17_55At D V₀ V)
    (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D)
    (K : Subgroup G) (hK : K ∈ calC (Lp D p)) (hKne : K ≠ L)
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L →
      p ∣ Nat.card (barImage D.M K') → K' = K)
    (hnotmain : Opp 7 D.M ≠ L ⊔ K) : False := by
  have h7not : 7 ∉ D.sig := seven_notMem_sig D ctx h55 hSg hK hshape
  obtain ⟨h3lt, hp7, -⟩ :=
    three_lt_pRank_p_and_ne_seven D ctx hK hKne hshape hnotmain hSg h13 h7not
  have hp3 : p = 3 :=
    p_eq_three_of_not_mem_sup D ctx hK hdvd hshape hunique h56 h57 hThin hp7 h3lt
  obtain ⟨P, E, hP, hEP, hEel, hEcard, hEcentP, hEcentL⟩ :=
    exists_elemAbelian_fortyNine_central D ctx hK hKne hshape hnotmain h55 hSg
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hEM : E ≤ D.M := hEP.trans hP.le
  have hENL : E ≤ Subgroup.normalizer (L : Set G) :=
    fun e he => (hEcentL he).2.1
  have hENO : E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    fun e he => (hEcentL he).2.2.1
  have hcommLE : ⁅L, E⁆ ≤ CFSG.Open.pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro l hl e he
    have h := (Subgroup.inv_mem _ (hEcentL he)).2.2.2 l hl
    have heq : ⁅l, e⁆ = e * ⁅e⁻¹, l⁆ * e⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hEcentL he).2.2.1 _).mp h
  have hO2card : Nat.card (CFSG.Open.pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have h7O : ¬ 7 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    rw [hO2card]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_seven
      (by norm_num)
  have h3O : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    rw [hO2card]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three
      (by norm_num)
  have hEc : 0 < CFSG.Open.pRank 3 (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
    obtain ⟨S, hS, hSE⟩ := CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := 7) (q := 3) (X := L) (N := CFSG.Open.pCoreOf 2 L) (R := E)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hENL hENO hEel.isPGroup h7O hcommLE h3O
    have hScard : Nat.card S = 9 := card_sylow_three_eq_nine ctx.shapeL hS
    have hSel : CFSG.Open.IsElemAbelian 3 S := isElemAbelian_sylow_three ctx.shapeL hS
    have hSrank : 2 ≤ CFSG.Open.pRank 3 S := by
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := S) (E := S)
        le_rfl hSel (k := 2) (by simpa using hScard)
      simpa using h
    have hSle : S ≤ D.M ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf (hS.le.trans hLM) hSE
    exact lt_of_lt_of_le (by norm_num : 0 < 2)
      (hSrank.trans (CFSG.SectionRank.pRank_mono (by norm_num) hSle))
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = 7 →
      1 < CFSG.Open.pRank 3 (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
    intro X hXE hXcard
    have hXcent : X ≤ centSection D.M L (CFSG.Open.pCoreOf 2 L) := hXE.trans hEcentL
    have hXNL : X ≤ Subgroup.normalizer (L : Set G) := fun x hx => (hXcent hx).2.1
    have hXNO : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      fun x hx => (hXcent hx).2.2.1
    have hcommLX : ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      have h := (Subgroup.inv_mem _ (hXcent hx)).2.2.2 l hl
      have heq : ⁅l, x⁆ = x * ⁅x⁻¹, l⁆ * x⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp (hXcent hx).2.2.1 _).mp h
    have hXp : IsPGroup 7 X := IsPGroup.of_card (p := 7) (n := 1) (by rw [hXcard]; norm_num)
    obtain ⟨S, hS, hSX⟩ := CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := 7) (q := 3) (X := L) (N := CFSG.Open.pCoreOf 2 L) (R := X)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hXNL hXNO hXp h7O hcommLX h3O
    have hScard : Nat.card S = 9 := card_sylow_three_eq_nine ctx.shapeL hS
    have hSel : CFSG.Open.IsElemAbelian 3 S := isElemAbelian_sylow_three ctx.shapeL hS
    have hSrank : 2 ≤ CFSG.Open.pRank 3 S := by
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := S) (E := S)
        le_rfl hSel (k := 2) (by simpa using hScard)
      simpa using h
    have hSle : S ≤ D.M ⊓ Subgroup.normalizer (X : Set G) :=
      le_inf (hS.le.trans hLM)
        (hSX.trans (Subgroup.centralizer_le_normalizer (X : Set G)))
    exact lt_of_lt_of_le (by norm_num : 1 < 2)
      (hSrank.trans (CFSG.SectionRank.pRank_mono (by norm_num) hSle))
  exact false_of_E49_sylow_seven D ctx h55 h76 h614 hSg hK hshape
    hp3 E hEM hEel hEcard hEc hXN ⟨P, hP, le_inf hEP hEcentP⟩



end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
