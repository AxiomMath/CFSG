module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5Proof
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.EmptyFaithful.S1421QA23Rk
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.CGT.PushingUpLit.ThmOne.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22CmpX
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {G : Type} [Group G] [Finite G]

private theorem n924_card_psl2 {Y : Type} [Group Y] {m : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 2 m) :
    Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hf : 1 ≤ m := h.1.2.1
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have hodd : Odd (2 ^ m - 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [h1]
  unfold CFSG.Open.ordA
  norm_num [Finset.Icc_self, hgcd]

private theorem n924_card_map_eq_two_pow {X : Type} [Group X] [Finite X] {Y : Type} [Group Y]
    [Finite Y] {V : Subgroup X} (φ : X →* Y) (hφ : Function.Surjective φ) (hker : φ.ker ≤ V)
    (hV : IsPGroup 2 V) (hodd : ¬ 2 ∣ V.index) {m : ℕ} (hm : 1 ≤ m)
    (hY : Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : Nat.card (V.map φ) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hV.map φ)
  have hcard := card_mul_index (V.map φ)
  rw [hY, index_map_eq V hφ hker, ha] at hcard
  have hoddV : Odd V.index := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hoddK : Odd ((2 ^ m) ^ 2 - 1) :=
    CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm (n := 2) (by norm_num)
  have ham := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hoddV hoddK hcard
  rw [ham] at ha
  exact ha

private theorem n924_eq_of_inClassXBlock {X Y B : Subgroup G} {m : ℕ} (hX : X = Opp 3 Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k)
    (hL2 : IsL2 (Bar2 X) m) (hm : 2 ≤ m) (hBY : B ≤ Y) (hBsn : CFSG.Open.IsSubnormal B Y)
    (hBX : CFSG.AGLEmbedding.InClassXBlock B) (hB1 : B ≠ ⊥) : B = X := by
  have hXY : X ≤ Y := hX ▸ opp_le_self 3 Y
  have hres : CFSG.RankThree.PartOne.oResidualTwo B = ⊤ :=
    (CFSG.AGLEmbedding.NoXBlock.isShortGroup_of_isShort2 hBX.1).residual_eq
  have hBXle : B ≤ X := by
    obtain ⟨k, hk⟩ := hidx
    haveI : (X.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hXY).2 hYX
    have hN : (X.subgroupOf B).Normal :=
      ⟨fun n hn b => (mem_normalizer_iff.1 (hYX (hBY b.2)) n).1 hn⟩
    have htop := CFSG.CGT.PushingUpLit.oResidualTwo_eq_top_iff.1 hres (X.subgroupOf B) hN
      fun b => ⟨k, by
        have h := pow_index_mem (X.subgroupOf Y) (⟨b, hBY b.2⟩ : Y)
        rw [hk] at h
        exact h⟩
    intro b hb
    have hb' : (⟨b, hb⟩ : B) ∈ X.subgroupOf B := by
      rw [htop]
      exact mem_top _
    exact hb'
  let φ : X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ CFSG.pCore 2 X := le_of_eq (QuotientGroup.ker_mk' _)
  have hsnX : (B.subgroupOf X).IsSubnormal := by
    have h := hBsn.inf_of_le hXY
    rw [inf_eq_left.2 hBXle] at h
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hBXle).1 h
  haveI : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  rcases (hsnX.map hφ).eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · refine absurd ?_ hB1
    have hle : B ≤ pCoreOf 2 X := fun b hb =>
      mem_map.2 ⟨⟨b, hBXle hb⟩, hker ((Subgroup.map_eq_bot_iff _).1 h (mem_subgroupOf.2 hb)), rfl⟩
    have hB2 : IsPGroup 2 B := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hle
    have hbot := CFSG.CGT.PushingUpLit.oResidualTwo_eq_top_iff.1 hres ⊥ inferInstance
      fun g => ⟨(hB2 g).choose, mem_bot.2 (hB2 g).choose_spec⟩
    refine eq_bot_iff.2 fun b hb => mem_bot.2 ?_
    have hb' : (⟨b, hb⟩ : B) ∈ (⊥ : Subgroup B) := by
      rw [hbot]
      exact mem_top _
    exact congrArg Subtype.val (mem_bot.1 hb')
  have hsup : B.subgroupOf X ⊔ CFSG.pCore 2 X = ⊤ := by
    have h' := comap_map_eq φ (B.subgroupOf X)
    rw [h, comap_top] at h'
    exact top_le_iff.1 (h'.le.trans (sup_le_sup_left hker _))
  have hON : pCoreOf 2 X ≤ normalizer (B : Set G) :=
    CFSG.CGT.PushingUpLit.ThmOne.le_normalizer_of_isSubnormal_of_isPGroup hres hBXle hsnX
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (hBXle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  haveI hBn : (B.subgroupOf X).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
    refine sup_le le_normalizer fun o ho => mem_normalizer_iff.2 fun x => ?_
    exact mem_normalizer_iff.1 (hON (mem_map_of_mem X.subtype ho)) (x : G)
  refine le_antisymm hBXle ?_
  rw [hX]
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine (closure_le B).2 fun x hx => ?_
  obtain ⟨k, hk⟩ := hx.2
  have hxX : x ∈ X := by
    rw [hX]
    exact subset_closure hx
  have hmem : (⟨x, hxX⟩ : X) ∈ B.subgroupOf X ⊔ CFSG.pCore 2 X := by
    rw [hsup]
    exact mem_top _
  rw [← SetLike.mem_coe, mul_normal] at hmem
  obtain ⟨b, hb, o, ho, hbo⟩ := Set.mem_mul.1 hmem
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := X) ⟨o, ho⟩
  have hoj : o ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hq : ((⟨x, hxX⟩ : X) : X ⧸ B.subgroupOf X) = (o : X ⧸ B.subgroupOf X) := by
    rw [← hbo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hb, one_mul]
  have hq3 : ((⟨x, hxX⟩ : X) : X ⧸ B.subgroupOf X) ^ 3 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).2]
    have h3 : (⟨x, hxX⟩ : X) ^ 3 ^ k = 1 := Subtype.ext (by
      show x ^ 3 ^ k = 1
      rw [← hk]
      exact pow_orderOf_eq_one x)
    rw [h3]
    exact one_mem _
  have hq2 : ((⟨x, hxX⟩ : X) : X ⧸ B.subgroupOf X) ^ 2 ^ j = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, hoj, QuotientGroup.mk_one]
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_of_pow_eq_one hq2)
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_pow_primes k j Nat.prime_three Nat.prime_two
    (by norm_num))] at hd
  have h1 : ((⟨x, hxX⟩ : X) : X ⧸ B.subgroupOf X) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

private theorem n924_cgsIn_ne_of_isL2 {X Y S : Subgroup G} {m : ℕ} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k)
    (hSY : IsSylowOf 2 S Y) (hL2 : IsL2 (Bar2 X) m) (hm : 2 ≤ m)
    (hB : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ Y ≤ normalizer (C : Set G)) :
    CFSG.Quasithin.cgsIn Y S ≠ Y := by
  let φ : X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hSX : IsSylowOf 2 (S ⊓ X) X := hSY.inf_of_le_normalizer hXY hYX
  have hO2 : pCoreOf 2 X ≤ S ⊓ X :=
    CFSG.Quasithin.pCoreOf_two_le_of_sylowIn inf_le_right hSX.isPGroup (isSylowOf_iff.1 hSX).2.2
  have hker : φ.ker ≤ S.subgroupOf X := fun x hx => by
    have hx' : ((x : X) : Bar2 X) = 1 := hx
    exact mem_subgroupOf.2
      (mem_inf.1 (hO2 (mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff x).1 hx')))).1
  have hVodd : ¬ 2 ∣ (S.subgroupOf X).index := by
    have := (isSylowOf_iff.1 hSX).2.2
    rwa [relIndex, inf_subgroupOf_right] at this
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 X) .PSL 2 2 m :=
    hL2.statedClassicalModel (by decide)
  have hcard : Nat.card (Bar2 X) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := n924_card_psl2 hmodel
  have h4 : Nat.card ((S.subgroupOf X).map φ) = 2 ^ m :=
    n924_card_map_eq_two_pow φ hφ hker hSY.isPGroup.comap_subtype hVodd (by omega) hcard
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf ((S.subgroupOf X).map φ) ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf, isSylowOf_iff]
    refine ⟨le_top, hSY.isPGroup.comap_subtype.map φ, ?_⟩
    rw [Subgroup.relIndex_top_right, index_map_eq (S.subgroupOf X) hφ hker]
    exact hVodd
  have hstep : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      Y ⊓ normalizer (C : Set G) ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
    intro C hCS hC hchar
    have hSC : S ≤ normalizer (C : Set G) :=
      le_normalizer.trans (normalizer_le_normalizer_of_char hCS hchar)
    have hVK : S.subgroupOf X ≤ (Y ⊓ normalizer (C : Set G)).subgroupOf X := fun x hx =>
      mem_subgroupOf.2 (mem_inf.2 ⟨hSY.le (mem_subgroupOf.1 hx), hSC (mem_subgroupOf.1 hx)⟩)
    have hmap : ((Y ⊓ normalizer (C : Set G)).subgroupOf X).map φ ≠ ⊤ := by
      intro h
      refine hB C hCS hC hchar (le_of_le_of_isSylowOf (fun x hx => ?_) hSC hSY hidx)
      have h' := comap_map_eq φ ((Y ⊓ normalizer (C : Set G)).subgroupOf X)
      rw [h, comap_top, sup_eq_left.2 (hker.trans hVK)] at h'
      have hx' : (⟨x, hx⟩ : X) ∈ (Y ⊓ normalizer (C : Set G)).subgroupOf X := by
        rw [← h']
        exact mem_top _
      exact (mem_inf.1 (mem_subgroupOf.1 hx')).2
    have hKV : (Y ⊓ normalizer (C : Set G)).subgroupOf X ≤
        normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
      have h1 := (le_comap_map (f := φ) ((Y ⊓ normalizer (C : Set G)).subgroupOf X)).trans
        (comap_mono (CFSG.Quasithin.QA23.normalizer_of_isPSL_two hmodel hU (map_mono hVK)
          hmap))
      rwa [comap_normalizer_eq_of_surjective _ hφ, comap_map_eq, sup_eq_left.2 hker] at h1
    have hKXN : Y ⊓ normalizer (C : Set G) ⊓ X ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
      have h1 := (map_mono (f := X.subtype) hKV).trans (le_normalizer_map X.subtype)
      rwa [subgroupOf_map_subtype, subgroupOf_map_subtype] at h1
    have hSXK : S ⊓ X ≤ Y ⊓ normalizer (C : Set G) ⊓ X := inf_le_inf_right _ (le_inf hSY.le hSC)
    have hcore : pCoreOf 2 (Y ⊓ normalizer (C : Set G) ⊓ X) = S ⊓ X := le_antisymm
      (CFSG.Quasithin.pCoreOf_two_le_of_sylowIn hSXK hSX.isPGroup
        (isSylowOf_iff.1 (hSX.of_le hSXK inf_le_right)).2.2)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSXK hKXN hSX.isPGroup)
    have hKK : Y ⊓ normalizer (C : Set G) ≤
        normalizer ((Y ⊓ normalizer (C : Set G) ⊓ X : Subgroup G) : Set G) :=
      fun k hk => mem_normalizer_iff.2 fun h =>
        (mem_inf.trans (and_congr (mem_normalizer_iff.1 (le_normalizer hk) h)
          (mem_normalizer_iff.1 (hYX (mem_inf.1 hk).1) h))).trans mem_inf.symm
    rw [← hcore]
    exact hKK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  intro hcgs
  have hcgsle : CFSG.Quasithin.cgsIn Y S ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
    unfold CFSG.Quasithin.cgsIn
    exact iSup_le fun C => iSup_le fun hCS => iSup_le fun hC => iSup_le fun hchar =>
      hstep C hCS hC hchar
  have hn : (S.subgroupOf X).Normal :=
    normal_subgroupOf_iff_le_normalizer_inf.2 (hXY.trans (hcgs.symm.le.trans hcgsle))
  haveI : ((S.subgroupOf X).map φ).Normal := hn.map φ hφ
  haveI : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have h4le : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S.subgroupOf X).map φ) with h | h <;>
    rw [h] at h4
  · rw [card_bot] at h4
    omega
  · rw [card_top, hcard] at h4
    have hone : (2 ^ m) ^ 2 - 1 = 1 :=
      Nat.mul_left_cancel (by positivity : 0 < 2 ^ m) (by simpa using h4)
    have h16 : 16 ≤ (2 ^ m) ^ 2 := by
      calc 16 = 4 * 4 := by norm_num
        _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul h4le h4le
        _ = (2 ^ m) ^ 2 := by ring
    omega

@[expose] def R912L2 (D : Data G) : Prop :=
  ∀ Y H D₃ S : Subgroup G, Hyp97 D Y H D₃ S → ∀ m : ℕ, 2 ≤ m → IsL2 (Bar2 (Opp 3 Y)) m →
    pCoreOf 2 Y ≠ ⊥ → IsSylowOf 2 S H ∧ pCoreOf 2 Y ∈ InvStar9 H Y 2

theorem r912L2_of_inputs (D : Data G) (h99 : R99 D) (h910 : R910 D)
    (h911 : R911 D) (h9R5 : R9R5 D) : R912L2 D := by
  intro Y H D₃ S hY m hm hL2 hR
  have hSY : IsSylowOf 2 S Y := hY.2.2.2
  have hYH : Y ≤ H := hY.1.2.1.1
  have hYHM : Y ≤ H ⊓ D.M := le_inf hYH hY.1.1.1
  have hYX : Y ≤ normalizer (Opp 3 Y : Set G) := hYHM.trans
    ((normal_subgroupOf_iff_le_normalizer ((opp_le_self 3 Y).trans hYHM)).1 (h9R5 Y H D₃ S hY).1)
  have hidx : ∃ k : ℕ, ((Opp 3 Y).subgroupOf Y).index = 2 ^ k := hY.2.1.1.2.2.2.2
  have hSH : IsSylowOf 2 S H := by
    by_contra hS
    have hcgs := n924_cgsIn_ne_of_isL2 (opp_le_self 3 Y) hYX hidx hSY hL2 hm
      fun C hCS hC hchar => not_le_normalizer_of_hyp97 h910 h9R5 hY hS hCS hC hchar
    haveI := D.standing.simple
    have hYtop : Y ≠ ⊤ := fun h => CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top
      D.standing.nonab D.maxLocal.1 (top_le_iff.1 (h ▸ hY.1.1.1))
    have hC2 : CFSG.QuasithinUnique.CharTwo Y := by
      apply charTwo_of_fitting_eq
      rw [← CFSG.Adapters.genFittingFStar_eq_foundations]
      exact map_injective Y.subtype_injective (h99 Y hY.2.1 hR)
    obtain ⟨B, hBY, hBsn, hBX, hBc⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved G Y S
        (D.standing.kProper.isKGroup Y hYtop) hC2 (isSylowOf_iff.1 hSY) hcgs
    have hB1 : B ≠ ⊥ := fun h => hBc (by rw [h]; exact bot_le)
    have hBeq := n924_eq_of_inClassXBlock rfl hYX hidx hL2 hm hBY hBsn hBX hB1
    exact h911 Y hY.2.1
      (CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock (hBeq ▸ hBX))
  exact ⟨hSH, pCoreOf_mem_invStar9 hYH hSY hSH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
