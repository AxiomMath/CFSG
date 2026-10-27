module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5Cgs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.CGT.PushingUpLit.ThmOne.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22CmpX
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_inClassXBlock {X Y B : Subgroup G} (hX : X = Opp 3 Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k)
    (hA5 : IsAlt (Bar2 X) 5) (hBY : B ≤ Y) (hBsn : CFSG.Open.IsSubnormal B Y)
    (hBX : CFSG.AGLEmbedding.InClassXBlock B) (hB1 : B ≠ ⊥) : B = X := by
  obtain ⟨e⟩ := hA5
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
  let φ : X →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ CFSG.pCore 2 X := fun x hx => by
    have hx' : e (QuotientGroup.mk' (CFSG.pCore 2 X) x) = 1 := hx
    exact (QuotientGroup.eq_one_iff x).1 (e.map_eq_one_iff.1 hx')
  have hsnX : (B.subgroupOf X).IsSubnormal := by
    have h := hBsn.inf_of_le hXY
    rw [inf_eq_left.2 hBXle] at h
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hBXle).1 h
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

theorem pCoreOf_mem_invStar9 {Y H S : Subgroup G} (hYH : Y ≤ H) (hSY : IsSylowOf 2 S Y)
    (hSH : IsSylowOf 2 S H) : pCoreOf 2 Y ∈ InvStar9 H Y 2 := by
  refine ⟨⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y⟩,
    ?_⟩
  intro Q hQ _
  obtain ⟨hQH, hQ2, hYQ⟩ := hQ
  have hSQ : S ⊔ Q = S := hSH.eq_of_le le_sup_left (sup_le hSH.le hQH)
    (hSH.isPGroup.to_sup_of_normal_right' hQ2 (hSY.le.trans hYQ))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((le_sup_right.trans hSQ.le).trans hSY.le) hYQ hQ2

theorem r912A5_of_inputs (D : Data G) (h99 : R99 D) (h910 : R910 D)
    (h911 : R911 D) (h9R5 : R9R5 D) : R912A5 D := by
  intro Y H D₃ S hY hA5 hR
  have hSY : IsSylowOf 2 S Y := hY.2.2.2
  have hYH : Y ≤ H := hY.1.2.1.1
  have hYHM : Y ≤ H ⊓ D.M := le_inf hYH hY.1.1.1
  have hYX : Y ≤ normalizer (Opp 3 Y : Set G) := hYHM.trans
    ((normal_subgroupOf_iff_le_normalizer ((opp_le_self 3 Y).trans hYHM)).1 (h9R5 Y H D₃ S hY).1)
  have hidx : ∃ k : ℕ, ((Opp 3 Y).subgroupOf Y).index = 2 ^ k := hY.2.1.1.2.2.2.2
  have hSH : IsSylowOf 2 S H := by
    by_contra hS
    have hcgs := cgsIn_ne_of_isAlt (opp_le_self 3 Y) hYX hidx hSY hA5
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
    have hBeq := eq_of_inClassXBlock rfl hYX hidx hA5 hBY hBsn hBX hB1
    exact h911 Y hY.2.1
      (CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock (hBeq ▸ hBX))
  exact ⟨hSH, pCoreOf_mem_invStar9 hYH hSY hSH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
