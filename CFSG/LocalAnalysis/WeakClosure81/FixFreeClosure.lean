module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveOTwoBar
public import CFSG.GroupTheory.PerfectNormalConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem fixFree_closure_facts {V T J X₁ U : Subgroup G}
    (hV1 : V ≠ ⊥) (hVT : V ≤ T) (hX₁V : X₁ ≤ normalizer (V : Set G)) (hT : IsSylowIn 2 T X₁)
    (hJX : J ≤ X₁) (hXJ : X₁ ≤ normalizer (J : Set G)) (hX₁ : X₁ = T ⊔ J)
    (hJs : IsSimpleGroup (Bar2 J)) (hfix : V ⊓ centralizer (J : Set G) = ⊥)
    (hUdef : U = CFSG.Quasithin.conjClosure (V ⊓ centralizer (T : Set G)) X₁) :
    U ≠ ⊥ ∧ U ≤ V ∧ X₁ ≤ normalizer (U : Set G) ∧
      J ⊓ centralizer (U : Set G) = pCoreOf 2 J ∧ X₁ ⊓ centralizer (U : Set G) ≤ T := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : T ≤ X₁ := hT.le
  have hTV : T ≤ normalizer (V : Set G) := hTX.trans hX₁V
  have hTJ : T ≤ normalizer (J : Set G) := hTX.trans hXJ
  have hCV : V ⊓ centralizer (T : Set G) ≠ ⊥ := by
    intro hbot
    refine uc22p22na_inf_center_ne_bot hT.isPGroup hVT hTV hV1 (le_bot_iff.1 ?_)
    rw [← hbot]
    exact inf_le_inf_left V inf_le_right
  have hUne : U ≠ ⊥ := by
    have hCU : V ⊓ centralizer (T : Set G) ≤ U := by
      rw [hUdef]
      exact le_conjClosure _ _
    exact fun h => hCV (le_bot_iff.1 (h ▸ hCU))
  have hUV : U ≤ V := by
    rw [hUdef]
    exact conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hX₁V hh) z).mp hz.1
  have hXU : X₁ ≤ normalizer (U : Set G) := by
    rw [hUdef]
    exact le_normalizer_conjClosure _ _
  have hcent_closure : ∀ R : Subgroup G, R ≤ X₁ → (R.subgroupOf X₁).Normal →
      IsPGroup 2 R → R ≤ centralizer (U : Set G) := by
    intro R hRX hRnorm hR2
    obtain ⟨a, ha⟩ := hR2.exists_card_eq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (ha ▸ Subgroup.relIndex_dvd_card (centralizer (U : Set G)) R)
    rw [hUdef] at hk ⊢
    exact le_centralizer_conjClosure_of_two_pow_relIndex hT inf_le_right hRX hRnorm ⟨k, hk⟩
  have hOJ : pCoreOf 2 J ≤ centralizer (U : Set G) := by
    have hO2 : IsPGroup 2 (pCoreOf 2 J) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥J)).map J.subtype
    refine hcent_closure (pCoreOf 2 J) ?_ ?_ hO2
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJX
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJX)).mpr
        (hXJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J))
  have hOJle : pCoreOf 2 J ≤ J ⊓ centralizer (U : Set G) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 J) hOJ
  have hKJ : J ⊓ centralizer (U : Set G) = pCoreOf 2 J := by
    have hJN : J ≤ normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
      (hJX.trans hXU).trans
        (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup U)
    have hJnormK : J ≤ normalizer ((J ⊓ centralizer (U : Set G)) : Set G) :=
      (le_inf Subgroup.le_normalizer hJN).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hKn : ((J ⊓ centralizer (U : Set G)).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hJnormK
    have hpcn : (CFSG.pCore 2 ↥J).Normal := CFSG.pCore_normal
    rcases CFSG.GroupTheory.le_or_sup_eq_top_of_normal_of_isSimpleGroup_quotient
      (N := CFSG.pCore 2 ↥J)
      (K := (J ⊓ centralizer (U : Set G)).subgroupOf J) hJs with hle | htop
    · refine le_antisymm ?_ hOJle
      intro j hj
      have hjK : (⟨j, hj.1⟩ : ↥J) ∈ (J ⊓ centralizer (U : Set G)).subgroupOf J := hj
      exact Subgroup.mem_map.mpr ⟨⟨j, hj.1⟩, hle hjK, rfl⟩
    · exfalso
      have hJleCU : J ≤ centralizer (U : Set G) := by
        intro j hj
        have hjtop : (⟨j, hj⟩ : ↥J) ∈
            (J ⊓ centralizer (U : Set G)).subgroupOf J ⊔ CFSG.pCore 2 ↥J := by
          rw [htop]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_sup_of_normal_right] at hjtop
        obtain ⟨y, hy, z, hz, hyz⟩ := hjtop
        have hyCU : (y : G) ∈ centralizer (U : Set G) := hy.2
        have hzCU : (z : G) ∈ centralizer (U : Set G) :=
          hOJ (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
        have hval : (j : G) = (y : G) * (z : G) := by
          have := congrArg (fun w : ↥J => (w : G)) hyz
          simpa using this.symm
        rw [hval]
        exact (Subgroup.centralizer (U : Set G)).mul_mem hyCU hzCU
      have hUJ : U ≤ centralizer (J : Set G) :=
        (Subgroup.le_centralizer_iff).1 hJleCU
      have hUbot : U ≤ (⊥ : Subgroup G) := by
        have hle : U ≤ V ⊓ centralizer (J : Set G) := le_inf hUV hUJ
        rwa [hfix] at hle
      exact hUne (le_bot_iff.1 hUbot)
  set K : Subgroup G := X₁ ⊓ centralizer (U : Set G) with hKdef
  have hKX : K ≤ X₁ := (le_of_eq hKdef).trans inf_le_left
  have hKinfJ : K ⊓ J = pCoreOf 2 J := by
    rw [hKdef]
    calc (X₁ ⊓ centralizer (U : Set G)) ⊓ J = J ⊓ centralizer (U : Set G) := by
          refine le_antisymm (fun x hx => ⟨hx.2, hx.1.2⟩) (fun x hx => ?_)
          exact ⟨⟨hJX hx.1, hx.2⟩, hx.1⟩
      _ = pCoreOf 2 J := hKJ
  have hKnorm : (K.subgroupOf X₁).Normal := by
    rw [hKdef]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer
        (hXU.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup U))).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
  have hK2 : IsPGroup 2 K := by
    obtain ⟨a, ha⟩ := ((CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥J)).map
      J.subtype).exists_card_eq
    have ha' : Nat.card ↥(pCoreOf 2 J) = 2 ^ a := ha
    obtain ⟨c, hc⟩ := hT.isPGroup.exists_card_eq
    have hrelX : J.relIndex X₁ = (T ⊓ J).relIndex T := by
      have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := T) (K := J) hTJ).2
      rwa [hX₁]
    have hdvdX : J.relIndex X₁ ∣ 2 ^ c := by
      rw [hrelX, ← hc]
      exact Subgroup.relIndex_dvd_card (T ⊓ J) T
    have hKJnorm : K ≤ normalizer (J : Set G) := hKX.trans hXJ
    have hrelK : (K ⊓ J).relIndex K = J.relIndex (K ⊔ J) :=
      ((CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := K) (K := J) hKJnorm).2).symm
    have hcardK : Nat.card ↥K = 2 ^ a * J.relIndex (K ⊔ J) := by
      have h := (Subgroup.relIndex_mul_card (K ⊓ J) K).symm
      rw [show (K ⊓ J) ⊓ K = K ⊓ J from inf_of_le_left inf_le_left] at h
      rw [hrelK] at h
      rw [h, hKinfJ, ha', Nat.mul_comm]
    have hdvdKJ : J.relIndex (K ⊔ J) ∣ J.relIndex X₁ := by
      have hmul := Subgroup.relIndex_mul_relIndex J (K ⊔ J) X₁ le_sup_right
        (sup_le hKX hJX)
      exact ⟨(K ⊔ J).relIndex X₁, hmul.symm⟩
    have hdvdK : Nat.card ↥K ∣ 2 ^ a * 2 ^ c := by
      rw [hcardK]
      exact Nat.mul_dvd_mul_left (2 ^ a) (hdvdKJ.trans hdvdX)
    refine IsPGroup.of_card_dvd_pow (n := a + c) ?_
    rwa [pow_add]
  have hKT : K ≤ T := IsSylowIn.le_of_normal hT hKX hKnorm hK2
  exact ⟨hUne, hUV, hXU, hKJ, hKdef ▸ hKT⟩

end CFSG.LocalAnalysis.WeakClosure81
