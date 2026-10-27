module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758Defs
import CFSG.Quasithin.Background.C126Solv
import CFSG.Quasithin.Background.C126Glue
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Group
import CFSG.Quasithin.Background.F6F613Basic
import CFSG.Quasithin.Background.C116Bridge.Main
import CFSG.Quasithin.H13.VolIC113c
import CFSG.Quasithin.Background.RonanE111MemE1
import CFSG.Quasithin.Background.C126A5ExtractAux
import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowThree
import CFSG.GroupTheory.WielandtProductAux
import CFSG.GroupTheory.TwoReflections
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L M : Subgroup G}

theorem ParabolicA.exists_block (hA : AmalgamS3 G₀ G₁ G₂ T L) (hM : ParabolicA G₁ G₂ M) :
    ∃ (W : Subgroup G) (r : G), W ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ∧ IsElemAbelian 2 W ∧
      G₂ ≤ Subgroup.normalizer (W : Set G) ∧
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ pCoreOf 2 G₁ ≤ Subgroup.centralizer (W : Set G) ∧
      r ∈ G₂ ∧ r ∉ G₁ ∧ (∀ d ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂, r * d * r⁻¹ * d⁻¹ ∈ W) ∧
      Nat.card W = 4 ∧ W ⊓ Subgroup.centralizer ({r} : Set G) = ⊥ := by
  classical
  have hQ1_2 : IsPGroup 2 (pCoreOf 2 G₁) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁
  have hQ1ne : pCoreOf 2 G₁ ≠ ⊥ := by
    intro hbot
    have hconjbot : conjClosure (⊥ : Subgroup G) G₂ = ⊥ := by
      refine le_antisymm (conjClosure_le ?_) bot_le
      intro h _ z hz
      rw [Subgroup.mem_bot] at hz
      simp [hz]
    have hMbot : M = ⊥ := by
      refine le_bot_iff.mp (hM.le_conjClosure.trans ?_)
      simpa [hbot] using hconjbot
    have hrel := hM.relIndex
    rw [hbot, hMbot, Subgroup.relIndex_self] at hrel
    norm_num at hrel
  have hQ1ltM : pCoreOf 2 G₁ < M := by
    refine lt_of_le_of_ne hM.isSylowTwoOf.1 ?_
    intro hEq
    have hrel := hM.relIndex
    rw [hEq, Subgroup.relIndex_self] at hrel
    norm_num at hrel
  have hmax : IsMaxSubgroupIn M (pCoreOf 2 G₁) := by
    refine ⟨hQ1ltM, ?_⟩
    intro K hK hKM
    have hprime : ((pCoreOf 2 G₁).relIndex M).Prime := by
      rw [hM.relIndex]
      exact Nat.prime_three
    obtain ⟨x, hxK, hxQ⟩ := SetLike.exists_of_lt hK
    exact le_antisymm hKM
      (CFSG.GroupTheory.SmallFixedTwoGroup.le_of_relIndex_prime hK.le hKM hprime hxK hxQ)
  have hmin : MinParabolic M (pCoreOf 2 G₁) (pCoreOf 2 G₁) :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15412.minParabolic_of_isMaxSubgroupIn
      hM.isSylowTwoOf hM.not_le_normalizer hmax
  have hU : M ∈ uFamHat M (pCoreOf 2 G₁) := CFSG.Quasithin.C126.mem_uFamHat_self hmin
  obtain ⟨a, ha⟩ := hM.card
  have hsolvM : Group.IsSolvable ↥M :=
    CFSG.Quasithin.F6.isSolvable_of_card_eq_two_pow_mul_three (Y := M) ha
  have hSQ : IsSQTKTC M :=
    CFSG.Quasithin.C116Bridge.isSQTKTC_of_isSQTKIn
      (CFSG.Quasithin.F6.isSQTKIn_of_card_eq_two_pow_mul_three (Y := M) ha)
  have hpcM : perfectCore M = ⊥ := (isSolvable_iff_perfectCore_eq_bot M).mp hsolvM
  have hsolv_le : perfectCore M ≤ Subgroup.centralizer (VZ (pCoreOf 2 G₁) M : Set G) := by
    rw [hpcM]
    exact bot_le
  obtain ⟨C₁, C₂, hC⟩ := CFSG.Quasithin.exists_isGNChoice (G := G) theoremC118
  have hpair := hC.pair (pCoreOf 2 G₁) hQ1_2 hQ1ne
  have hC1ne : C₁ (pCoreOf 2 G₁) ≠ ⊥ := hpair.1
  have hC1Z : C₁ (pCoreOf 2 G₁) ≤ omegaOneCenterOf (pCoreOf 2 G₁) := hpair.2.1
  have hC1char : ((C₁ (pCoreOf 2 G₁)).subgroupOf (pCoreOf 2 G₁)).Characteristic := hpair.2.2.1
  have hC2ne : C₂ (pCoreOf 2 G₁) ≠ ⊥ := hpair.2.2.2.1
  have hC2B : C₂ (pCoreOf 2 G₁) ≤ baum (pCoreOf 2 G₁) := hpair.2.2.2.2.1
  have hC2char : ((C₂ (pCoreOf 2 G₁)).subgroupOf (baum (pCoreOf 2 G₁))).Characteristic :=
    hpair.2.2.2.2.2.1
  have hC1leQ : C₁ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ :=
    hC1Z.trans (C1GN.omegaOneCenterOf_le_self _)
  have hQ1centC1 : pCoreOf 2 G₁ ≤
      Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcz : c ∈ centerOf (pCoreOf 2 G₁) :=
      C1GN.omegaOneCenterOf_le_centerOf _ (hC1Z hc)
    exact (Subgroup.mem_centralizer_iff.mp hcz.2 q hq).symm
  have hNQ1C2 : Subgroup.normalizer (pCoreOf 2 G₁ : Set G) ≤
      Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) :=
    (normalizer_le_normalizer_baum _).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC2B hC2char)
  have hQ1normC2 : pCoreOf 2 G₁ ≤
      Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) :=
    Subgroup.le_normalizer.trans hNQ1C2
  have hA1 : M ⊓ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) ≤ pCoreOf 2 G₁ := by
    by_contra hnot
    have hle_inf : pCoreOf 2 G₁ ≤
        M ⊓ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) :=
      le_inf hM.isSylowTwoOf.1 hQ1centC1
    have hlt : pCoreOf 2 G₁ <
        M ⊓ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) :=
      lt_of_le_of_ne hle_inf (fun heq => hnot (heq ▸ le_rfl))
    have heq : M ⊓ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) = M :=
      hmax.2 _ hlt inf_le_left
    have hMcent : M ≤ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G) :=
      heq ▸ inf_le_right
    have hMN : M ≤ Subgroup.normalizer (C₁ (pCoreOf 2 G₁) : Set G) :=
      hMcent.trans (Subgroup.centralizer_le_normalizer _)
    have hG1N : G₁ ≤ Subgroup.normalizer (C₁ (pCoreOf 2 G₁) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) G₁).trans
        (normalizer_le_normalizer_of_characteristic_subgroupOf hC1leQ hC1char)
    have hG2N : G₂ ≤ Subgroup.normalizer (C₁ (pCoreOf 2 G₁) : Set G) := by
      rw [← hM.sup_eq]
      exact sup_le hMN (inf_le_left.trans hG1N)
    have hG0N : G₀ ≤ Subgroup.normalizer (C₁ (pCoreOf 2 G₁) : Set G) := by
      rw [hA.hyp.gen]
      exact sup_le hG1N hG2N
    have hC12 : IsPGroup 2 (C₁ (pCoreOf 2 G₁)) := hQ1_2.to_le hC1leQ
    have hleG0 : C₁ (pCoreOf 2 G₁) ≤ G₀ :=
      hC1leQ.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₁).trans hA.hyp.le₁)
    have hp := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hleG0 hG0N hC12
    rw [hA.hyp.o2_trivial] at hp
    exact hC1ne (le_bot_iff.mp hp)
  have hA2 : M ⊓ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) ≤ pCoreOf 2 G₁ := by
    by_contra hnot
    have hle_inf : pCoreOf 2 G₁ ≤
        M ⊓ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) :=
      le_inf hM.isSylowTwoOf.1 hQ1normC2
    have hlt : pCoreOf 2 G₁ <
        M ⊓ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) :=
      lt_of_le_of_ne hle_inf (fun heq => hnot (heq ▸ le_rfl))
    have heq : M ⊓ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) = M :=
      hmax.2 _ hlt inf_le_left
    have hMN : M ≤ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) := heq ▸ inf_le_right
    have hG1N : G₁ ≤ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) G₁).trans hNQ1C2
    have hG2N : G₂ ≤ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) := by
      rw [← hM.sup_eq]
      exact sup_le hMN (inf_le_left.trans hG1N)
    have hG0N : G₀ ≤ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G) := by
      rw [hA.hyp.gen]
      exact sup_le hG1N hG2N
    have hC2Q : C₂ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ := hC2B.trans (C1GN.baum_le _)
    have hC22 : IsPGroup 2 (C₂ (pCoreOf 2 G₁)) := hQ1_2.to_le hC2Q
    have hleG0 : C₂ (pCoreOf 2 G₁) ≤ G₀ :=
      hC2Q.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 G₁).trans hA.hyp.le₁)
    have hp := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hleG0 hG0N hC22
    rw [hA.hyp.o2_trivial] at hp
    exact hC2ne (le_bot_iff.mp hp)
  have hM' : (M ⊓ Subgroup.centralizer (C₁ (pCoreOf 2 G₁) : Set G)) ⊔
      (M ⊓ Subgroup.normalizer (C₂ (pCoreOf 2 G₁) : Set G)) ≤ pCoreOf 2 G₁ :=
    sup_le hA1 hA2
  obtain ⟨K, hKblock, hKalt, hKJ, hMK, hKnotQ⟩ :=
    exists_a3Block_of_not_le hC hM.charTwo hSQ hM.isSylowTwoOf hsolv_le hU hM' le_rfl
      (fun hle => hM.not_le_normalizer (hle.trans Subgroup.le_normalizer))
  obtain hKshort : IsShort2 K := hKblock.1.1
  have hQ1N_K : pCoreOf 2 G₁ ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    by_contra hnt
    let K' : Subgroup G := B6.conjSub t K
    have hK'block : IsChi0Block M K' :=
      CFSG.Quasithin.C126.isChi0Block_conjSub hM.isSylowTwoOf.1 hKblock ht
    have hne : K' ≠ K := by
      intro heq
      apply hnt
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmap : K' = K.map (MulAut.conj t).toMonoidHom := rfl
      exact hmap ▸ heq
    have hcomm : ⁅K, K'⁆ = ⊥ :=
      CFSG.Quasithin.distinctBlocksCommuteStatement M K K' hM.charTwo hKblock.1
        hK'block.1 hne.symm
    have hquotK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
      obtain ⟨α, hαsurj, hαker, -⟩ := hKalt
      have hcardAlt : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
      have e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 3) :=
        (QuotientGroup.quotientMulEquivOfEq hαker).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαsurj)
      exact (Nat.card_congr e.toEquiv).trans hcardAlt
    have h3dvdK : 3 ∣ Nat.card ↥K := by
      have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
      rw [hquotK] at hdec
      exact ⟨Nat.card ↥(CFSG.pCore 2 ↥K), hdec⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3dvdK
    obtain ⟨y, hyK, hyord⟩ : ∃ y ∈ K, orderOf y = 3 :=
      ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hxord⟩
    let z : G := t * y * t⁻¹
    have hzK' : z ∈ K' := by
      change z ∈ B6.conjSub t K
      rw [B6.mem_conjSub]
      have hconj : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [hconj]
      exact hyK
    have hzord : orderOf z = 3 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj t) y
      simpa [z, MulAut.conj_apply, hyord] using h
    have hz_y : z * y = y * z := by
      have hleC : K ≤ Subgroup.centralizer (K' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact Subgroup.mem_centralizer_iff.mp (hleC hyK) z hzK'
    have hzK : z ∈ K := by
      by_contra hzK
      have hinf : Subgroup.zpowers y ⊓ Subgroup.zpowers z = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        by_contra hw1
        have hw3 : orderOf w = 3 := by
          have hdvd : orderOf w ∣ 3 := by
            rw [← hyord]
            exact orderOf_dvd_of_mem_zpowers hw.1
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
          · exact absurd (orderOf_eq_one_iff.mp h1) hw1
          · exact h3
        have hEq : Subgroup.zpowers w = Subgroup.zpowers z := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw.2) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hw3, hzord]
        exact hzK ((Subgroup.zpowers_le.mpr hyK)
          ((Subgroup.zpowers_le.mpr hw.1) (hEq.symm ▸ Subgroup.mem_zpowers z)))
      have hcard9 : Nat.card ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers z) = 9 := by
        obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_zpowers_sup_zpowers
          (a := y) (b := z) (r := 3) (show Commute y z from hz_y.symm) hyord hzord hinf
        exact hcard
      have h9dvd : 9 ∣ Nat.card ↥M := by
        have hsub : Subgroup.zpowers y ⊔ Subgroup.zpowers z ≤ M := by
          refine sup_le (Subgroup.zpowers_le.mpr (hKblock.1.2.1 hyK)) ?_
          exact Subgroup.zpowers_le.mpr
            (M.mul_mem (M.mul_mem (hM.isSylowTwoOf.1 ht) (hKblock.1.2.1 hyK))
              (M.inv_mem (hM.isSylowTwoOf.1 ht)))
        have hdvd := Subgroup.card_dvd_of_le hsub
        rwa [hcard9] at hdvd
      have h9not : ¬ 9 ∣ Nat.card ↥M := by
        rw [ha]
        intro h9
        have hcop : Nat.Coprime 9 (2 ^ a) :=
          Nat.Coprime.pow_right a (by norm_num)
        have h31 : 9 ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using h9)
        norm_num at h31
      exact h9not h9dvd
    have hzcent : z ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hleC : K ≤ Subgroup.centralizer (K' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact (Subgroup.mem_centralizer_iff.mp (hleC hk) z hzK').symm
    have hsubQ : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      ext x
      simp [pCoreOf, Subgroup.mem_subgroupOf]
    have hrelK : (blockQ K).relIndex K = 3 := by
      change Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K) = 3
      rw [hsubQ]
      exact hquotK
    have hznotQ : z ∉ blockQ K := by
      intro hzQ
      change z ∈ pCoreOf 2 K at hzQ
      obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
      have hdvd : orderOf z ∣ 2 ^ m := by
        rw [← hm]
        exact Subgroup.orderOf_dvd_natCard _ hzQ
      rw [hzord] at hdvd
      have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
      have h31 : 3 ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
      norm_num at h31
    have hKsup : K ≤ blockQ K ⊔ Subgroup.zpowers z := by
      have hprime : ((blockQ K).relIndex K).Prime := by
        rw [hrelK]
        exact Nat.prime_three
      exact CFSG.GroupTheory.SmallFixedTwoGroup.le_of_relIndex_prime le_sup_left
        (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (Subgroup.zpowers_le.mpr hzK))
        hprime (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hznotQ
    have hKeq : K = blockQ K ⊔ Subgroup.zpowers z :=
      le_antisymm hKsup
        (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (Subgroup.zpowers_le.mpr hzK))
    have hNnormal : ((Subgroup.zpowers z).subgroupOf K).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hzk : (k : G) * z * (k : G)⁻¹ = z := by
        have hkz : (k : G) * z = z * (k : G) :=
          Subgroup.mem_centralizer_iff.mp hzcent (k : G) k.2
        calc (k : G) * z * (k : G)⁻¹ = z * (k : G) * (k : G)⁻¹ := by rw [hkz]
          _ = z := by group
      have hconj : (k : G) * (n : G) * (k : G)⁻¹ = z ^ j := by
        rw [← hj, ← conj_zpow, hzk]
      change (k : G) * (n : G) * (k : G)⁻¹ ∈ Subgroup.zpowers z
      rw [hconj]
      exact Subgroup.zpow_mem (Subgroup.zpowers z) (Subgroup.mem_zpowers z) j
    have hquot2 : IsPGroup 2 (↥K ⧸ (Subgroup.zpowers z).subgroupOf K) := by
      have hNcard : Nat.card ↥((Subgroup.zpowers z).subgroupOf K) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (Subgroup.zpowers_le.mpr hzK)).toEquiv, Nat.card_zpowers, hzord]
      have hKcard1 : Nat.card ↥K = 3 * Nat.card ↥(blockQ K) := by
        have h := Subgroup.relIndex_mul_card (H := blockQ K) (K := K)
        rw [show blockQ K ⊓ K = blockQ K from
          inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 K), hrelK] at h
        exact h.symm
      have hKcard2 : Nat.card ↥K =
          Nat.card (↥K ⧸ (Subgroup.zpowers z).subgroupOf K) * 3 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
          ((Subgroup.zpowers z).subgroupOf K)
        rwa [hNcard] at h
      have hcardQeq : Nat.card (↥K ⧸ (Subgroup.zpowers z).subgroupOf K) =
          Nat.card ↥(blockQ K) := by
        have h3 : Nat.card ↥(blockQ K) * 3 =
            Nat.card (↥K ⧸ (Subgroup.zpowers z).subgroupOf K) * 3 := by
          rw [mul_comm (Nat.card ↥(blockQ K)) 3, ← hKcard2, hKcard1]
        exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h3).symm
      obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
      exact IsPGroup.of_card (n := m) (by rw [hcardQeq]; simpa [blockQ] using hm)
    haveI : ((Subgroup.zpowers z).subgroupOf K).Normal := hNnormal
    have htop := hKshort.1 ((Subgroup.zpowers z).subgroupOf K) hquot2
    have hKleZ : K ≤ Subgroup.zpowers z := Subgroup.subgroupOf_eq_top.mp htop
    have hQbot : blockQ K = ⊥ := by
      have hle : blockQ K ≤ Subgroup.zpowers z :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKleZ
      have hcop : Nat.Coprime (Nat.card ↥(blockQ K)) (Nat.card ↥(Subgroup.zpowers z)) := by
        obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
        have hm' : Nat.card ↥(blockQ K) = 2 ^ m := by
          change Nat.card ↥(pCoreOf 2 K) = 2 ^ m
          exact hm
        rw [hm', Nat.card_zpowers, hzord]
        exact Nat.Coprime.pow_left m (by norm_num)
      have hdisj : blockQ K ⊓ Subgroup.zpowers z = ⊥ :=
        disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
      rw [eq_bot_iff]
      intro b hb
      have : b ∈ blockQ K ⊓ Subgroup.zpowers z := ⟨hb, hle hb⟩
      rw [hdisj] at this
      exact Subgroup.mem_bot.mp this
    have hUbot : blockU K = ⊥ := by
      rw [blockU, hQbot, Subgroup.commutator_bot_left]
    have hZbot : blockZ K = ⊥ := by
      rw [blockZ, hUbot]
      simp
    have hlt := hKshort.2.2.2.2.1
    rw [hZbot, hUbot] at hlt
    exact (lt_irrefl (⊥ : Subgroup G)) hlt
  have hKleM : K ≤ M := hKblock.1.2.1
  have hconjle : conjClosure K (pCoreOf 2 G₁) ≤ K := by
    refine CFSG.Quasithin.conjClosure_le ?_
    intro t ht z hz
    exact (Subgroup.mem_normalizer_iff.mp (hQ1N_K ht) z).mp hz
  have hMle : M ≤ K ⊔ pCoreOf 2 G₁ := by
    calc M = pCoreOf 2 G₁ ⊔ conjClosure K (pCoreOf 2 G₁) := hMK
      _ ≤ K ⊔ pCoreOf 2 G₁ := sup_le le_sup_right (hconjle.trans le_sup_left)
  have hKleO2 : K ≤ twoResidual M :=
    CFSG.Quasithin.C126.le_twoResidual_of_short hKleM hKshort
  have hO2leK : twoResidual M ≤ K :=
    CFSG.Quasithin.RonanE111.twoResidual_le_of_le_sup_two hQ1N_K hQ1_2 hMle
  have hKtwoRes : K = twoResidual M := le_antisymm hKleO2 hO2leK
  have hG2N_K : G₂ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKtwoRes]
    exact hM.le_normalizer.trans
      (CFSG.Quasithin.C126.A5.normalizer_le_normalizer_twoResidual M)
  have hKMsup : K ⊔ pCoreOf 2 G₁ = M := by
    refine le_antisymm (sup_le hKleM hM.isSylowTwoOf.1) ?_
    calc M = pCoreOf 2 G₁ ⊔ conjClosure K (pCoreOf 2 G₁) := hMK
      _ ≤ pCoreOf 2 G₁ ⊔ K := sup_le le_sup_left (hconjle.trans le_sup_right)
      _ = K ⊔ pCoreOf 2 G₁ := sup_comm _ _
  set D : Subgroup G := pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ with hD
  have hDM : pCoreOf 2 M = D := hM.pCoreOf_eq.trans hD.symm
  have hSyl : IsSylowTwoOf (pCoreOf 2 G₁) (K ⊔ pCoreOf 2 G₁) := by
    rw [hKMsup]
    exact hM.isSylowTwoOf
  have h113 := CFSG.Quasithin.H13.VolI.asC113c_holds G K (pCoreOf 2 G₁) hSyl hQ1N_K
    hKshort 3 (Or.inl rfl) hKalt
  obtain ⟨hD1, hD2, -, hAlt4, -, hCent⟩ := h113
  have hWU : blockQ K = blockU K :=
    CFSG.Quasithin.H13.VolI.blockQ_eq_blockU_of_alt3 hKshort hKalt
  have hWQ : blockU K = pCoreOf 2 K := by
    rw [← hWU]
    rfl
  have hZbot' : blockZ K = ⊥ :=
    CFSG.Quasithin.H13.VolI.blockZ_eq_bot_of_alt3 hKshort hKalt
  have hWleD : blockU K ≤ D := by
    rw [← hDM, ← hKMsup, hD1]
    exact le_sup_left
  have hDleCW : D ≤ Subgroup.centralizer (blockU K : Set G) := by
    rw [← hDM, ← hKMsup, hWQ]
    exact hCent
  have hW2 : IsPGroup 2 (blockU K) := by
    rw [hWQ]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hWab : IsMulCommutative ↥(blockU K) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxC : (x : G) ∈ Subgroup.centralizer (blockQ K : Set G) :=
      (hKshort.2.2.1.1 x.2).2
    have hyQ : (y : G) ∈ blockQ K := (hKshort.2.2.1.1 y.2).1
    exact ((Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyQ).symm
  have hWel : IsElemAbelian 2 (blockU K) := ⟨hWab, hKshort.2.2.1.2⟩
  have hG2N_W : G₂ ≤ Subgroup.normalizer (blockU K : Set G) := by
    rw [hWQ]
    exact hG2N_K.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKcard : Nat.card ↥K = 12 := by
    obtain ⟨e⟩ := hAlt4 rfl
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hquotK' : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    obtain ⟨α, hαsurj, hαker, -⟩ := hKalt
    have hcardAlt : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    have e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 3) :=
      (QuotientGroup.quotientMulEquivOfEq hαker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαsurj)
    exact (Nat.card_congr e.toEquiv).trans hcardAlt
  have h3dvdK' : 3 ∣ Nat.card ↥K := by
    have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [hquotK'] at hdec
    exact ⟨Nat.card ↥(CFSG.pCore 2 ↥K), hdec⟩
  have hWQcard : Nat.card ↥(blockU K) = Nat.card ↥(CFSG.pCore 2 ↥K) := by
    rw [hWQ]
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hWcard : Nat.card ↥(blockU K) = 4 := by
    have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [hquotK'] at hdec
    rw [hKcard] at hdec
    have hcore : Nat.card ↥(CFSG.pCore 2 ↥K) = 4 := by omega
    rw [hWQcard, hcore]
  have hWne : blockU K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(blockU K) = 1 := by rw [hbot]; simp
    rw [hWcard] at h1
    norm_num at h1
  obtain ⟨x', hx'ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3dvdK'
  obtain ⟨r, hrK, hrord⟩ : ∃ r ∈ K, orderOf r = 3 :=
    ⟨(x' : G), x'.2, by rw [Subgroup.orderOf_coe]; exact hx'ord⟩
  have hrG2 : r ∈ G₂ := hM.le (hKleM hrK)
  have hr_notG1 : r ∉ G₁ := by
    intro hrG1
    have hrQ1 : r ∈ pCoreOf 2 G₁ := by
      rw [← hM.inf_eq]
      exact ⟨hKleM hrK, hrG1⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁).exists_card_eq
    have hdvd : orderOf r ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard _ hrQ1
    rw [hrord] at hdvd
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have h31 : 3 ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    norm_num at h31
  have hsubQ : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
    ext x
    simp [pCoreOf, Subgroup.mem_subgroupOf]
  have hrelK' : (blockQ K).relIndex K = 3 := by
    change Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K) = 3
    rw [hsubQ]
    exact hquotK'
  have hKN_W : K ≤ Subgroup.normalizer (blockU K : Set G) := by
    rw [hWQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K
  have hrnotW : r ∉ blockU K := by
    intro hrW
    obtain ⟨m, hm⟩ := hW2.exists_card_eq
    have hdvd : orderOf r ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard _ hrW
    rw [hrord] at hdvd
    have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have h31 : 3 ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    norm_num at h31
  have hKWsup : K = blockU K ⊔ Subgroup.zpowers r := by
    have hrel : (blockU K).relIndex K = 3 := by
      rw [← hWU]
      exact hrelK'
    have hprime : ((blockU K).relIndex K).Prime := by
      rw [hrel]
      exact Nat.prime_three
    refine le_antisymm ?_ (sup_le (by rw [hWQ]; exact
      CFSG.LieType.BorelTits.pCoreOf_le 2 K) (Subgroup.zpowers_le.mpr hrK))
    exact CFSG.GroupTheory.SmallFixedTwoGroup.le_of_relIndex_prime le_sup_left
      (sup_le (by rw [hWQ]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K)
        (Subgroup.zpowers_le.mpr hrK))
      hprime (Subgroup.mem_sup_right (Subgroup.mem_zpowers r)) hrnotW
  have hC_Wr : blockU K ⊓ Subgroup.centralizer ({r} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwW : w ∈ blockU K := hw.1
    have hwr : w * r = r * w := by
      have := (Subgroup.mem_centralizer_iff.mp hw.2) r rfl
      exact this.symm
    have hwcent : w ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : k ∈ blockU K ⊔ Subgroup.zpowers r := by
        rw [← hKWsup]
        exact hk
      have hnorm : Subgroup.zpowers r ≤ Subgroup.normalizer (blockU K : Set G) :=
        (Subgroup.zpowers_le.mpr hrK).trans hKN_W
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hk'
      have hwa : w * a = a * w := by
        have := isMulCommutative_iff.mp hWab ⟨w, hwW⟩ ⟨a, ha⟩
        exact congrArg Subtype.val this
      have hwb : w * b = b * w := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← hj]
        exact (Commute.zpow_right hwr j).eq
      calc (a * b) * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [← hwb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [← hwa]
        _ = w * (a * b) := by group
    have hwZ : w ∈ blockZ K := ⟨hwW, hwcent⟩
    rw [hZbot'] at hwZ
    exact Subgroup.mem_bot.mp hwZ
  have hQ2C : pCoreOf 2 G₂ ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    let CW : Subgroup G := blockU K ⊓ Subgroup.centralizer ({q} : Set G)
    have hCWle : CW ≤ blockU K := inf_le_left
    have hWQ2 : blockU K ≤ pCoreOf 2 G₂ := hWleD.trans inf_le_right
    have hqN : q ∈ Subgroup.normalizer (blockU K : Set G) :=
      hG2N_W (CFSG.LieType.BorelTits.pCoreOf_le 2 G₂ hq)
    have hCW_ne_bot : CW ≠ ⊥ := by
      have hq2 : IsPGroup 2 (Subgroup.zpowers q) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₂).to_le
          (Subgroup.zpowers_le.mpr hq)
      have hqNzp : Subgroup.zpowers q ≤ Subgroup.normalizer (blockU K : Set G) :=
        Subgroup.zpowers_le.mpr hqN
      have hP2 : IsPGroup 2 ↥(blockU K ⊔ Subgroup.zpowers q) :=
        hW2.to_sup_of_normal_left' hq2 hqNzp
      have hPN : blockU K ⊔ Subgroup.zpowers q ≤
          Subgroup.normalizer (blockU K : Set G) :=
        sup_le Subgroup.le_normalizer hqNzp
      obtain ⟨x, hxW, hx1, hxcomm⟩ :=
        CFSG.GroupTheory.WielandtProduct.exists_mem_commute_of_le_of_isPGroup
          (p := 2) hP2 le_sup_left hPN hWne
      have hxC : x ∈ Subgroup.centralizer ({q} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyq : y = q := by simpa using hy
        rw [hyq]
        exact (hxcomm q (Subgroup.mem_sup_right (Subgroup.mem_zpowers q))).symm
      exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, ⟨hxW, hxC⟩⟩,
        fun h => hx1 (congrArg Subtype.val h)⟩
    have hCWtop : CW = blockU K := by
      by_contra hne
      have hdvd : Nat.card ↥CW ∣ 4 := by
        rw [← hWcard]
        exact Subgroup.card_dvd_of_le hCWle
      have hlt : Nat.card ↥CW < 4 := by
        have hcardlt : Nat.card ↥CW < Nat.card ↥(blockU K) := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hCWle) ?_
          intro hcard
          exact hne (Subgroup.eq_of_le_of_card_ge hCWle (le_of_eq hcard.symm))
        rwa [hWcard] at hcardlt
      haveI : Nontrivial ↥CW := by
        obtain ⟨x, hx, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hCW_ne_bot
        exact ⟨⟨⟨x, hx⟩, ⟨1, CW.one_mem⟩,
          fun h => hx1 (congrArg Subtype.val h)⟩⟩
      have hge2 : 2 ≤ Nat.card ↥CW := by
        have h1 : 1 < Nat.card ↥CW := Finite.one_lt_card
        omega
      set c : ℕ := Nat.card ↥CW with hcdef
      have hdvd' : c ∣ 4 := by rwa [hcdef]
      have hlt4 : c < 4 := by rwa [hcdef]
      have hge2' : 2 ≤ c := by rwa [hcdef]
      have hc2 : c = 2 := by
        have hle4 : c ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd'
        have hne3 : c ≠ 3 := by
          intro h3
          have : 3 ∣ 4 := by rw [h3] at hdvd'; exact hdvd'
          norm_num at this
        interval_cases c
        · rfl
        · exact absurd rfl hne3
      have hcardCW : Nat.card ↥CW = 2 := by
        rw [← hcdef]
        exact hc2
      have hrinv : ∀ y ∈ CW, r * y * r⁻¹ ∈ CW := by
        intro y hy
        have hyW : y ∈ blockU K := hy.1
        have hyC : y ∈ Subgroup.centralizer ({q} : Set G) := hy.2
        have hqy : q * y = y * q :=
          (Subgroup.mem_centralizer_iff.mp hyC) q rfl
        have hry : r * y * r⁻¹ ∈ blockU K :=
          (Subgroup.mem_normalizer_iff.mp (hKN_W hrK) y).mp hyW
        refine ⟨hry, ?_⟩
        change r * y * r⁻¹ ∈ Subgroup.centralizer ({q} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvq : v = q := by simpa using hv
        rw [hvq]
        set c : G := r * q * r⁻¹ * q⁻¹ with hcdef
        have hcW : c ∈ Subgroup.centralizer (blockU K : Set G) := by
          apply hDleCW
          rw [hD]
          exact hM.commutator_mem r (hKleM hrK) q hq
        have hqr : q * r = c⁻¹ * r * q := by
          have hcinv : c⁻¹ = q * r * q⁻¹ * r⁻¹ := by rw [hcdef]; group
          calc q * r = (q * r * q⁻¹ * r⁻¹) * (r * q) := by group
            _ = c⁻¹ * (r * q) := by rw [hcinv]
            _ = c⁻¹ * r * q := by group
        have hrq : r⁻¹ * q = (r⁻¹ * c⁻¹ * r) * q * r⁻¹ := by
          calc r⁻¹ * q = r⁻¹ * (q * r) * r⁻¹ := by group
            _ = r⁻¹ * (c⁻¹ * r * q) * r⁻¹ := by rw [hqr]
            _ = (r⁻¹ * c⁻¹ * r) * q * r⁻¹ := by group
        have hc'y : (r⁻¹ * c⁻¹ * r) * y = y * (r⁻¹ * c⁻¹ * r) := by
          have hcc : (r * y * r⁻¹) * c⁻¹ = c⁻¹ * (r * y * r⁻¹) :=
            Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hcW)
              (r * y * r⁻¹) hry
          calc r⁻¹ * c⁻¹ * r * y = r⁻¹ * c⁻¹ * (r * y * r⁻¹) * r := by group
            _ = r⁻¹ * ((r * y * r⁻¹) * c⁻¹) * r := by
              simpa [mul_assoc] using congrArg (fun t => r⁻¹ * t * r) hcc.symm
            _ = y * (r⁻¹ * c⁻¹ * r) := by group
        exact (calc (r * y * r⁻¹) * q = r * y * (r⁻¹ * q) := by group
          _ = r * y * ((r⁻¹ * c⁻¹ * r) * q * r⁻¹) := by rw [hrq]
          _ = r * (y * (r⁻¹ * c⁻¹ * r)) * q * r⁻¹ := by group
          _ = r * ((r⁻¹ * c⁻¹ * r) * y) * q * r⁻¹ := by rw [← hc'y]
          _ = (r * (r⁻¹ * c⁻¹ * r)) * y * q * r⁻¹ := by group
          _ = (c⁻¹ * r) * y * q * r⁻¹ := by
              rw [show r * (r⁻¹ * c⁻¹ * r) = c⁻¹ * r by group]
          _ = c⁻¹ * r * (y * q) * r⁻¹ := by group
          _ = c⁻¹ * r * (q * y) * r⁻¹ := by rw [← hqy]
          _ = (c⁻¹ * r * q) * y * r⁻¹ := by group
          _ = (q * r) * y * r⁻¹ := by rw [← hqr]
          _ = q * (r * y * r⁻¹) := by group).symm
      obtain ⟨x, hxCW, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hCW_ne_bot
      obtain ⟨z, hz1, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥CW)).mp hcardCW
      have hxeq : (⟨x, hxCW⟩ : ↥CW) = z :=
        hzuniq ⟨x, hxCW⟩ (fun h => hx1 (congrArg Subtype.val h))
      have hrinvx : r * x * r⁻¹ ∈ CW := hrinv x hxCW
      have hrxne : r * x * r⁻¹ ≠ 1 := by
        intro h1
        apply hx1
        calc x = r⁻¹ * (r * x * r⁻¹) * r := by group
          _ = 1 := by rw [h1]; group
      have hrxeq : (⟨r * x * r⁻¹, hrinvx⟩ : ↥CW) = z :=
        hzuniq _ (fun h => hrxne (congrArg Subtype.val h))
      have hfix : r * x * r⁻¹ = x := by
        exact (congrArg Subtype.val (hxeq.trans hrxeq.symm)).symm
      have hxr : r * x = x * r := by
        calc r * x = (r * x * r⁻¹) * r := by group
          _ = x * r := by rw [hfix]
      have hxC_r : x ∈ blockU K ⊓ Subgroup.centralizer ({r} : Set G) := by
        refine ⟨hxCW.1, ?_⟩
        change x ∈ Subgroup.centralizer ({r} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyr : y = r := by simpa using hy
        subst hyr
        exact hxr
      rw [hC_Wr] at hxC_r
      exact hx1 (Subgroup.mem_bot.mp hxC_r)
    have hwCW : w ∈ CW := by rw [hCWtop]; exact hw
    exact ((Subgroup.mem_centralizer_iff.mp hwCW.2) q rfl).symm
  have hnotQ1C : ¬ pCoreOf 2 G₁ ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro hle
    have hG2Ncent : G₂ ≤
        Subgroup.normalizer (Subgroup.centralizer (blockU K : Set G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro c
      constructor
      · intro hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro w hw
        have hgw : g⁻¹ * w * g ∈ blockU K := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ (hG2N_W hg)) w).mp hw
        have h1 : (g⁻¹ * w * g) * c = c * (g⁻¹ * w * g) := hc _ hgw
        calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * w := by group
      · intro hc
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro w hw
        have hgw : g * w * g⁻¹ ∈ blockU K :=
          (Subgroup.mem_normalizer_iff.mp (hG2N_W hg) w).mp hw
        have h1 : (g * w * g⁻¹) * (g * c * g⁻¹) =
            (g * c * g⁻¹) * (g * w * g⁻¹) := hc _ hgw
        have h2 := congrArg (fun t => g⁻¹ * t * g) h1
        simpa [mul_assoc] using h2
    have hconj : conjClosure (pCoreOf 2 G₁) G₂ ≤
        Subgroup.centralizer (blockU K : Set G) := by
      refine CFSG.Quasithin.conjClosure_le ?_
      intro t ht z hz
      exact (Subgroup.mem_normalizer_iff.mp (hG2Ncent ht) z).mp (hle hz)
    have hMcent : M ≤ Subgroup.centralizer (blockU K : Set G) :=
      hM.le_conjClosure.trans hconj
    have hrC : r ∈ Subgroup.centralizer (blockU K : Set G) :=
      hMcent (hKleM hrK)
    have hWle : blockU K ≤ Subgroup.centralizer ({r} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyr : y = r := by simpa using hy
      subst hyr
      exact ((Subgroup.mem_centralizer_iff.mp hrC) w hw).symm
    have hWbot : blockU K = ⊥ := by
      have hinf : blockU K ⊓ Subgroup.centralizer ({r} : Set G) = blockU K :=
        inf_eq_left.mpr hWle
      rw [hC_Wr] at hinf
      exact hinf.symm
    exact hWne hWbot
  have hDeq : D = blockU K ⊔
      (pCoreOf 2 G₁ ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hDM, ← hKMsup]
    exact hD1
  have hC_le_CW : (pCoreOf 2 G₁ ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.centralizer (blockU K : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwK : w ∈ K := by
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 K (by rwa [hWQ] at hw)
    exact Subgroup.mem_centralizer_iff.mp hc.2 w hwK
  have hCNW : (pCoreOf 2 G₁ ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.normalizer (blockU K : Set G) :=
    hC_le_CW.trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨blockU K, r, hWleD, hWel, hG2N_W, hQ2C, hnotQ1C, hrG2, hr_notG1, ?_, hWcard, hC_Wr⟩
  intro d hd
  rw [hDeq] at hd
  obtain ⟨w, hw, c, hc, hdc⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hCNW).mp hd
  have hrc : r * c * r⁻¹ = c := by
    have hcr : r * c = c * r := Subgroup.mem_centralizer_iff.mp hc.2 r hrK
    calc r * c * r⁻¹ = c * r * r⁻¹ := by rw [hcr]
      _ = c := by group
  have hdeq : r * d * r⁻¹ * d⁻¹ = r * w * r⁻¹ * w⁻¹ := by
    rw [hdc]
    calc r * (w * c) * r⁻¹ * (w * c)⁻¹ =
        (r * w * r⁻¹) * (r * c * r⁻¹) * (c⁻¹ * w⁻¹) := by group
      _ = (r * w * r⁻¹) * c * (c⁻¹ * w⁻¹) := by rw [hrc]
      _ = r * w * r⁻¹ * w⁻¹ := by group
  rw [hdeq]
  exact (blockU K).mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN_W hrK) w).mp hw)
    ((blockU K).inv_mem hw)


end CFSG.Quasithin.F112Crit.APrime

end
