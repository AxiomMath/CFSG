module

public import CFSG.RankThree.PartTwo.Sec4.Item48Proof
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Notation
import CFSG.RankThree.PartTwo.Sec4.Item45Closed
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXTools
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
import CFSG.RankThree.CentralLift.LinearTwoLifting

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G} {L : Subgroup G}

namespace Proof167Core

theorem commutator_le_normalizer_of_mem_thetaComponentsIn {M E V J : Subgroup G}
    (hE : ∀ K ∈ thetaComponentsIn M, E ≤ Subgroup.normalizer (K : Set G))
    (hV : V ≤ Subgroup.normalizer (M : Set G)) (hJ : J ∈ thetaComponentsIn M) :
    ⁅V, E⁆ ≤ Subgroup.normalizer (J : Set G) := by
  let K : Subgroup G :=
    ⨅ L : {L : Subgroup G // L ∈ thetaComponentsIn M}, Subgroup.normalizer (L : Set G)
  have hEK : ∀ e ∈ E, ∀ L : {L : Subgroup G // L ∈ thetaComponentsIn M},
      e ∈ Subgroup.normalizer (L : Set G) :=
    fun e he L => hE L.1 L.2 he
  have hconj : ∀ v ∈ V, ∀ e ∈ E, v * e * v⁻¹ ∈ K := by
    intro v hv e he
    change v * e * v⁻¹ ∈
      (⨅ L : {L : Subgroup G // L ∈ thetaComponentsIn M},
        Subgroup.normalizer (L : Set G))
    refine Subgroup.mem_iInf.mpr fun L => ?_
    have hLv : L.1.map (MulAut.conj v⁻¹).toMonoidHom ∈ thetaComponentsIn M :=
      Sec15.map_conj_mem_thetaComponentsIn (Subgroup.inv_mem _ (hV hv)) L.2
    have hx : e ∈ Subgroup.normalizer
        ((L.1.map (MulAut.conj v⁻¹).toMonoidHom : Subgroup G) : Set G) :=
      hEK e he ⟨_, hLv⟩
    have hmem : (MulAut.conj v) e ∈
        (Subgroup.normalizer
          ((L.1.map (MulAut.conj v⁻¹).toMonoidHom : Subgroup G) : Set G)).map
          (MulAut.conj v).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.map_equiv_normalizer_eq] at hmem
    have hLmap : (L.1.map (MulAut.conj v⁻¹).toMonoidHom : Subgroup G).map
        (MulAut.conj v).toMonoidHom = L.1 := by
      rw [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
    rw [hLmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  have heK : ∀ e ∈ E, e ∈ K := by
    intro e he
    change e ∈ (⨅ L : {L : Subgroup G // L ∈ thetaComponentsIn M},
      Subgroup.normalizer (L : Set G))
    exact Subgroup.mem_iInf.mpr (hEK e he)
  have hcomm : ⁅V, E⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr ?_
    intro v hv e he
    rw [commutatorElement_def]
    exact K.mul_mem (hconj v hv e he) (K.inv_mem (heK e he))
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    change x ∈ (⨅ L : {L : Subgroup G // L ∈ thetaComponentsIn M},
      Subgroup.normalizer (L : Set G)) at hx
    exact (Subgroup.mem_iInf.mp hx) ⟨J, hJ⟩
  exact hcomm.trans hKJ

theorem le_normalizer_of_eq_delta {N J Y₀ : Subgroup G}
    (hQJ : ∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (N : Set G) →
      A ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime (Nat.card Q) 3 →
        Q ≤ Subgroup.normalizer (J : Set G))
    (hY₀N : Y₀ ≤ Subgroup.normalizer (N : Set G))
    (hY₀delta : Y₀ = delta A LB Y₀) :
    Y₀ ≤ Subgroup.normalizer (J : Set G) := by
  rw [hY₀delta, delta]
  refine sSup_le ?_
  rintro Q ⟨hQ, hQY₀⟩
  have hQN : Q ≤ Subgroup.normalizer (N : Set G) := hQY₀.trans hY₀N
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ).2.1
  have hQ3 : Nat.Coprime (Nat.card Q) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp (mem_scriptQ_iff.mp hQ).1)).symm
  exact hQJ Q hQN hAQ hQ3

theorem le_normalizer_of_oPrimeResidualOf_eq_bot {N J Y : Subgroup G}
    (hQJ : ∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (N : Set G) →
      A ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime (Nat.card Q) 3 →
        Q ≤ Subgroup.normalizer (J : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : oPrimeResidualOf 3 Y = ⊥) :
    Y ≤ Subgroup.normalizer (J : Set G) :=
  hQJ Y hYN hAY
    (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (CFSG.RankThree.PartTwo.Sec14.not_three_dvd_of_oPrimeResidualOf_eq_bot hY3)).symm)

theorem le_of_mem_scriptY0_of_le {Y₀ J P : Subgroup G} (hY₀ : Y₀ ∈ scriptY0 A LB)
    (hYJ : Y₀ ≤ Subgroup.normalizer (J : Set G)) (hP : Group.IsPerfect P) (hP1 : P ≠ ⊥)
    (hPY : P ≤ Y₀) (hPJ : P ≤ J) : Y₀ ≤ J := by
  have hY₀res : oPrimeResidualOf 3 Y₀ = Y₀ := hY₀.1.2.1.symm
  have hquasi : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := hY₀.1.2.2.2
  let Y := ↥Y₀
  let W : Subgroup Y := CFSG.pCore 2 Y
  let M : Subgroup Y := (J ⊓ Y₀).subgroupOf Y₀
  have hMnorm : M.Normal := by
    have hinf : Y₀ ≤ Subgroup.normalizer ((J ⊓ Y₀ : Subgroup G) : Set G) :=
      (le_inf hYJ (Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hinf
  haveI : M.Normal := hMnorm
  have hmemM : ∀ x : Y, x ∈ M ↔ (x : G) ∈ J := by
    intro x
    change x ∈ (J ⊓ Y₀).subgroupOf Y₀ ↔ (x : G) ∈ J
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  let π : Y →* Y ⧸ W := QuotientGroup.mk' W
  let Mq : Subgroup (Y ⧸ W) := M.map π
  have hMqnorm : Mq.Normal := hMnorm.map π (QuotientGroup.mk'_surjective W)
  have hMqtop : Mq = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hquasi hMqnorm with h | h
    · exact h
    · exfalso
      let P' : Subgroup Y := P.subgroupOf Y₀
      have hP'perf : Group.IsPerfect P' := by
        have := hP
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hPY).symm.toMonoidHom)
          (MulEquiv.surjective _)
      have hP'M : P' ≤ M := by
        intro x hx
        change (x : G) ∈ P at hx
        exact (hmemM x).mpr (hPJ hx)
      have hPqcenter : P'.map π ≤ Subgroup.center (Y ⧸ W) :=
        (Subgroup.map_mono hP'M).trans h
      haveI : Group.IsPerfect P' := hP'perf
      have hδ : ∀ x : P', (π.comp P'.subtype) x ∈ Subgroup.center (Y ⧸ W) :=
        fun x => hPqcenter (Subgroup.mem_map_of_mem π x.2)
      have hδ1 : π.comp P'.subtype = 1 :=
        CFSG.RankThree.CentralLift.eq_one_of_isPerfect_of_mem_center _ hδ
      have hP'W : P' ≤ W := by
        intro x hx
        have hx1 : (QuotientGroup.mk' W) x = 1 := by
          have hx1' : (π.comp P'.subtype) ⟨x, hx⟩ = 1 := by rw [hδ1]; rfl
          simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using hx1'
        exact (QuotientGroup.ker_mk' W) ▸ (MonoidHom.mem_ker.mpr hx1)
      have hWp : IsPGroup 2 W := CFSG.pCore_isPGroup
      have hP'p : IsPGroup 2 P' := hWp.to_le hP'W
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hP'card : Nat.card P' = 1 :=
        CFSG.RankThree.PartTwo.Sec15.Proof152Gen.card_eq_one_of_isPerfect_of_isPGroup
          hP'perf hP'p
      have hP'bot : P' = ⊥ := Subgroup.eq_bot_of_card_eq P' hP'card
      have hPbot : P = ⊥ := by
        have hmap : (P.subgroupOf Y₀).map Y₀.subtype = ⊥ := by
          rw [show P.subgroupOf Y₀ = P' from rfl, hP'bot, Subgroup.map_bot]
        rwa [Subgroup.map_subgroupOf_eq_of_le hPY] at hmap
      exact hP1 hPbot
  have hMW : M ⊔ W = ⊤ := by
    have h1 : Mq.comap π = ⊤ := by rw [hMqtop]; simp
    change (M.map π).comap π = ⊤ at h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hres_le_M : CFSG.GH74.GLS.oPrimeResidual 3 Y ≤ M := by
    change Subgroup.closure {x : Y | ∃ k : ℕ, x ^ (3 ^ k) = 1} ≤ M
    refine (Subgroup.closure_le M).mpr ?_
    rintro x ⟨k, hxk⟩
    have hxMW : x ∈ M ⊔ W := by rw [hMW]; exact Subgroup.mem_top x
    obtain ⟨m, hm, w, hw, hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hxMW
    have hWp : IsPGroup 2 W := CFSG.pCore_isPGroup
    obtain ⟨l, hwl⟩ := hWp ⟨w, hw⟩
    have hwl' : w ^ 2 ^ l = 1 := by simpa using hwl
    have hconj : ∀ n : ℕ, ∃ m' ∈ M, (m * w) ^ n = m' * w ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, M.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨m', hm', hmn⟩ := ih
        refine ⟨m' * (w ^ n * m * (w ^ n)⁻¹), M.mul_mem hm'
          (hMnorm.conj_mem m hm (w ^ n)), ?_⟩
        rw [pow_succ, hmn, pow_succ]
        group
    have hpow : (m * w) ^ 2 ^ l ∈ M := by
      obtain ⟨m', hm', heq⟩ := hconj (2 ^ l)
      rw [heq, hwl', mul_one]
      exact hm'
    have hcop : Nat.Coprime (2 ^ l) (3 ^ k) :=
      Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)
    have hxk' : (m * w) ^ (3 ^ k) = 1 := by
      rw [hxeq]
      exact hxk
    have hxM : x ∈ M := by
      rw [← hxeq]
      exact CFSG.Quasithin.EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem hcop hpow
        (hxk'.symm ▸ M.one_mem)
    exact hxM
  intro y hy
  have hyres : y ∈ oPrimeResidualOf 3 Y₀ := by
    rw [hY₀res]
    exact hy
  rw [CFSG.GH74.GLS.oPrimeResidualOf] at hyres
  obtain ⟨x, hxres, hxmap⟩ := hyres
  have hxM : x ∈ M := hres_le_M hxres
  have hxJ : (x : G) ∈ J := (hmemM x).mp hxM
  exact hxmap ▸ hxJ

section Certified


theorem exists_thetaComponent
    (h : Sec14Std G A c L) {N : Subgroup G} (hN : N ≠ ⊤)
    (hAN : A ≤ N) (hLN : L ≤ N) :
    ∃ J ∈ thetaComponentsIn N, L ≤ J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
      ∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (N : Set G) →
        A ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime (Nat.card Q) 3 →
          Q ≤ Subgroup.normalizer (J : Set G) := by
  have h45 : Sec4.Item4_5 := Sec4.rank3II_4_5
  have h48 : Sec4.Item4_8 := Sec4.rank3II_4_8_of h45
  have hSF : SectionFourHyp N := TheoremFourHyp.sectionFourHyp h.toTheoremFourHyp hN
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hAcard : Nat.card A = 27 := by
    have hFE : partTwoF G = partTwoE G :=
      (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
    exact (hFE ▸ h.mem_partTwoF).2.1
  have hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n :=
    ⟨3, le_rfl, by rw [hAcard]; norm_num⟩
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h3 : Nat.card (Subgroup.zpowers (1 : G)) = 3 :=
      (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
    simpa using h3
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_lA.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hLmem : L ∈ thetaComponentsIn (N ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rw [mem_thetaComponentsIn_iff]
    refine ⟨le_inf hLN hLC, ?_⟩
    exact CFSG.RankThree.PartOne.subgroupOf_mem_thetaComponents_of_le
      Nat.prime_three (le_inf hLN hLC) inf_le_right (mem_thetaComponentsIn_iff.mp hLc).2
  obtain ⟨J, hJ, hLJ⟩ :=
    Sec6.exists_le_mem_thetaComponentsIn h48 hSF hAN hAel hAn hcA hc1 hLmem
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hSF hAN hAel hAn J hJ
  refine ⟨J, hJ, hLJ, hAJ, ?_⟩
  intro Q hQN hAQ hQ3
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hAel
  have hQ3' : ¬ 3 ∣ Nat.card Q :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQ3.symm
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A Q hA3 hQ3' hAQ
  have hcomm : ⁅Q, A⁆ ≤ Subgroup.normalizer (J : Set G) :=
    commutator_le_normalizer_of_mem_thetaComponentsIn (M := N) (E := A) (V := Q) (J := J)
      (Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hSF hAN hAel hAn)
      hQN hJ
  have hcent : Q ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (J : Set G) := by
    have hV_N : Q ⊓ Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (N : Set G) := inf_le_left.trans hQN
    have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rwa [hx])
    have hV_L : Q ⊓ Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (L : Set G) :=
      (inf_le_right.trans hCAc).trans (Proof1613.centralizer_le_normalizer_L h)
    have hLperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
    have hL1 : L ≠ ⊥ := by
      intro hLbot
      have h3 := Proof1613.three_dvd_card_L h
      rw [hLbot, Subgroup.card_bot] at h3
      norm_num at h3
    exact Sec15.le_normalizer_of_mem_thetaComponentsIn hV_N hJ hLJ hLperf hL1 hV_L
  rw [hfac]
  exact sup_le hcomm hcent


theorem exists_thetaComponent_of_scriptY0
    (h : Sec14Std G A c L) {N Y₀ : Subgroup G}
    (hN : N ≠ ⊤) (hAN : A ≤ N) (hLN : L ≤ N) (hY₀ : Y₀ ∈ scriptY0 A LB)
    (hLY₀ : L ≤ Y₀) (hY₀N : Y₀ ≤ Subgroup.normalizer (N : Set G)) :
    ∃ J ∈ thetaComponentsIn N, L ≤ J ∧ Y₀ ≤ J ∧
      A ≤ Subgroup.normalizer (J : Set G) ∧
        ∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (N : Set G) →
          A ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime (Nat.card Q) 3 →
            Q ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨J, hJ, hLJ, hAJ, hQJ⟩ := exists_thetaComponent h hN hAN hLN
  have hY₀NJ : Y₀ ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_eq_delta hQJ hY₀N hY₀.1.2.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_lA.1
  have hLperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hL1 : L ≠ ⊥ := by
    intro hLbot
    have h3 := Proof1613.three_dvd_card_L h
    rw [hLbot, Subgroup.card_bot] at h3
    norm_num at h3
  have hY₀J : Y₀ ≤ J := le_of_mem_scriptY0_of_le hY₀ hY₀NJ hLperf hL1 hLY₀ hLJ
  exact ⟨J, hJ, hLJ, hY₀J, hAJ, hQJ⟩

end Certified

end Proof167Core

end CFSG.RankThree.PartTwo.Sec16
