module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38Syl
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Four
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Lift
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Odd

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open scoped commutatorElement


theorem pair87UnitarySyl_of
    (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (hM : U38SylModel) (hP : U38P3Model) :
    Pair87UnitarySyl := by
  intro G _ _ A c L a b X n h hU Y hY hJY
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have hbA : b ∈ A := h.isGammaIndex.1
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAel.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAel.2 g g.2)⟩
  have hAcC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hc3 hc1 hAp hAcC L
      h.mem_thetaComponentsAt
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAL hcA
  obtain ⟨haN, hbN, ha3, hb3, hab, haL, hCa, hu4, hβ1, h7, hθodd⟩ := u38_pair_data h45 h hU
  have hac : a * c = c * a := hAc a haA c hcA
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) :=
    Item87Proof.le_centralizer_of_isElemAbelian hAel haA
  have hAfix : ∀ Z ∈ thetaComponentsAt 3 a, A ≤ Subgroup.normalizer (Z : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
      (hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG h.a_ne_one)) hAH hAel
      ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩
  set I : Subgroup G := sec8I L a with hI
  have hIdef : I = Subgroup.closure
      {y | y ∈ L ⊓ Subgroup.centralizer {a} ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
    simp only [hI, sec8I, hU, ↓reduceIte]
  have hIC : I ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := Item812Res7.sec8I_le L a
  have hcomm : ⁅L ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers b⁆ ≤
      Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.commutator_le]
    intro g hg β hβ
    have hβA : β ∈ A := (Subgroup.zpowers_le.mpr hbA) hβ
    exact Item89Res2.commutator_mem_normalizer (Subgroup.mem_inf.mp hg).2
      (fun Z hZ => hAfix Z hZ hβA) hY
  have hIN : I ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hIdef, Subgroup.closure_le]
    rintro t ⟨htL, ht2⟩
    exact hcomm (kF87UBComm_of h45 hM G A c L a b X n h hU t htL ht2)
  have hAI : A ≤ Subgroup.normalizer (I : Set G) := fun d hd =>
    Item812Res7.mem_normalizer_sec8I
      (CFSG.Goldschmidt.G310.le_normalizer_inf hAL (hAH.trans Subgroup.le_normalizer) hd)
  obtain ⟨T, hTα, hT8, hTβ, hTc⟩ := hM (L ⧸ aschbacherSolvableCore 3 L) hU
    (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) (thetaQuotMulAut L (compAction L ⟨b, hbN⟩))
    (u38_pow_eq_one haN ha3) (u38_pow_eq_one hbN hb3) (u38_mul_comm haN hbN hab)
    (by obtain ⟨hx, hnot⟩ := haL; exact fun hin => hnot hin)
    (by rw [← barCentralizer_eq_u38Fix haN]; exact hCa)
    (by
      obtain ⟨u, hu, h4, h2⟩ := hu4
      exact ⟨u, by rwa [barCentralizer_eq_u38Fix haN] at hu, h4, h2⟩)
    hβ1 (by rw [← barCentralizer_eq_u38Fix hbN]; exact h7)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_of_mem_thetaComponentsIn h.mem_thetaComponentsAt
  have hcc : compAction L ⟨c, hcN⟩ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp (hLc x.2)
    show c * (x : G) * c⁻¹ = (x : G)
    rw [← this, mul_inv_cancel_right]
  have hcL : thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1 := by rw [hcc, map_one]
  have hBA : Subgroup.closure ({b, c} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hbA, hcA]
  obtain ⟨Q, hQC, hQ2, hQ8, hBQ, hQb⟩ := exists_B0_syl haN hbN hcN ha3
    (hAel.2 b hbA) hc3 hab hac hcL (hAp.to_le hBA) hθodd T
    (by rw [barCentralizer_eq_u38Fix haN]; exact hTα) hT8 hCa hTβ hTc
  have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := hQC.trans inf_le_right
  have hQB : Q ≤ ⁅Q, Subgroup.closure ({b, c} : Set G)⁆ :=
    calc Q = ⁅Q, Subgroup.zpowers b⁆ := hQb.symm
      _ ≤ ⁅Q, Subgroup.closure ({b, c} : Set G)⁆ :=
        Subgroup.commutator_mono le_rfl
          (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hBF : ∀ L' ∈ thetaComponentsAt 3 a,
      Subgroup.closure ({b, c} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
    fun L' hL' => hBA.trans (hAfix L' hL')
  have hQYC : Q ≤ Y ⊔ Sec4.thetaQuotCentralizer Y :=
    u38_four_nine h49 hG (hAp.to_le hBA) ha3 h.a_ne_one hBF (hBA.trans hAH) hY hQ2 hQa hBQ hQB
  have hQI : Q ≤ I := by
    intro q hq
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    rw [hIdef]
    exact Subgroup.subset_closure ⟨hQC hq, k, by simpa using congrArg Subtype.val hk⟩
  have hQ8' : Nat.card (Q.subgroupOf I) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQI).toEquiv]
    exact hQ8
  have hdvd8 : 2 ^ 3 ∣ Nat.card I := by
    have := Subgroup.card_dvd_of_le hQI
    rw [hQ8] at this
    simpa using this
  have hv3 : 3 ≤ (Nat.card I).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd8
  have hv : (Nat.card I).factorization 2 ≤ 3 := by
    obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 I))
    have h1 : Nat.card P₀ = 2 ^ (Nat.card I).factorization 2 := Sylow.card_eq_multiplicity P₀
    have h2 : Nat.card ((P₀ : Subgroup I).map I.subtype) ≤ 8 :=
      card_le_eight_of_isPGroup haN ha3 hθodd hCa (P₀.isPGroup'.map I.subtype)
        ((Subgroup.map_subtype_le _).trans hIC)
    have h3 : Nat.card (P₀ : Subgroup I) ≤ 8 :=
      (Subgroup.card_map_of_injective I.subtype_injective).symm.le.trans h2
    have h4 : 2 ^ (Nat.card I).factorization 2 ≤ 8 := h1 ▸ h3
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ≤ 2 ^ (Nat.card I).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hS8 : Nat.card (Q.subgroupOf I) = 2 ^ (Nat.card I).factorization 2 := by
    rw [hQ8', le_antisymm hv hv3]
    norm_num
  let T₂ : Sylow 2 I := Sylow.ofCard (Q.subgroupOf I) hS8
  have hIN' : I ≤ Subgroup.normalizer
      ((Y ⊔ Sec4.thetaQuotCentralizer Y : Subgroup G) : Set G) :=
    Sec6.le_normalizer_sup_of_conj
      (fun g hg z hz => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hIN hg) z).mp hz))
      (fun g hg z hz => Subgroup.mem_sup_right (Sec6.conj_mem_thetaQuotCentralizer hz (hIN hg)))
  have hT₂ : (T₂ : Subgroup I).map I.subtype ≤ Y ⊔ Sec4.thetaQuotCentralizer Y := by
    show (Q.subgroupOf I).map I.subtype ≤ _
    rw [Subgroup.map_subgroupOf_eq_of_le hQI]
    exact hQYC
  have hgen2 : ∀ t ∈ I, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ∈ Y ⊔ Sec4.thetaQuotCentralizer Y :=
    fun t htI ht2 => Item89Res2.mem_of_sylow_le hIN' T₂ hT₂ htI ht2
  have hIYC : I ≤ Y ⊔ Sec4.thetaQuotCentralizer Y := by
    rw [hIdef, Subgroup.closure_le]
    rintro t ⟨htL, ht2⟩
    have htI : t ∈ I := by
      rw [hIdef]
      exact Subgroup.subset_closure ⟨htL, ht2⟩
    exact hgen2 t htI ht2
  have hS3 := mem_of_three_pow_mem (u38_three_elt_mem h45 hP h hU hJY hIN)
  obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 I))
  refine ⟨T₀, ?_⟩
  rintro t ⟨s, hs, rfl⟩
  obtain ⟨k, hk⟩ := T₀.isPGroup' ⟨s, hs⟩
  exact u38_two_elt_mem hG.localRank_three.le hAel h.card_eq (hAfix Y hY) hAI hIN hIYC hS3 s.2
    ⟨k, by simpa using congrArg Subtype.val (congrArg Subtype.val hk)⟩

end CFSG.RankThree.PartTwo.Sec8
