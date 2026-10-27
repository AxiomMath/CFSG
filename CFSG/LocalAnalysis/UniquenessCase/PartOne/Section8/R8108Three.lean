module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.GammaRThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CyclicNormalizerThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerPSubQ108Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four R8_108)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_inf_sup_eq_bot (D : Data G) (h69 : UC6.R6_9 D)
    (hsub : D.sig ⊆ D.sig1) (hm3 : CFSG.Open.pRank 3 D.M ≤ 3) {P R R' : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (hT : TwoExtraThree P R R')
    (hΓE : ∀ E : Subgroup G, R ⊓ R' ≤ E → E ≤ R ⊔ R' → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → CFSG.Open.rankThreeGamma 1 3 E ≤ D.M)
    {A : Subgroup G} (hAP : A ≤ P) (hA3 : Nat.card A = 3) (hAQ : A ⊓ (R ⊔ R') = ⊥) :
    Subgroup.centralizer (A : Set G) ≤ D.M := by
  classical
  have hZeq : (Subgroup.center ↥R).map R.subtype = (Subgroup.center ↥R').map R'.subtype :=
    hT.cen.symm.trans hT.cen'
  obtain ⟨B, E, hBle, hBea, hBcard, hZleB, hEleB, hEea, hEcard, hEcent, hAZ_comm, hABZ⟩ :=
    exists_elemAbelian_27_and_nine_le_centralizer_of_two_extraspecial_order_three
      hT.extra hT.extra' hT.card hT.card' hT.exp hT.exp' hT.comm hZeq hA3
      (hAP.trans hT.norm) (hAP.trans hT.norm')
  set Z : Subgroup G := (Subgroup.center ↥R).map R.subtype with hZdef
  have hZinf : Z = R ⊓ R' := hT.cen.symm
  have hQM : R ⊔ R' ≤ D.M := hT.le.trans hP.le
  have hEQ : E ≤ R ⊔ R' := hEleB.trans hBle
  have hEM : E ≤ D.M := hEQ.trans hQM
  have hAinfB : A ⊓ B = ⊥ := by
    apply le_antisymm _ bot_le
    calc A ⊓ B ≤ A ⊓ (R ⊔ R') := inf_le_inf le_rfl hBle
      _ = ⊥ := hAQ
  have hP0M : A ⊔ B ≤ D.M := sup_le (hAP.trans hP.le) (hBle.trans hQM)
  have hP0p : IsPGroup 3 (A ⊔ B : Subgroup G) :=
    hP.isPGroup.to_le (sup_le hAP (hBle.trans hT.le))
  have hBabel : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hBea.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hZcard : Nat.card Z = 3 := by rw [hZinf]; exact hT.card_inf
  by_contra hCnot
  have hN : ¬ Subgroup.normalizer (A : Set G) ≤ D.M := fun hNle =>
    hCnot ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNle)
  have hAB_comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    by_cases hZE : Z ≤ E
    ·
      have hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
        hΓE E (hZinf ▸ hZE) hEQ hEea hEcard
      have hE_norm : E ≤ Subgroup.normalizer (A : Set G) :=
        hEcent.trans (Subgroup.centralizer_le_normalizer (A : Set G))
      have hstep := h69 hsub 3 Nat.prime_three (by norm_num) E hEM hEea
        (by rw [hEcard]; norm_num) hΓ 3 A Nat.prime_three (hAP.trans hP.le) hA3
        hE_norm hN (A ⊔ B) hP0M hP0p le_sup_left
      have hcomm69 : ∀ y ∈ (Subgroup.upperCentralSeries ↥(A ⊔ B) 2).map (A ⊔ B).subtype,
          ∀ x ∈ A, x * y = y * x := hstep.2.1
      have hANB : A ≤ Subgroup.normalizer (B : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro a ha b hb
        have h1 : a * b * a⁻¹ = ⁅a, b⁆ * b := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact B.mul_mem (hZleB (hABZ a ha b hb)) hb
      have hZcentral : ∀ z ∈ Z, ∀ y ∈ A ⊔ B, z * y = y * z := by
        intro z hz y hy
        obtain ⟨a, ha, b, hb, hxy⟩ := CFSG.Walter.mem_sup_of_le_normalizer hANB hy
        rw [← hxy]
        have hzB : z ∈ B := hZleB hz
        calc z * (a * b) = (z * a) * b := by group
          _ = (a * z) * b := by rw [(hAZ_comm a ha z hz).symm]
          _ = a * (z * b) := by group
          _ = a * (b * z) := by rw [hBabel z hzB b hb]
          _ = (a * b) * z := by group
      have hcenter_Z : Z.subgroupOf (A ⊔ B) ≤ Subgroup.center ↥(A ⊔ B) := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (hZcentral (z : G) (Subgroup.mem_subgroupOf.mp hz) (y : G) y.2).symm
      have hbZ : ∀ b ∈ B, ∀ y ∈ A ⊔ B, ⁅b, y⁆ ∈ Z := by
        intro b hb y hy
        obtain ⟨a, ha, b', hb', hxy⟩ := CFSG.Walter.mem_sup_of_le_normalizer hANB hy
        rw [← hxy]
        have hbb' : ⁅b, b'⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact hBabel b hb b' hb'
        have h1 : ⁅b, a * b'⁆ = ⁅b, a⁆ := by
          rw [commutatorElement_mul_right_eq_mul_conj, hbb']
          group
        rw [h1, (commutatorElement_inv a b).symm]
        exact Z.inv_mem (hABZ a ha b hb)
      have hB_up : ∀ (b : G) (hb : b ∈ B), (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(A ⊔ B)) ∈
          Subgroup.upperCentralSeries ↥(A ⊔ B) 2 := by
        intro b hb
        rw [show (2 : ℕ) = 1 + 1 by norm_num, Subgroup.mem_upperCentralSeries_succ_iff]
        intro y
        rw [Subgroup.upperCentralSeries_one]
        apply hcenter_Z
        rw [Subgroup.mem_subgroupOf]
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using
          hbZ b hb (y : G) y.2
      intro a ha b hb
      exact hcomm69 b (Subgroup.mem_map.mpr ⟨⟨b, Subgroup.mem_sup_right hb⟩, hB_up b hb, rfl⟩)
        a ha
    ·
      have hZEbot : Z ⊓ E = ⊥ := by
        have hdvd : Nat.card ↥(Z ⊓ E) ∣ 3 := hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact Subgroup.eq_bot_of_card_eq _ h
        · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hZcard])).symm.le.trans
            inf_le_right) hZE
      have hZEcomm : ∀ a ∈ Z, ∀ b ∈ E, a * b = b * a :=
        fun a ha b hb => hBabel a (hZleB ha) b (hEleB hb)
      have hcardZE : Nat.card ↥(Z ⊔ E) = 27 := by
        have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hZEcomm
        rw [hZEbot, Subgroup.card_bot, hZcard, hEcard] at h
        omega
      have hBeq : Z ⊔ E = B :=
        Subgroup.eq_of_le_of_card_ge (sup_le hZleB hEleB) (by rw [hcardZE, hBcard])
      have hBC : B ≤ Subgroup.centralizer (A : Set G) := by
        rw [← hBeq]
        refine sup_le ?_ hEcent
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact hAZ_comm a ha z hz
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hBC hb) a ha)
  have hAea : CFSG.Open.IsElemAbelian 3 A := by
    refine ⟨(isCyclic_of_card_dvd_prime (p := 3) (by rw [hA3])).isMulCommutative, ?_⟩
    intro x hx
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨x, hx⟩)
    simpa [hA3] using congrArg Subtype.val h
  have hcardAUB : Nat.card ↥(A ⊔ B) = 81 := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := A) (B := B) hAB_comm
    rw [hAinfB, Subgroup.card_bot, hA3, hBcard] at h
    omega
  have hP0ea : CFSG.Open.IsElemAbelian 3 (A ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAea hBea hAB_comm
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.le_pRank (p := 3) (H := D.M) (k := 4)
      (by norm_num) hP0M hP0ea (by rw [hcardAUB]; norm_num)
  omega

theorem centralizer_le_of_mem_of_cyclic {M P Q : Subgroup G}
    (hY : ∀ Y : Subgroup G, Y ≤ Q → Nat.card Y = 3 → Subgroup.normalizer (Y : Set G) ≤ M)
    (hA : ∀ A : Subgroup G, A ≤ P → Nat.card A = 3 → A ⊓ Q = ⊥ →
      Subgroup.centralizer (A : Set G) ≤ M)
    {x : G} (hxP : x ∈ P) (hx : orderOf x = 3) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  let A : Subgroup G := Subgroup.zpowers x
  have hAcard : Nat.card A = 3 := by
    show Nat.card (Subgroup.zpowers x) = 3
    rw [Nat.card_zpowers, hx]
  have hcent : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer (A : Set G) := by
    show Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  by_cases hxQ : x ∈ Q
  · exact (Subgroup.centralizer_le_normalizer (A : Set G)).trans
      (hY A (Subgroup.zpowers_le.mpr hxQ) hAcard)
  · have hAP : A ≤ P := Subgroup.zpowers_le.mpr hxP
    have hAQ : A ⊓ Q = ⊥ := by
      have hdvd : Nat.card (A ⊓ Q : Subgroup G) ∣ 3 := by
        rw [← hAcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq (A ⊓ Q) h
      · exfalso
        have hE : A ⊓ Q = A :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hAcard])
        have hxAQ : x ∈ A ⊓ Q := by
          rw [hE]
          exact Subgroup.mem_zpowers x
        exact hxQ hxAQ.2
    exact hA A hAP hAcard hAQ

theorem r8_108_of_data
    (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D)
    (h76 : ∀ p ∈ D.sig, p ≠ 3 → IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (hm3 : ¬ IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 D.M ≤ 3) :
    R8_108 D := by
  classical
  intro L hL hSL hL'
  obtain ⟨L', hL'ne, hset⟩ := hL'
  by_contra hnot
  have hm3' := hm3 hnot
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hnot (UC6S846.sp_of_mem_sig hSg hns hp)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) D.M
  have hT : TwoExtraThree P (P ⊓ L) (P ⊓ L') :=
    twoExtraThree_of_isSL3Four hL hset hL'ne.symm hSL hP hm3'
  have hc2 : (conjSetOf D.M L).ncard ≤ 2 := by
    rw [hset, Set.ncard_pair hL'ne.symm]
  have hR : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hP hL.1.le
      hL.1.subgroupOf
  have hΓR : CFSG.Open.rankThreeGamma 1 3 (P ⊓ L) ≤ D.M :=
    rankThreeGamma_le_of_isSL3Four_of_mem_sig D hSg h76 hp hp3 hL hc2 hSL hR
  obtain ⟨E₀, -, hE₀R, hE₀el, hE₀9⟩ :=
    exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hT.extra hT.exp (P ⊓ L).one_mem
  have hNP : Subgroup.normalizer (P : Set G) ≤ D.M :=
    normalizer_sylow_le_of_r6_3 D h63 hP.le (hE₀R.trans inf_le_left) hE₀el hE₀9
      ((CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hE₀R).trans hΓR)
  have hsub : D.sig ⊆ D.sig1 := UC6S846.sig_subset_sig1 hSg hns
  have hY : ∀ Y : Subgroup G, Y ≤ (P ⊓ L) ⊔ (P ⊓ L') → Nat.card Y = 3 →
      Subgroup.normalizer (Y : Set G) ≤ D.M := fun Y hYQ hY3 =>
    normalizer_le_of_le_sup_of_card_three D h69 hsub hP.le hP.isPGroup hT hΓR hYQ hY3
  have hΓE : ∀ E : Subgroup G, (P ⊓ L) ⊓ (P ⊓ L') ≤ E → E ≤ (P ⊓ L) ⊔ (P ⊓ L') →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
    fun E hZE hEQ hEel hE9 => rankThreeGamma_le_of_inf_le hP hT hNP hY hZE hEQ hEel hE9
  have hA : ∀ A : Subgroup G, A ≤ P → Nat.card A = 3 → A ⊓ ((P ⊓ L) ⊔ (P ⊓ L')) = ⊥ →
      Subgroup.centralizer (A : Set G) ≤ D.M := fun A hAP hA3 hAQ =>
    centralizer_le_of_inf_sup_eq_bot D h69 hsub hm3' hP hT hΓE hAP hA3 hAQ
  have hMtop : D.M ≠ ⊤ := by
    have : IsSimpleGroup G := D.standing.simple
    exact CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab D.M
      D.maxLocal.1
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : P ⊓ L = ⊥ := by rw [hbot, bot_inf_eq]
    have h27 := hT.card
    rw [h1, Subgroup.card_bot] at h27
    omega
  exact hnot (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le hMtop hP hPne
    hNP fun x hxP hx => centralizer_le_of_mem_of_cyclic hY hA hxP hx)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r8_108_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (hK : UCK.K36)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (S : Setup G) :
    Inputs1719.PartOne.R8_108 (dataOfSetup hS S) :=
  PartOne.Section8.r8_108_of_data (dataOfSetup hS S)
    (UC6S846.sigmaStd_dataOfSetup hS S) (r6_3_dataOfSetup hS hUC hC S)
    (r6_9_dataOfSetup hS hUC hC hK S)
    (fun p hp hp3 hsp => conclusion76_dataOfSetup_of_five_le hSE hS hUC hC S
      ((dataOfSetup hS S).sig_prime p hp).1
      (((dataOfSetup hS S).sig_prime p hp).1.five_le_of_ne_two_of_ne_three
        ((dataOfSetup hS S).sig_prime p hp).2 hp3) hsp)
    (fun _ => (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) (dataOfSetup hS S).M (dataOfSetup hS S).maxLocal.1).trans hS.rank.le)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
