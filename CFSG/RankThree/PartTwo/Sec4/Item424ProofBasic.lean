module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item424Proof

variable {G : Type} [Group G]

theorem eq_one_of_pow_three_of_not_dvd {H : Subgroup G} (h3 : ¬ 3 ∣ Nat.card H) {x : G}
    (hx : x ∈ H) (hx3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) h3

theorem three_dvd_card_of_isType424 {X : Type} [Group X] (hX : Sec11.IsType424 X) :
    3 ∣ Nat.card X := by
  rcases hX with ⟨n, -, ⟨e⟩⟩ | ⟨p, n, hp, -, -, ⟨e⟩⟩ | ⟨n, hn, h⟩
  · rw [Nat.card_congr (e.trans (projSLEquivPSL _)).toEquiv]
    exact KFacts.three_dvd_card_psl2 _
  · rw [Nat.card_congr (e.trans (projSLEquivPSL _)).toEquiv]
    exact KFacts.three_dvd_card_psl2 _
  · exact KFacts.three_dvd_card_of_isoLThreeMinusPi_of_ne_zero (by omega) h

theorem not_three_dvd_card_theta [Finite G] (K : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
  (Sec6.theta_solvable_and_not_dvd K).2

theorem eq_one_of_mem_of_commute [Finite G] {K : Subgroup G}
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) {z : G} (hzK : z ∈ K)
    (hz : ∀ k ∈ K, z * k = k * z) (hz3 : z ^ 3 = 1) : z = 1 := by
  have hmem : ((⟨z, hzK⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hz y y.2).symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact eq_one_of_pow_three_of_not_dvd (not_three_dvd_card_theta K) ⟨_, hmem, rfl⟩ hz3

theorem isQuasisimple_of_mem_thetaComponentsIn [Finite G] {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e := Subgroup.subgroupOfEquivOfLe hKM
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
      Nat.prime_three e)) hK'.2.2

theorem card_closure_pair_eq_nine {A : Subgroup G} [Finite G]
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {y z : G} (hyA : y ∈ A)
    (hzA : z ∈ A) (hy1 : y ≠ 1) (hzy : z ∉ Subgroup.zpowers y) :
    Nat.card (Subgroup.closure ({y, z} : Set G)) = 9 := by
  have hcomm : y * z = z * y := congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hyA⟩ ⟨z, hzA⟩)
  have hle : Nat.card (Subgroup.closure ({y, z} : Set G)) ≤ 9 := by
    rw [Set.pair_comm]
    exact Sec10.card_closure_pair_le hcomm.symm (hA.2 z hzA) (hA.2 y hyA)
  have hBA : Subgroup.closure ({y, z} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hyA
    · exact hzA
  have hdvd : Nat.card (Subgroup.closure ({y, z} : Set G)) ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hBA
  have hy3 : orderOf y = 3 := orderOf_eq_prime (hA.2 y hyA) hy1
  have h3 : 3 ∣ Nat.card (Subgroup.closure ({y, z} : Set G)) := by
    rw [← hy3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hne : Nat.card (Subgroup.closure ({y, z} : Set G)) ≠ 3 := by
    intro h
    apply hzy
    have heq : Subgroup.zpowers y = Subgroup.closure ({y, z} : Set G) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
        (by rw [h, Nat.card_zpowers, hy3])
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  have : Nat.card (Subgroup.closure ({y, z} : Set G)) ∈ Nat.divisors 27 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [hd] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem eq_closure_triple {A : Subgroup G} [Finite G] (h27 : Nat.card A = 27) {y z w : G}
    (hyA : y ∈ A) (hzA : z ∈ A) (hwA : w ∈ A)
    (h9 : Nat.card (Subgroup.closure ({y, z} : Set G)) = 9)
    (hw : w ∉ Subgroup.closure ({y, z} : Set G)) : A = Subgroup.closure {y, z, w} := by
  have hTA : Subgroup.closure ({y, z, w} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hyA
    · exact hzA
    · exact hwA
  have hBT : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.closure {y, z, w} :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have hdvd : Nat.card (Subgroup.closure ({y, z, w} : Set G)) ∣ 27 :=
    h27 ▸ Subgroup.card_dvd_of_le hTA
  have h9d : 9 ∣ Nat.card (Subgroup.closure ({y, z, w} : Set G)) := h9 ▸ Subgroup.card_dvd_of_le hBT
  have hne : Nat.card (Subgroup.closure ({y, z, w} : Set G)) ≠ 9 := by
    intro h
    apply hw
    have heq := Subgroup.eq_of_le_of_card_ge hBT (by rw [h, h9])
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  have hT : Nat.card (Subgroup.closure ({y, z, w} : Set G)) = 27 := by
    have : Nat.card (Subgroup.closure ({y, z, w} : Set G)) ∈ Nat.divisors 27 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hTA (by rw [hT, h27])).symm

end Item424Proof

open Item424Proof

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

theorem isElemAbelian (h : Config424 G A L a c K) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.maximal.prop

theorem pow_three (h : Config424 G A L a c K) : ∀ x ∈ A, x ^ 3 = 1 :=
  h.isElemAbelian.2

theorem comm (h : Config424 G A L a c K) : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isPGroup (h : Config424 G A L a c K) : IsPGroup 3 A :=
  Sec5.isPGroup_of_isElemAbelian h.isElemAbelian

theorem a_mem (h : Config424 G A L a c K) : a ∈ A := by
  have ha : a ∈ (Subgroup.zpowers a : Set G) := Subgroup.mem_zpowers a
  rw [← h.sectionCentralizer_eq] at ha
  exact ha.1

theorem a_ne_one (h : Config424 G A L a c K) : a ≠ 1 := by
  intro h1
  have := h.orderOf_a
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem c_ne_one (h : Config424 G A L a c K) : c ≠ 1 := fun h1 =>
  h.c_not_mem (h1 ▸ Subgroup.one_mem _)

theorem orderOf_c (h : Config424 G A L a c K) : orderOf c = 3 :=
  orderOf_eq_prime (h.pow_three c h.c_mem) h.c_ne_one

theorem a_comm (h : Config424 G A L a c K) (x : G) : x * a = a * x :=
  Subgroup.mem_center_iff.mp h.a_mem_center x

theorem isQuasisimple_L (h : Config424 G A L a c K) :
    IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
  h.mem_thetaComponents.2.2

theorem inf_thetaQuotCentralizer (h : Config424 G A L a c K)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    A ⊓ thetaQuotCentralizer L = Subgroup.zpowers a := by
  have hsc := h.sectionCentralizer_eq
  rw [Sec13.sectionCentralizer_eq_inf hAN] at hsc
  exact SetLike.coe_injective hsc

theorem le_normalizer (h45 : Item4_5) (h : Config424 G A L a c K) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  h45 G h.sectionFourHyp A h.isPGroup
    (Or.inr ⟨h.isElemAbelian, 3, le_rfl, by rw [h.card_eq]; norm_num⟩) L h.mem_thetaComponents

theorem le_centralizer_c (h : Config424 G A L a c K) :
    A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm x hx c h.c_mem)

theorem K_le (h : Config424 G A L a c K) : K ≤ L ⊓ Subgroup.centralizer ({c} : Set G) :=
  (mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn).1

theorem K_le_L (h : Config424 G A L a c K) : K ≤ L := h.K_le.trans inf_le_left

theorem commute_c_of_mem_K (h : Config424 G A L a c K) {k : G} (hk : k ∈ K) : k * c = c * k :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.K_le hk).2

theorem isPerfect_K (h : Config424 G A L a c K) : Group.IsPerfect K :=
  isPerfect_of_mem_thetaComponentsIn h.mem_thetaComponentsIn

theorem isQuasisimple_K (h : Config424 G A L a c K) :
    IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
  isQuasisimple_of_mem_thetaComponentsIn h.mem_thetaComponentsIn

theorem mem_thetaComponentsIn_centralizer (h : Config424 G A L a c K) :
    K ∈ thetaComponentsIn (Subgroup.centralizer ({c} : Set G)) := by
  set N := Subgroup.centralizer ({c} : Set G) with hN
  set M := L ⊓ N with hM
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsIn
  have hMN : M ≤ N := inf_le_right
  have hKN : K ≤ N := hKM.trans hMN
  have hMsn : (M.subgroupOf N).IsSubnormal := by
    have heq : M.subgroupOf N = L.subgroupOf N := by
      ext x
      simp only [Subgroup.mem_subgroupOf, hM, Subgroup.mem_inf]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [heq]
    exact h.mem_thetaComponents.2.1.subgroupOf
  have hKsn : ((K.subgroupOf N).subgroupOf (M.subgroupOf N)).IsSubnormal := by
    set e : M.subgroupOf N ≃* M := Subgroup.subgroupOfEquivOfLe hMN with he
    have heq : (K.subgroupOf N).subgroupOf (M.subgroupOf N) =
        (K.subgroupOf M).comap e.toMonoidHom := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    rw [heq]
    exact hK'.2.1.comap _
  refine Sec6.mem_thetaComponentsIn_of hKN h.isPerfect_K ?_ h.isQuasisimple_K
  exact Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono N hKM) hKsn hMsn

theorem le_normalizer_K (h45 : Item4_5) (h : Config424 G A L a c K) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
    (sectionFourHyp_subgroup h.sectionFourHyp _) h.le_centralizer_c h.isElemAbelian
    ⟨3, le_rfl, by rw [h.card_eq]; norm_num⟩ K h.mem_thetaComponentsIn_centralizer

theorem center_K (h : Config424 G A L a c K) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
  Sec11.FieldCentRigid82.center_eq_bot_of_isType424 h.isType424

theorem three_dvd_card_K (h : Config424 G A L a c K) : 3 ∣ Nat.card K :=
  (three_dvd_card_of_isType424 h.isType424).trans (Subgroup.card_quotient_dvd_card _)

theorem card_closure_pair (h : Config424 G A L a c K) :
    Nat.card (Subgroup.closure ({a, c} : Set G)) = 9 :=
  card_closure_pair_eq_nine h.isElemAbelian h.card_eq h.a_mem h.c_mem h.a_ne_one h.c_not_mem

theorem eq_one_of_mem_closure_pair_of_mem_K (h : Config424 G A L a c K) {z : G}
    (hz : z ∈ Subgroup.closure ({a, c} : Set G)) (hzK : z ∈ K) : z = 1 := by
  have hBA : Subgroup.closure ({a, c} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.a_mem
    · exact h.c_mem
  have hBC : Subgroup.closure ({a, c} : Set G) ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr fun k _ => h.a_comm k
    · exact Subgroup.mem_centralizer_iff.mpr fun k hk => h.commute_c_of_mem_K hk
  refine eq_one_of_mem_of_commute h.center_K hzK (fun k hk => ?_) (h.pow_three z (hBA hz))
  exact (Subgroup.mem_centralizer_iff.mp (hBC hz) k hk).symm

theorem exists_mem_K_commute (h45 : Item4_5) (h : Config424 G A L a c K) :
    ∃ y ∈ K, orderOf y = 3 ∧ ∀ x ∈ A, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQN⟩ := KFacts.exists_sylow_le_normalizer h.isPGroup (h.le_normalizer_K h45)
  set Q' := (Q : Subgroup K).map K.subtype with hQ'
  have hQ'3 : IsPGroup 3 Q' := Q.isPGroup'.map K.subtype
  have hQ'K : Q' ≤ K := Subgroup.map_subtype_le _
  have hQ1 : (Q : Subgroup K) ≠ ⊥ := Q.ne_bot_of_dvd_card h.three_dvd_card_K
  have hQ'1 : Q' ≠ ⊥ := fun h0 => hQ1 ((Subgroup.map_eq_bot_iff_of_injective _
    K.subtype_injective).mp h0)
  set P := Q' ⊔ A with hP
  have hP3 : IsPGroup 3 P := IsPGroup.to_sup_of_normal_left' hQ'3 h.isPGroup hQN
  have hQ'P : Q' ≤ P := le_sup_left
  have hAP : A ≤ P := le_sup_right
  set H := Q'.subgroupOf P with hH
  have hHn : H.Normal := by
    rw [hH, Subgroup.normal_subgroupOf_iff_le_normalizer hQ'P]
    exact sup_le Subgroup.le_normalizer hQN
  have hH1 : H ≠ ⊥ := by
    intro h0
    apply hQ'1
    rw [← Subgroup.map_subgroupOf_eq_of_le hQ'P, ← hH, h0, Subgroup.map_bot]
  have hnil : Group.IsNilpotent P := hP3.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := H) hH1
  set Z := H ⊓ Subgroup.center P with hZdef
  have hZ3 : IsPGroup 3 Z := hP3.to_subgroup Z
  have hZc : 3 ∣ Nat.card Z := by
    rcases hZ3.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hZ
    · exact h1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hZc
  refine ⟨((y : P) : G), hQ'K (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp y.2).1), ?_, ?_⟩
  · rw [← hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · intro x hx
    have hc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp y.2).2 ⟨x, hAP hx⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    exact hc'

theorem exists_d (h45 : Item4_5) (h : Config424 G A L a c K) :
    ∃ d : G, A ⊓ K = Subgroup.zpowers d ∧ orderOf d = 3 ∧
      d ∉ Subgroup.closure ({a, c} : Set G) ∧ A = Subgroup.closure {a, c, d} := by
  obtain ⟨d, hdK, hd3, hdA⟩ := h.exists_mem_K_commute h45
  have hdA' : d ∈ A := mem_of_maximal_of_commute h.maximal
    (by rw [← hd3]; exact pow_orderOf_eq_one d) hdA
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hdB : d ∉ Subgroup.closure ({a, c} : Set G) := fun hB =>
    hd1 (h.eq_one_of_mem_closure_pair_of_mem_K hB hdK)
  have hA := eq_closure_triple h.card_eq h.a_mem h.c_mem hdA' h.card_closure_pair hdB
  refine ⟨d, ?_, hd3, hdB, hA⟩
  apply le_antisymm _ (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA', hdK⟩))
  set B := Subgroup.closure ({a, c} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.a_mem
    · exact h.c_mem
  let f : B × ↥(A ⊓ K) → A := fun p => ⟨(p.1 : G) * (p.2 : G), A.mul_mem (hBA p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ hbk
    have e : (b : G) * k = b' * k' := congrArg Subtype.val hbk
    have h1 : (b' : G)⁻¹ * b = k' * (k : G)⁻¹ := by
      calc (b' : G)⁻¹ * b = (b' : G)⁻¹ * (b * k) * (k : G)⁻¹ := by group
        _ = (b' : G)⁻¹ * (b' * k') * (k : G)⁻¹ := by rw [e]
        _ = k' * (k : G)⁻¹ := by group
    have h2 : (b' : G)⁻¹ * b = 1 := h.eq_one_of_mem_closure_pair_of_mem_K
      (B.mul_mem (B.inv_mem b'.2) b.2) (h1 ▸ K.mul_mem k'.2.2 (K.inv_mem k.2.2))
    have hbb : (b : G) = b' := by
      calc (b : G) = b' * ((b' : G)⁻¹ * b) := by group
        _ = b' := by rw [h2, mul_one]
    have hkk : (k : G) = k' := by
      have := e
      rw [hbb] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hbb) (Subtype.ext hkk)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, h.card_closure_pair, h.card_eq] at hcard
  have hle : Nat.card (A ⊓ K : Subgroup G) ≤ Nat.card (Subgroup.zpowers d) := by
    rw [Nat.card_zpowers, hd3]
    omega
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA', hdK⟩))
    hle).symm.le

end Config424

end CFSG.RankThree.PartTwo.Sec4
