module

public import CFSG.Quasithin.H13.A5W1620Tb
public import CFSG.Quasithin.H13.A5W1620P
public import CFSG.Quasithin.EmptyFaithful.SBc5Three

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd
  quotPCore_subgroupOf_equiv pRank_subgroupOf_eq map_oPrimeResidualOf_top)

section Orders

theorem sl2_order_ne {p m a : ℕ} (h1 : a * (a ^ 2 - 1) < m)
    (h2 : m < (a + 1) * ((a + 1) ^ 2 - 1)) : p * (p ^ 2 - 1) ≠ m := by
  intro h
  rcases Nat.lt_or_ge a p with hap | hpa
  · have h3 : (a + 1) * ((a + 1) ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul hap (Nat.sub_le_sub_right (Nat.pow_le_pow_left hap 2) 1)
    omega
  · have h3 : p * (p ^ 2 - 1) ≤ a * (a ^ 2 - 1) :=
      Nat.mul_le_mul hpa (Nat.sub_le_sub_right (Nat.pow_le_pow_left hpa 2) 1)
    omega

theorem sl2_order_ne_big {p c N : ℕ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hN : N = 20160 ∨ N = 9999360) : p * (p ^ 2 - 1) ≠ N * c := by
  rcases hN with rfl | rfl <;> interval_cases c
  · exact sl2_order_ne (a := 27) (by norm_num) (by norm_num)
  · exact sl2_order_ne (a := 34) (by norm_num) (by norm_num)
  · exact sl2_order_ne (a := 215) (by norm_num) (by norm_num)
  · exact sl2_order_ne (a := 271) (by norm_num) (by norm_num)

theorem sl3_su3_card_big {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ 60480 ∧ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ 29998080 ∧
      q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ 29998080 ∧
      (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = 60480 → q = 4) := by
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hbound : ∀ t : ℕ, q ^ 3 - 1 ≤ t → q ^ 3 * (q ^ 2 - 1) * t ≤ 29998080 → q ≤ 10 := by
    intro t ht h
    by_contra hc
    push Not at hc
    have h1 : 1331 ≤ q ^ 3 := by
      calc 1331 = 11 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hc 3
    have h2 : 120 ≤ q ^ 2 - 1 := by
      have : 121 ≤ q ^ 2 := by
        calc 121 = 11 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have h3 : 1331 * 120 * 1330 ≤ q ^ 3 * (q ^ 2 - 1) * t :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (by omega)
    omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hq10 := hbound _ (by omega) ((le_of_eq h).trans (by norm_num))
    interval_cases q <;> norm_num at h
  · have hq10 := hbound _ le_rfl (le_of_eq h)
    interval_cases q <;> norm_num at h
  · have hq10 := hbound _ (by omega) (le_of_eq h)
    interval_cases q <;> norm_num at h
  · have hq10 := hbound _ le_rfl ((le_of_eq h).trans (by norm_num))
    interval_cases q <;> first | rfl | norm_num at h

end Orders

section PSL3

theorem center_statedSL_eq_statedScalars (n : ℕ) (K : Type) [Field K] :
    Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSL n K) =
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin n) K).subgroupOf
        (CFSG.Assembly.LowTwoRank.StatedSL n K) := by
  rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars, Subgroup.map_center_eq]

theorem isPSL_quot_center_of_statedSL {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (eX : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) :
    IsPSL 3 2 2 (X ⧸ Subgroup.center X) := by
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by rw [hK]; norm_num, ⟨QuotientGroup.congr _ _ eX ?_⟩⟩
  rw [← center_statedSL_eq_statedScalars]
  exact Subgroup.map_center_eq eX

end PSL3

section A318

theorem eq_oPrime_or_theta_of_center_three' (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {G : Type} [Group G] [Finite G] {I L : Subgroup G} (hH : SQTKGroup ↥I)
    (hL : L ∈ cComp I) (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    {S : Type} [Group S] [Finite S] (hS : A318Exclusion S)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S)
    (hno3 : ∀ (s : Bool) (q : ℕ), IsSLEps3 s q (↥L ⧸ CFSG.pCore 2 ↥L) → False) :
    L = oPrimeResidualOf 3 I ∨ L = thetaOf I := by
  classical
  have hLH : L ≤ I := le_of_mem_cComp hL
  set Lb := ↥L ⧸ CFSG.pCore 2 ↥L with hLb
  have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Lb) := by
    refine two_le_pRank_of_card_center_three hZ3 ?_
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact hS.rank
  have hcardLb : Nat.card Lb = 3 * Nat.card S := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Lb),
      Nat.card_congr e.toEquiv, hZ3, mul_comm]
  have hSQ := SQTKHyp.of_sqtkGroup ↥I hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr1 : 1 < CFSG.Open.pRank 3 (L.subgroupOf I) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num)]
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr1
  have hLn : (L.subgroupOf I).Normal :=
    A318.normal_of_pRank_gt_one hH (h38 _ hSQ) hLc Nat.prime_three (by norm_num) hr1
  have hcen' : Nat.card (Subgroup.center
      (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.centerCongr e₀).toEquiv
  have hZ3' : IsPGroup 3 ↥(Subgroup.center
      (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hcen']; norm_num)
  have h3X' : 3 ∣ Nat.card (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I)) := by
    rw [Nat.card_congr e₀.toEquiv, hcardLb]
    exact dvd_mul_right 3 _
  obtain ⟨eS⟩ := nonempty_starImage_equiv (L := L.subgroupOf I) hQ' hZ3' h3X'
  let eLX : ↥(starImage 3 (L.subgroupOf I)) ≃* Lb := eS.trans e₀
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
  · left
    rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
  · exfalso
    obtain ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    subst hq
    let ψ : ↥(starImage 3 (L.subgroupOf I)) →* S :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Lb)).comp eLX.toMonoidHom)
    have hψ : Function.Surjective ψ :=
      e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eLX.surjective)
    exact hS.noImage _ s r k hrp hk1 hPSL hmod ψ hψ
  · right
    rw [← map_thetaOf_top, ← h3a, Subgroup.map_subgroupOf_eq_of_le hLH]
  · exfalso
    obtain ⟨s, q, x, hSL, -⟩ := h3b
    refine hno3 s q ?_
    cases s
    · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
      exact ⟨K, inferInstance, inferInstance, hK, ⟨eLX.symm.trans eK⟩⟩
    · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
      exact ⟨K, inferInstance, inferInstance, hK, ⟨eLX.symm.trans eK⟩⟩

end A318

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_cases_big (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 9999360) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨
        Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective
  have hcen : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (Subgroup.center ↥(modO2Image Gv K)) :=
    Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF) hK
  rcases hA with ⟨hcomp, hsimp, -⟩ | ⟨hcomp, h3, -⟩ | h3 | h4
  · refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1, Or.inl ?_⟩
    have hZ : Subgroup.center ↥(modO2Image Gv K) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(modO2Image Gv K)) with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := hcomp.1
        apply hab
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [(QuotientGroup.eq_one_iff a).mpr (h ▸ Subgroup.mem_top a),
          (QuotientGroup.eq_one_iff b).mpr (h ▸ Subgroup.mem_top b)]
    rw [hZ, Subgroup.card_bot] at hcen
    exact Subgroup.card_eq_one.mp hcen
  · exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1, Or.inr (by rw [hcen, h3])⟩
  · exfalso
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact sl2_order_ne_big hc1 hc2 hN hcard.symm
  · exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rcases hN with h | h <;> rw [h] at hcard <;> omega

theorem Lv_le_of_exclusion_big (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {X : Type} [Group X] [Finite X]
    (hX : A318Exclusion X) (e : ↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K) ≃* X)
    (hcard : Nat.card X = 20160 ∨ Nat.card X = 9999360) : S.Lv ≤ K := by
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = Nat.card X :=
    Nat.card_congr e.toEquiv
  obtain ⟨hq, hZ⟩ := S.kbar_cases_big h1222 h517 hF h36 h37 h38 hK hYz hT (hN ▸ hcard)
  have hLv := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus h1222 h517 hF hYz.1 hT hLv
  have hqP := S.isQuasisimple_plus h1222 h517 hF hYz hT
  have hnt : Nontrivial ↥(S.plus K) := by
    obtain ⟨a, b, hab⟩ := hqP.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hker := ker_le_center_of_isQuasisimple hq π hπ hnt
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  let eA : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X :=
    (centerQuotEquiv π hπ hker).trans e
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
      (S.pCoreOf_Gv_ne_bot h1222 h517 hF)
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  refine S.Lv_le_of_eq_oPrime_or_theta ?_
  rcases hZ with hZ | hZ3
  · left
    exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38' hGv hK hq
      ((quotCenterEquivOfEqBot hZ).symm.trans eA) hX
  · refine eq_oPrime_or_theta_of_center_three' hF318 h36 h38' hGv hK hq hZ3 hX eA ?_
    have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 * Nat.card X := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _),
        Nat.card_congr eA.toEquiv, hZ3, mul_comm]
    intro s q hSL
    cases s
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK' ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := card_statedSU_three_of hK'
      rw [← Nat.card_congr eK.toEquiv, hcK] at h2
      rcases hcard with h | h <;> rw [h] at h2
      · exact (sl3_su3_card_big hq2).1 h2.symm
      · exact (sl3_su3_card_big hq2).2.2.1 h2.symm
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
      rw [← Nat.card_congr eK.toEquiv, hcK, hK'] at h2
      have hq2 : 2 ≤ q := hK' ▸ Finite.one_lt_card
      rcases hcard with h | h <;> rw [h] at h2
      · have hq4 := (sl3_su3_card_big hq2).2.2.2 h2.symm
        have hP := isPSL_quot_center_of_statedSL (hK'.trans hq4) eK
        exact hX.noImage _ true 2 2 Nat.prime_two (by norm_num) hP (by decide)
          (eA.toMonoidHom.comp (MonoidHom.id _)) eA.surjective
      · exact (sl3_su3_card_big hq2).2.1 h2.symm

end Setting

theorem lemma13620L45_of (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) : Lemma13620L45 := by
  intro G _ _ T L V S hH K hK hYz hT h45
  have hF := hH.hF
  rcases h45 with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hl := SBc5.isPSL_two_of_statedSL (n := 4) (by norm_num) e4
    have hX := hKF.l42 _ hl
    have hcard : Nat.card ↥(S.plus K) = 20160 := by
      rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    exact S.Lv_le_of_exclusion_big h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hX
      (quotCenterEquivOfEqBot hX.center_eq_bot) (Or.inl hcard)
  · obtain ⟨e5⟩ := h5
    have hl := SBc5.isPSL_two_of_statedSL (n := 5) (by norm_num) e5
    have hX := hKF.l52 _ hl
    have hcard : Nat.card ↥(S.plus K) = 9999360 := by
      rw [Nat.card_congr e5.toEquiv, ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    exact S.Lv_le_of_exclusion_big h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hX
      (quotCenterEquivOfEqBot hX.center_eq_bot) (Or.inr hcard)

end CFSG.Quasithin.H13.A5
