module

public import CFSG.Quasithin.H13.A5W1623d
public import CFSG.Quasithin.H13.A5W1620Tc
public import CFSG.CGT.Timmesfeld75.Sec5NineMathieu

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq
  map_oPrimeResidualOf_top)

section A318

theorem eq_oPrime_of_center_three (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) {G : Type} [Group G] [Finite G] {I L : Subgroup G} (hH : SQTKGroup ↥I)
    (hL : L ∈ cComp I) (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    {S : Type} [Group S] [Finite S] (hS : A318Exclusion S)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S)
    (hno3 : ∀ (s : Bool) (q : ℕ), IsSLEps3 s q (↥L ⧸ CFSG.pCore 2 ↥L) → False)
    (hhat : ∀ (Y : Type) [Group Y], (IsHat Y (alternatingGroup (Fin 6)) ∨
      IsHat Y (alternatingGroup (Fin 7)) ∨ IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) →
      Nat.card Y ≠ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    L = oPrimeResidualOf 3 I := by
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
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3, -⟩
  · rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
  · exfalso
    obtain ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    subst hq
    let ψ : ↥(starImage 3 (L.subgroupOf I)) →* S :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Lb)).comp eLX.toMonoidHom)
    have hψ : Function.Surjective ψ :=
      e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eLX.surjective)
    exact hS.noImage _ s r k hrp hk1 hPSL hmod ψ hψ
  · exfalso
    rcases h3 with ⟨s, q, -, hSL⟩ | hY
    · refine hno3 s q ?_
      cases s
      · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
        exact ⟨K, inferInstance, inferInstance, hK, ⟨eLX.symm.trans eK⟩⟩
      · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hSL
        exact ⟨K, inferInstance, inferInstance, hK, ⟨eLX.symm.trans eK⟩⟩
    · exact hhat _ hY (Nat.card_congr eLX.toEquiv)

theorem card_eq_three_mul_of_isHat {Y X : Type} [Group Y] [Group X] (h : IsHat Y X) :
    Nat.card Y = 3 * Nat.card X := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y),
    Nat.card_congr e.toEquiv, hZ, mul_comm]

theorem card_hat_ne_60480 {Y : Type} [Group Y] (hY : IsHat Y (alternatingGroup (Fin 6)) ∨
    IsHat Y (alternatingGroup (Fin 7)) ∨ IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    Nat.card Y ≠ 60480 := by
  rcases hY with h | h | h
  · rw [card_eq_three_mul_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · rw [card_eq_three_mul_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · intro hc
    have h11 : 11 ∣ Nat.card Y := by
      rw [card_eq_three_mul_of_isHat h]
      exact Dvd.dvd.mul_left CFSG.CGT.Timmesfeld75.eleven_dvd_card_nativeM22 3
    rw [hc] at h11
    exact absurd h11 (by decide)

end A318

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem eq_oPrime_of_sl4 (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (e4 : ↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    K = oPrimeResidualOf 3 (Subgroup.centralizer ({S.v12} : Set G)) := by
  have hl := SBc5.isPSL_two_of_statedSL (n := 4) (by norm_num) e4
  have hX := hKF.l42 _ hl
  have hcard : Nat.card ↥(S.plus K) = 20160 := by
    rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  let eX : ↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K) ≃* ↥(S.plus K) :=
    quotCenterEquivOfEqBot hX.center_eq_bot
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 :=
    (Nat.card_congr eX.toEquiv).trans hcard
  obtain ⟨hq, hZ⟩ := S.kbar_cases_big h1222 h517 hF h36 h37 h38 hK hYz hT (Or.inl hN)
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
  let eA : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(S.plus K) :=
    (centerQuotEquiv π hπ hker).trans eX
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
      (S.pCoreOf_Gv_ne_bot h1222 h517 hF)
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  rcases hZ with hZ | hZ3
  · exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38' hGv hK hq
      ((quotCenterEquivOfEqBot hZ).symm.trans eA) hX
  · have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60480 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _),
        Nat.card_congr eA.toEquiv, hZ3, hcard]
    refine eq_oPrime_of_center_three hF318 h36 h38' hGv hK hq hZ3 hX eA ?_
      (fun Y _ hY => hcK ▸ card_hat_ne_60480 hY)
    intro s q hSL
    have hcK' : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 * 20160 := hcK
    cases s
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK' ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := card_statedSU_three_of hK'
      rw [← Nat.card_congr eK.toEquiv, hcK'] at h2
      exact (sl3_su3_card_big hq2).1 h2.symm
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
      rw [← Nat.card_congr eK.toEquiv, hcK', hK'] at h2
      have hq2 : 2 ≤ q := hK' ▸ Finite.one_lt_card
      have hq4 := (sl3_su3_card_big hq2).2.2.2 h2.symm
      have hP := isPSL_quot_center_of_statedSL (hK'.trans hq4) eK
      exact hX.noImage _ true 2 2 Nat.prime_two (by norm_num) hP (by decide)
        (eA.toMonoidHom.comp (MonoidHom.id _)) eA.surjective

end Setting

theorem o3Prime1367_of (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) : O3Prime1367 := by
  intro G _ _ T L V S hH K hK hYz hT ⟨e4⟩
  exact S.eq_oPrime_of_sl4 h1222 h517 hF318 h36 h37 h38 hKF hH.hF hK hYz hT e4

end CFSG.Quasithin.H13.A5
