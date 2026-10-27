module

public import CFSG.Walter.Bender1970.S3.CoreExchangeTools
public import CFSG.Walter.Bender1970.S3.PGroupFStar
public import CFSG.Walter.Bender1970.S1.PCoreRankTwo
public import CFSG.Walter.Bender1970.S2.Generation

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Bender39Conditions (t : G) (H T V : Subgroup G) (p : ℕ) : Prop :=
  (Subgroup.centralizer (V : Set G) ≤ H ∧ ⁅V, Subgroup.zpowers t⁆ = V) ∨
  ((∀ v ∈ V, v ≠ 1 → t ∈ Subgroup.centralizer ({v} : Set G) ∧
      Subgroup.centralizer ({v} : Set G) ≤ H) ∧ CFSG.Open.IsElemAbelian p V ∧
    Nat.card V = p ^ 2) ∨
  (t ∈ Subgroup.centralizer (V : Set G) ∧ Subgroup.centralizer (V : Set G) ≤ H ∧
    ∃ W ≤ T, IsKleinFour W ∧ ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ H)

omit [Finite G] in
theorem Bender39Conditions.centralizer_le {t : G} {H T V : Subgroup G} {p : ℕ}
    (h : Bender39Conditions t H T V p) (hp : 1 < p) :
    Subgroup.centralizer (V : Set G) ≤ H := by
  rcases h with ⟨hCV, -⟩ | ⟨hVv, -, hVcard⟩ | ⟨-, hCV, -⟩
  · exact hCV
  · have hV1 : V ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hVcard
      have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp
      omega
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr v.2)).trans
      (hVv v v.2 fun h => hv1 (Subtype.ext h)).2
  · exact hCV

omit [Finite G] in
theorem Bender39Conditions.ne_bot {t : G} {H T V : Subgroup G} {p : ℕ}
    (h : Bender39Conditions t H T V p) (hp : 1 < p) (hH : H ≠ ⊤) : V ≠ ⊥ := by
  intro hV
  apply hH
  rw [eq_top_iff]
  have := h.centralizer_le hp
  have h1 : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  rw [hV, h1] at this
  exact this

theorem qCoreOf_two_le_sylow {M : Subgroup G} (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    qCoreOf M 2 ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := T.isPGroup'.to_sup_of_normal_right' (qCoreOf_isPGroup M 2)
    (hTM.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in M 2)))
  have heq := T.is_maximal' h le_sup_left
  exact le_sup_right.trans heq.le

omit [Finite G] in
theorem exists_sylow_mem {X : Subgroup G} {t : G} (htX : t ∈ X) (ht : orderOf t = 2) :
    ∃ T : Sylow 2 X, (⟨t, htX⟩ : X) ∈ (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : IsPGroup 2 (Subgroup.zpowers (⟨t, htX⟩ : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  obtain ⟨T, hT⟩ := htp.exists_le_sylow
  exact ⟨T, hT (Subgroup.mem_zpowers _)⟩

theorem mem_primesOfOrder_of_qCoreOf_ne_bot {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQ : qCoreOf M p ≠ ⊥) : p ∈ primesOfOrder (generalizedFittingSubgroupOf M) := by
  have : Fact p.Prime := ⟨hp⟩
  show p ∈ (Nat.card (generalizedFittingSubgroupOf M)).primeFactors
  rw [Nat.mem_primeFactors]
  refine ⟨hp, ?_, Nat.card_pos.ne'⟩
  have : Nontrivial (qCoreOf M p) := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card (qCoreOf_isPGroup M p)).mp inferInstance
  have h1 : p ∣ Nat.card (qCoreOf M p) := hcard ▸ dvd_pow_self p hn.ne'
  exact h1.trans (Subgroup.card_dvd_of_le
    ((qCoreOf_le_fittingSubgroupOf M p hp).trans le_sup_left))

theorem two_le_card_primes_of_benderM
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2) {M : Subgroup G}
    (hM : M ∈ benderM s) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (hQ : qCoreOf M p ≠ ⊥) : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf M)) := by
  by_contra hlt
  push Not at hlt
  have hpπ := mem_primesOfOrder_of_qCoreOf_ne_bot hp hQ
  have hfin : (primesOfOrder (generalizedFittingSubgroupOf M)).Finite :=
    (Nat.card (generalizedFittingSubgroupOf M)).primeFactors.finite_toSet
  have hsub : primesOfOrder (generalizedFittingSubgroupOf M) ⊆ {p} := by
    intro r hr
    rw [Nat.card_coe_set_eq] at hlt
    exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one hfin).mp (by omega) r hr p hpπ)
  have hFH := bender1970_3_6 hG hs hM hp hp2 (isPGroup_of_primesOfOrder_subset hp hsub) ht hH
  have := card_primesOfOrder_le_one_of_isPGroup hp hFH
  omega

theorem pResidualOf_ne_bot_of_benderM
    (hG : BenderCounterexample G) {t : G}
    (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2)
    {M : Subgroup G} (hM : M ∈ benderM s) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) :
    pResidualOf (generalizedFittingSubgroupOf M) p ≠ ⊥ := by
  intro h
  have hFM := isPGroup_of_pResidualOf_eq_bot _ p hp h
  have hFH := bender1970_3_6 hG hs hM hp hp2 hFM ht hH
  have := card_primesOfOrder_le_one_of_isPGroup hp hFH
  omega

theorem not_dvd_card_qCoreOf {M : Subgroup G} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) : ¬ p ∣ Nat.card (qCoreOf M q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro h
  obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M q).exists_card_eq
  rw [hk] at h
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm

theorem pResidualOf_le_of_bender39Conditions
    (hG : BenderCounterexample G) {t : G}
    (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G}
    (hVP : V ≤ qCoreOf H p) {s : G} (hsT : s ∈ (T : Subgroup G)) {M : Subgroup G}
    (hM : M ∈ benderM s) (hVM : V ≤ M) (habc : Bender39Conditions t H T V p) :
    pResidualOf (generalizedFittingSubgroupOf M) p ≤ H := by
  have hMco := isCoatom_of_mem_benderM hM
  have hCH := centralizer_le_of_mem_benderM hH
  have hTH : (T : Subgroup G) ≤ H := hG.sylow_le_of_mem_benderM T htT hH
  have hTM : (T : Subgroup G) ≤ M := hG.sylow_le_of_mem_benderM T hsT hM
  have htM : t ∈ M := hTM htT
  have hMA : IsAStar M := hG.isAStar_of_isCoatom hMco
  have hVU : V ≤ Subgroup.centralizer ({t} : Set G) →
      V ≤ oddCoreOf (CFSG.fittingSubgroupOf (M ⊓ Subgroup.centralizer ({t} : Set G))) := by
    intro hVt
    have hVodd : Odd (Nat.card V) := by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hVP).exists_card_eq
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have hVF : V ≤ oddCoreOf (CFSG.fittingSubgroupOf H) :=
      le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent H)
        (hVP.trans (qCoreOf_le_fittingSubgroupOf H p hp)) hVodd
    exact (le_inf hVF (le_inf hVM hVt)).trans (oddCoreOf_fitting_inf_le (inf_le_right.trans hCH))
  refine (pResidualOf_generalizedFitting_le M hp).trans ?_
  rcases habc with ⟨hCV, hVt⟩ | ⟨hVv, hVel, hVcard⟩ | ⟨htV, hCV, W, hWT, hW, hWC⟩
  ·
    have h24 : ⁅qCoreOf H p ⊓ M, Subgroup.zpowers t⁆ ≤ qCoreOf M p :=
      bender1970_2_4_pGroup_subgroup hMA htM ht hp hp2 inf_le_right
        ((qCoreOf_isPGroup H p).to_le inf_le_left) fun c hc =>
          mem_normalizer_inf (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc.2))
            (Subgroup.le_normalizer hc.1)
    have hVQ : V ≤ qCoreOf M p := by
      rw [← hVt]
      exact (Subgroup.commutator_mono (le_inf hVP hVM) le_rfl).trans h24
    refine le_trans ?_ hCV
    refine sup_le (sSup_le ?_) ?_
    · rintro _ ⟨q, hq, hqp, rfl⟩
      exact (qCoreOf_centralizer_of_ne M hp hq (Ne.symm hqp)).trans (Subgroup.centralizer_le hVQ)
    · exact (componentLayerOf_le_centralizer_fitting M).trans
        (Subgroup.centralizer_le (hVQ.trans (qCoreOf_le_fittingSubgroupOf M p hp)))
  ·
    have hVt : V ≤ Subgroup.centralizer ({t} : Set G) := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]
        exact Subgroup.one_mem _
      · have h := (hVv v hv hv1).1
        rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
        exact h.symm
    have hVcyc : ¬ IsCyclic V := by
      intro hcyc
      have h1 : Monoid.exponent V ∣ p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hVel.2 x x.2)
      rw [IsCyclic.exponent_eq_card, hVcard] at h1
      have := Nat.le_of_dvd hp.pos h1
      have := hp.one_lt
      nlinarith
    refine sup_le (sSup_le ?_) (sSup_le fun L hL => ?_)
    · rintro _ ⟨q, hq, hqp, rfl⟩
      refine (le_iSup_inf_centralizer hp hVel.1 hVel.2 (by rw [hVcard])
        (hVM.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in M q)))
        (not_dvd_card_qCoreOf hp hq hqp)).trans ?_
      exact iSup₂_le fun v hv => iSup_le fun hv1 => inf_le_right.trans (hVv v hv hv1).2
    · obtain ⟨u, huV, hu1, hLu⟩ :=
        exists_ne_one_mem_centralizer_of_isComponentOf hMA htM ht (hVU hVt) hVcyc hL
      exact hLu.trans (hVv u huV hu1).2
  ·
    have hVt : V ≤ Subgroup.centralizer ({t} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp htV) v hv
    have hWcomm : IsMulCommutative W :=
      ⟨⟨fun a b => mul_comm_of_exponent_two hW.exponent_two a b⟩⟩
    have hWexp : ∀ x ∈ W, x ^ 2 = 1 := fun x hx => by
      have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : W)
      rw [hW.exponent_two] at h
      exact congrArg Subtype.val h
    have hWcard : 2 ^ 2 ≤ Nat.card W := by rw [hW.card_four]; norm_num
    have hWM : W ≤ M := hWT.trans hTM
    refine sup_le (sSup_le ?_) (sSup_le fun L hL => ?_)
    · rintro _ ⟨q, hq, hqp, rfl⟩
      by_cases hq2 : q = 2
      · subst hq2
        exact (qCoreOf_two_le_sylow T hTM).trans hTH
      · refine (le_iSup_inf_centralizer Nat.prime_two hWcomm hWexp hWcard
          (hWM.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in M q)))
          (not_dvd_card_qCoreOf Nat.prime_two hq hq2)).trans ?_
        exact iSup₂_le fun w hw => iSup_le fun hw1 => inf_le_right.trans (hWC w hw hw1)
    · by_cases hL2 : IsTypeL2Even (L ⧸ Subgroup.center L) ∨ IsTypeJR (L ⧸ Subgroup.center L)
      · obtain ⟨T', hT'⟩ := exists_sylow_mem htM ht
        obtain ⟨-, -, hE⟩ := bender1970_2_5_subgroup hMA htM ht T' hT' rfl
        obtain ⟨-, -, -, hiii⟩ := hE L hL
        exact (Subgroup.le_centralizer_iff.mp ((hVU hVt).trans (hiii hL2))).trans hCV
      · push Not at hL2
        rw [bender1970_2_6_subgroup hMA hWM hW hL hL2.1]
        exact iSup₂_le fun w hw => iSup_le fun hw1 => inf_le_right.trans (hWC w hw hw1)

theorem bender1970_3_9_cores_aux
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G} (hVP : V ≤ qCoreOf H p)
    {s : G} (hs : orderOf s = 2) (hsT : s ∈ (T : Subgroup G)) {M : Subgroup G}
    (hM : M ∈ benderM s)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) (hVM : V ≤ M)
    (habc : Bender39Conditions t H T V p) :
    pResidualOf (generalizedFittingSubgroupOf M) p ≤ H ∧ qCoreOf H p ≤ M ∧
      pResidualOf (generalizedFittingSubgroupOf M) p ≤
        Subgroup.centralizer (qCoreOf H p : Set G) := by
  have := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set Q := qCoreOf M p with hQdef
  set K := pResidualOf (generalizedFittingSubgroupOf M) p with hKdef
  have hHco := isCoatom_of_mem_benderM hH
  have hMco := isCoatom_of_mem_benderM hM
  have hCM := centralizer_le_of_mem_benderM hM
  have hTH : (T : Subgroup G) ≤ H := hG.sylow_le_of_mem_benderM T htT hH
  have hsH : s ∈ H := hTH hsT
  have hsM : s ∈ M := mem_of_mem_benderM hM
  have hMA : IsAStar M := hG.isAStar_of_isCoatom hMco
  have hV1 : V ≠ ⊥ := habc.ne_bot hp.one_lt hHco.1
  have hCV : Subgroup.centralizer (V : Set G) ≤ H := habc.centralizer_le hp.one_lt
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hQp : IsPGroup p Q := qCoreOf_isPGroup M p
  have hPN : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hQN : M ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in M p)
  have hKH : K ≤ H := pResidualOf_le_of_bender39Conditions hG ht hH T htT hp hp2 hVP hsT hM hVM habc
  have hKn : IsNormalIn K M := pResidualOf_generalizedFitting_isNormalIn M p
  have hKQ : K ≤ Subgroup.centralizer (Q : Set G) :=
    pResidualOf_generalizedFitting_le_centralizer M hp
  have hKK : pResidualOf K p = K := pResidualOf_pResidualOf _ p hp
  have hKPM : ⁅K, P ⊓ M⁆ = ⊥ := by
    refine commutator_eq_bot_of_pResidual hp hKK
      (inf_le_right.trans (le_normalizer_of_isNormalIn hKn)) (hKH.trans hPN) inf_le_left
      (hPp.to_le inf_le_right) ?_
    have hKPn : ((K ⊓ P).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
        mem_normalizer_inf (Subgroup.le_normalizer hk) (hPN (hKH hk))
    have h1 : K ⊓ P ≤ qCoreOf K p :=
      le_qCoreOf_of_normal_isPGroup K (K ⊓ P) p inf_le_left hKPn (hPp.to_le inf_le_right)
    have hOKn : IsNormalIn (qCoreOf K p) M :=
      map_characteristic_isNormalIn_of_isNormalIn (pCore p K) inferInstance hKn
    have h2 : qCoreOf K p ≤ Q :=
      le_qCoreOf_of_normal_isPGroup M (qCoreOf K p) p hOKn.1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hOKn.1).mpr
          (le_normalizer_of_isNormalIn hOKn)) (qCoreOf_isPGroup K p)
    exact (h1.trans h2).trans (Subgroup.le_centralizer_iff.mp hKQ)
  have hPMK : ⁅P ⊓ M, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hKPM
  set ZQ := Q ⊓ Subgroup.centralizer (Q : Set G) with hZQdef
  set Z := ZQ ⊓ Subgroup.centralizer ((P ⊓ M : Subgroup G) : Set G) with hZdef
  have hVPM : V ≤ P ⊓ M := le_inf hVP hVM
  have hZQn : IsNormalIn ZQ M := ⟨inf_le_left.trans (qCoreOf_normal_in M p).1, fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf (hQN hm)
      (Bender35.mem_normalizer_centralizer (hQN hm))) z).mp hz⟩
  have hZM : Subgroup.centralizer (Z : Set G) ≤ M := by
    by_cases hr : rank Q ≤ 2
    · have hPMQ : P ⊓ M ≤ Q :=
        bender1970_1_4 hMA.1 hp inf_le_right (hPp.to_le inf_le_left) hr hPMK
      have hQ1 : Q ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVPM.trans hPMQ))
      have hZQ1 : ZQ ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hp hQp hQp Subgroup.le_normalizer hQ1
      have hZQZ : ZQ ≤ Z := le_inf le_rfl fun x hx => Subgroup.centralizer_le hPMQ hx.2
      exact (Subgroup.centralizer_le hZQZ).trans ((Subgroup.centralizer_le_normalizer _).trans
        (hG.normalizer_eq_of_isNormalIn hMco hZQn hZQ1).le)
    · push Not at hr
      have hQ1 : Q ≠ ⊥ := by
        intro h
        have : rank Q ≤ 1 :=
          rank_le_one_of_card_le hp hQp (by rw [h, Subgroup.card_bot]; exact hp.one_lt.le)
        omega
      have hZQ1 : ZQ ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hp hQp hQp Subgroup.le_normalizer hQ1
      have hPMZQ : P ⊓ M ≤ Subgroup.normalizer (ZQ : Set G) :=
        inf_le_right.trans (le_normalizer_of_isNormalIn hZQn)
      have hZ1 : Z ≠ ⊥ :=
        inf_centralizer_ne_bot_of_isPGroup hp (hPp.to_le inf_le_left) (hQp.to_le inf_le_left)
          hPMZQ hZQ1
      have hZQ : Z ≤ Q := inf_le_left.trans inf_le_left
      by_cases hsQ : Q ≤ Subgroup.centralizer ({s} : Set G)
      ·
        have hZp : IsPGroup p Z := hQp.to_le hZQ
        have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ1
        obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hZp).mp inferInstance
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p
          (by rw [hcard]; exact dvd_pow_self p hn.ne')
        have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
        obtain ⟨E, hEQ, hE, hEcard⟩ := exists_isElemAbelian_of_le_rank hp hQp (k := 3) hr
        have hzE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (z : G)) := by
          refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
          · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
            obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
            rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
            exact (Commute.zpow_zpow_self (z : G) i j).eq
          · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
              pow_orderOf_eq_one, one_zpow]
        have hEz : E ≤ Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
          rw [centralizer_zpowers_eq']
          intro e he
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp z.2.1.2) e (hEQ he)
        have hV₀ := isElemAbelian_sup hE hzE hEz
        have hV₀Q : E ⊔ Subgroup.zpowers (z : G) ≤ Q :=
          sup_le hEQ (Subgroup.zpowers_le.mpr (hZQ z.2))
        have hV₀3 : 3 ≤ rank (E ⊔ Subgroup.zpowers (z : G)) := by
          obtain ⟨k, hk⟩ := (hQp.to_le hEQ).exists_card_eq
          have hk3 : 3 ≤ k := by
            rw [hk] at hEcard
            exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hEcard
          exact hk3.trans (le_rank hp le_sup_left hE hk)
        have hz1 : (z : G) ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hzo
          exact hp.one_lt.ne hzo
        have h37 := bender1970_3_7 hG hs hM hp hp2 hsQ hV₀Q hV₀ hV₀3
          ((le_sup_right : Subgroup.zpowers (z : G) ≤ _) (Subgroup.mem_zpowers _)) hz1
        exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr z.2)).trans h37
      ·
        have hpt : ⁅Subgroup.zpowers s, Q⁆ ≠ ⊥ := by
          intro h
          apply hsQ
          rw [commutator_zpowers_eq_bot_iff] at h
          intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact h x hx
        obtain ⟨Pbar, hPbarQ, hPbarC, hPbart, hPbarA⟩ := bender1970_3_5 hG hs hM hp hpt
        have hsC : s ∈ Subgroup.centralizer ({s} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr rfl
        have hsN : s ∈ Subgroup.normalizer (Pbar : Set G) := hPbarC hsC
        set U := ⁅Pbar, Subgroup.zpowers s⁆ with hUdef
        have hU1 : U ≠ ⊥ := by rw [hUdef, Subgroup.commutator_comm]; exact hPbart
        have hUA : U ∈ benderABar M :=
          hPbarA U (commutator_zpowers_le_of_mem_normalizer hsN) hU1
            (mem_normalizer_commutator hsN (Subgroup.le_normalizer (Subgroup.mem_zpowers s)))
        have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers s)) (Nat.card Pbar) := by
          obtain ⟨k, hk⟩ := (hQp.to_le hPbarQ).exists_card_eq
          rw [Nat.card_zpowers, hs, hk]
          exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
        have hUt : ⁅U, Subgroup.zpowers s⁆ = U :=
          le_antisymm (commutator_zpowers_le_of_mem_normalizer
            (mem_normalizer_commutator hsN (Subgroup.le_normalizer (Subgroup.mem_zpowers s))))
            (commutator_le_commutator_commutator _ _ (Subgroup.zpowers_le.mpr hsN) hcop)
        have hUZ : U ≤ Subgroup.centralizer (Z : Set G) := by
          rw [Subgroup.le_centralizer_iff]
          exact (inf_le_left.trans inf_le_right).trans (Subgroup.centralizer_le
            ((commutator_zpowers_le_of_mem_normalizer hsN).trans hPbarQ))
        obtain ⟨hZF, hZsn⟩ := Bender35.le_and_isSubnormal hp hZQ
        have hsPM : s ∈ Subgroup.normalizer ((P ⊓ M : Subgroup G) : Set G) :=
          mem_normalizer_inf (hPN hsH) (Subgroup.le_normalizer hsM)
        have hsZ : s ∈ Subgroup.normalizer (Z : Set G) :=
          mem_normalizer_inf (mem_normalizer_inf (hQN hsM)
            (Bender35.mem_normalizer_centralizer (hQN hsM)))
            (Bender35.mem_normalizer_centralizer hsPM)
        have hZA := bender1970_3_1_ii hG hs hM hZ1 hZF hZsn hsZ hUA hUZ hUt
        have hπM := two_le_card_primes_of_benderM hG ht hH hs hM hp hp2 hπ hQ1
        exact (Subgroup.centralizer_le_normalizer _).trans (hZA.2.2.1 hπM)
  have hZQH : Z ≤ Q ⊓ H :=
    le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans ((Subgroup.centralizer_le hVPM).trans hCV))
  have hCQH : Subgroup.centralizer ((Q ⊓ H : Subgroup G) : Set G) ≤ M :=
    (Subgroup.centralizer_le hZQH).trans hZM
  have hKP : Centralizes K P := by
    refine bender1970_1_1_thompson p hp (Q ⊓ H) K P (hQp.to_le inf_le_left) hPp hKK
      (inf_le_right.trans hPN) (hKH.trans hPN) ?_ ?_
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_left.trans (Subgroup.le_centralizer_iff.mp hKQ)
    · exact le_bot_iff.mp (hPMK ▸ Subgroup.commutator_mono (inf_le_inf_left _ hCQH) le_rfl)
  have hK1 : K ≠ ⊥ := pResidualOf_ne_bot_of_benderM hG ht hH hs hM hp hp2 hπ
  have hNK : Subgroup.normalizer (K : Set G) = M := hG.normalizer_eq_of_isNormalIn hMco hKn hK1
  exact ⟨hKH, (Subgroup.le_centralizer_iff.mp hKP).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNK.le), hKP⟩

theorem bender1970_3_9_cores
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G} (hVP : V ≤ qCoreOf H p)
    {s : G} (hs : orderOf s = 2) (hsT : s ∈ (T : Subgroup G)) {M : Subgroup G}
    (hM : M ∈ benderM s)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) (hVM : V ≤ M)
    (habc : Bender39Conditions t H T V p) :
    pResidualOf (generalizedFittingSubgroupOf M) p ≤ H ∧ qCoreOf H p ≤ M :=
  (bender1970_3_9_cores_aux hG ht hH T htT hp hp2 hVP hs hsT hM hπ hVM habc).imp_right And.left

end CFSG.Walter
