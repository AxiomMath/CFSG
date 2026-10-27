module

public import CFSG.Walter.Bender1970.S3.TransitivityMain

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaOneCenter (P : Subgroup G) (p : ℕ) : Subgroup G where
  carrier := {z | z ∈ P ∧ z ∈ Subgroup.centralizer (P : Set G) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haP, haC, hap⟩ ⟨hbP, hbC, hbp⟩
    refine ⟨P.mul_mem haP hbP, Subgroup.mul_mem _ haC hbC, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haP
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨P.one_mem, Subgroup.one_mem _, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haP, haC, hap⟩
    exact ⟨P.inv_mem haP, Subgroup.inv_mem _ haC, by rw [inv_pow, hap, inv_one]⟩

omit [Finite G] in
theorem omegaOneCenter_le (P : Subgroup G) (p : ℕ) : omegaOneCenter P p ≤ P := fun _ h => h.1

omit [Finite G] in
theorem omegaOneCenter_le_centralizer (P : Subgroup G) (p : ℕ) :
    omegaOneCenter P p ≤ Subgroup.centralizer (P : Set G) := fun _ h => h.2.1

omit [Finite G] in
theorem pow_eq_one_of_mem_omegaOneCenter {P : Subgroup G} {p : ℕ} {z : G}
    (hz : z ∈ omegaOneCenter P p) : z ^ p = 1 := hz.2.2

theorem omegaOneCenter_ne_bot {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPp : IsPGroup p P)
    (hP1 : P ≠ ⊥) : omegaOneCenter P p ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have hZ : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (hPp.to_subgroup (Subgroup.center P)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center P) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact lt_irrefl 1 h1
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) p hdvd
  intro h
  have hmem : (((z : Subgroup.center P) : P) : G) ∈ omegaOneCenter P p := by
    refine ⟨(z : P).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center P => ((w : P) : G)) h1
      simpa using h2
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact hp.one_lt.ne hz

omit [Finite G] in
theorem le_normalizer_omegaOneCenter {H P : Subgroup G} (hP : IsNormalIn P H) (p : ℕ) :
    H ≤ Subgroup.normalizer (omegaOneCenter P p : Set G) := by
  have key : ∀ g ∈ H, ∀ z ∈ omegaOneCenter P p, g * z * g⁻¹ ∈ omegaOneCenter P p := by
    rintro g hg z ⟨hzP, hzC, hzp⟩
    refine ⟨hP.2 g hg z hzP, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Bender35.mem_normalizer_centralizer
        (le_normalizer_of_isNormalIn hP hg)) z).mp hzC
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key h hh z, fun hz => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hz
  simpa [mul_assoc] using this

theorem bender1970_3_7_of_le_centralizer
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : IsCoatom H)
    (hCH : Subgroup.centralizer ({t} : Set G) ≤ H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htP : qCoreOf H p ≤ Subgroup.centralizer ({t} : Set G))
    (htF : generalizedFittingSubgroupOf H ≤ Subgroup.centralizer ({t} : Set G))
    {V : Subgroup G} (hVP : V ≤ qCoreOf H p) (hVcomm : IsMulCommutative V)
    (hVexp : ∀ x ∈ V, x ^ p = 1) (hV3 : p ^ 3 ≤ Nat.card V) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) : Subgroup.centralizer ({v} : Set G) ≤ H := by
  set P := qCoreOf H p with hPdef
  set Ω := omegaOneCenter P p with hΩdef
  set V' := V ⊔ Ω with hV'def
  have hPn := qCoreOf_normal_in H p
  have hΩH : H ≤ Subgroup.normalizer (Ω : Set G) := le_normalizer_omegaOneCenter hPn p
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV3
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  have hP1 : P ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVP))
  have hΩ1 : Ω ≠ ⊥ := omegaOneCenter_ne_bot hp (qCoreOf_isPGroup H p) hP1
  have hΩn : IsNormalIn Ω H := ⟨(omegaOneCenter_le P p).trans hPn.1, fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.mp (hΩH hh) z).mp hz⟩
  have hNΩ : Subgroup.normalizer (Ω : Set G) = H := hG.normalizer_eq_of_isNormalIn hH hΩn hΩ1
  have hV'P : V' ≤ P := sup_le hVP (omegaOneCenter_le P p)
  have hΩV : Ω ≤ Subgroup.centralizer (V : Set G) :=
    (omegaOneCenter_le_centralizer P p).trans (Subgroup.centralizer_le hVP)
  have hVV : V ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hVcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hΩΩ : Ω ≤ Subgroup.centralizer (Ω : Set G) :=
    (omegaOneCenter_le_centralizer P p).trans (Subgroup.centralizer_le (omegaOneCenter_le P p))
  have hV'C : V' ≤ Subgroup.centralizer (V' : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hVV hΩV
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (Subgroup.le_centralizer_iff.mp hΩV) hΩΩ
  have hV'comm : IsMulCommutative V' :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hV'C b.2)) a a.2)⟩⟩
  have hV'exp : ∀ x ∈ V', x ^ p = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      mem_sup_of_le_normalizer (hVP.trans (hPn.1.trans hΩH)) hx
    have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp (hΩV hb)) a ha
    rw [hcomm.mul_pow, hVexp a ha, pow_eq_one_of_mem_omegaOneCenter hb, one_mul]
  have hV'3 : p ^ 3 ≤ Nat.card V' := hV3.trans (Subgroup.card_le_of_le le_sup_left)
  have hCV' : Subgroup.centralizer (V' : Set G) ≤ H :=
    (Subgroup.centralizer_le (le_sup_right : Ω ≤ V')).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNΩ.le)
  exact (Bender37.mk hG t ht H hH hCH p hp hp2 V' hV'P hV'comm hV'exp hV'3 (hV'P.trans htP)
    htF hCV').centralizer_le (le_sup_left (b := Ω) hv) hv1

theorem qCoreOf_two_le_centralizer (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {X : Subgroup G} (htX : t ∈ X) : qCoreOf X 2 ≤ Subgroup.centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN : t ∈ Subgroup.normalizer (qCoreOf X 2 : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in X 2) htX
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hP : IsPGroup 2 (Subgroup.zpowers t ⊔ qCoreOf X 2 : Subgroup G) :=
    htp.to_sup_of_normal_right' (qCoreOf_isPGroup X 2) (Subgroup.zpowers_le.mpr htN)
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hTab := hG.hasAbelianSylowTwo T
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hTab.is_comm.comm
    ⟨x, hT ((le_sup_right : qCoreOf X 2 ≤ Subgroup.zpowers t ⊔ qCoreOf X 2) hx)⟩
    ⟨t, hT ((le_sup_left : Subgroup.zpowers t ≤ Subgroup.zpowers t ⊔ qCoreOf X 2)
      (Subgroup.mem_zpowers t))⟩)

theorem bender1970_3_7_of_not_le_centralizer
    (hG : BenderCounterexample G) {t : G}
    (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime)
    (htP : qCoreOf H p ≤ Subgroup.centralizer ({t} : Set G))
    (htF : ¬ generalizedFittingSubgroupOf H ≤ Subgroup.centralizer ({t} : Set G)) {v : G}
    (hv : v ∈ qCoreOf H p) (hv1 : v ≠ 1) : Subgroup.centralizer ({v} : Set G) ≤ H := by
  have hHco := isCoatom_of_mem_benderM hH
  have hCH := centralizer_le_of_mem_benderM hH
  have htH := mem_of_mem_benderM hH
  have hHA := hG.isAStar_of_isCoatom hHco
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set Vv := Subgroup.zpowers v with hVvdef
  have hVvP : Vv ≤ qCoreOf H p := Subgroup.zpowers_le.mpr hv
  have hVv1 : Vv ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
  obtain ⟨hVvF, hVvsn⟩ := Bender35.le_and_isSubnormal hp hVvP
  have hVvt : t ∈ Subgroup.normalizer (Vv : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (htP hv)).symm
  obtain ⟨U, hUA, hUV, hUt⟩ : ∃ U ∈ benderABar H, U ≤ Subgroup.centralizer (Vv : Set G) ∧
      ⁅U, Subgroup.zpowers t⁆ = U := by
    by_cases hF : ∀ q : ℕ, q.Prime → qCoreOf H q ≤ Subgroup.centralizer ({t} : Set G)
    ·
      have hFt : CFSG.fittingSubgroupOf H ≤ Subgroup.centralizer ({t} : Set G) := by
        rw [(show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
        exact iSup_le fun q => hF q.1.1 (Nat.prime_of_mem_primeFactors q.1.2)
      have hEt : ¬ componentLayerOf H ≤ Subgroup.centralizer ({t} : Set G) :=
        fun h => htF (sup_le hFt h)
      set 𝒦 := {L : Subgroup G | IsComponentOf L H ∧ ¬ L ≤ Subgroup.centralizer ({t} : Set G)}
        with h𝒦
      obtain ⟨L₀, hL₀, hL₀t⟩ : ∃ L, IsComponentOf L H ∧
          ¬ L ≤ Subgroup.centralizer ({t} : Set G) := by
        by_contra hcon
        push Not at hcon
        exact hEt (sSup_le fun L hL => hcon L hL)
      have htL : ∀ L, IsComponentOf L H → t ∈ Subgroup.normalizer (L : Set G) := fun L hL =>
        mem_normalizer_of_isComponentOf_of_orderOf hHA hL htH ht
      have hLt : ∀ L ∈ 𝒦, L ≤ ⁅L, Subgroup.zpowers t⁆ := by
        intro L hL
        rcases commutator_eq_bot_or_le_of_isComponentOf hL.1
            (Subgroup.zpowers_le.mpr (htL L hL.1)) with h | h
        · exfalso
          apply hL.2
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq'] at h
          exact h
        · exact h
      set U := sSup 𝒦 with hUdef
      have hUE : U ≤ componentLayerOf H :=
        sSup_le fun L hL => le_sSup (s := {E : Subgroup G | IsComponentOf E H}) hL.1
      have hU1 : U ≠ ⊥ := fun h => Bender37.ne_bot_of_isComponentOf hL₀
        (le_bot_iff.mp (h ▸ le_sSup (s := 𝒦) ⟨hL₀, hL₀t⟩))
      have hUF : U ≤ generalizedFittingSubgroupOf H := hUE.trans le_sup_right
      have hFN : generalizedFittingSubgroupOf H ≤ Subgroup.normalizer (U : Set G) :=
        fun x hx => mem_normalizer_sSup fun L hL =>
          Bender37.generalizedFitting_le_normalizer_component hL.1 hx
      have hUsn : (U.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal :=
        isSubnormal_subgroupOf_of_le_normalizer hUF hFN
      have hUtN : t ∈ Subgroup.normalizer (U : Set G) :=
        mem_normalizer_sSup fun L hL => htL L hL.1
      have hmap : ∀ g ∈ Subgroup.centralizer ({t} : Set G), ∀ L ∈ 𝒦,
          L.map (MulAut.conj g).toMonoidHom ∈ 𝒦 := by
        intro g hg L hL
        refine ⟨fstar_isComponentOf_conjugateSubgroup_of_mem hL.1 g (hCH hg), fun h => hL.2 ?_⟩
        have h' := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
        rwa [map_conj_map_conj_inv, map_conj_eq_self_of_mem (Subgroup.inv_mem _ hg)] at h'
      have hUC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (U : Set G) :=
        fun c hc => mem_normalizer_sSup_of_map_mem (hmap c hc) (hmap c⁻¹ (Subgroup.inv_mem _ hc))
      refine ⟨U, bender1970_3_1_i hG ht hH hU1 hUF hUsn hUC, ?_, ?_⟩
      · exact hUE.trans ((componentLayerOf_le_centralizer_fitting H).trans
          (Subgroup.centralizer_le (hVvP.trans (qCoreOf_le_fittingSubgroupOf H p hp))))
      · exact le_antisymm (commutator_zpowers_le_of_mem_normalizer hUtN)
          (sSup_le fun L hL => (hLt L hL).trans (Subgroup.commutator_mono (le_sSup hL) le_rfl))
    ·
      push Not at hF
      obtain ⟨q, hq, hqt⟩ := hF
      have hqp : q ≠ p := fun h => hqt (h ▸ htP)
      have hq2 : q ≠ 2 := by
        rintro rfl
        exact hqt (qCoreOf_two_le_centralizer hG ht htH)
      have htN : t ∈ Subgroup.normalizer (qCoreOf H q : Set G) :=
        le_normalizer_of_isNormalIn (qCoreOf_normal_in H q) htH
      set U := ⁅qCoreOf H q, Subgroup.zpowers t⁆ with hUdef
      have hUO : U ≤ qCoreOf H q := commutator_zpowers_le_of_mem_normalizer htN
      have hU1 : U ≠ ⊥ := by
        intro h
        apply hqt
        rw [hUdef, Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq'] at h
        exact h
      have hUF : U ≤ generalizedFittingSubgroupOf H :=
        hUO.trans ((qCoreOf_le_fittingSubgroupOf H q hq).trans le_sup_left)
      have hUsn : (U.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal :=
        isSubnormal_subgroupOf_trans hUO
          (isSubnormal_subgroupOf_of_le_normalizer hUO (Subgroup.normalizer_commutator_ge_left _ _))
          (isSubnormal_subgroupOf_of_isNormalIn (qCoreOf_isNormalIn_generalizedFitting H hq))
      have hUC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
        intro c hc
        refine mem_normalizer_commutator
          (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q) (hCH hc))
          (Subgroup.centralizer_le_normalizer _ ?_)
        rw [centralizer_zpowers_eq']
        exact hc
      have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card (qCoreOf H q)) := by
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H q).exists_card_eq
        rw [Nat.card_zpowers, ht, hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
      refine ⟨U, bender1970_3_1_i hG ht hH hU1 hUF hUsn hUC, ?_, ?_⟩
      · exact hUO.trans ((qCoreOf_centralizer_of_ne H hp hq (Ne.symm hqp)).trans
          (Subgroup.centralizer_le hVvP))
      · exact le_antisymm (commutator_zpowers_le_of_mem_normalizer (hUC htC))
          (commutator_le_commutator_commutator _ _ (Subgroup.zpowers_le.mpr htN) hcop)
  have hVvA := bender1970_3_1_ii hG ht hH hVv1 hVvF hVvsn hVvt hUA hUV hUt
  have hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) := by
    by_contra hlt
    push Not at hlt
    have : Fact p.Prime := ⟨hp⟩
    have hvF : v ∈ generalizedFittingSubgroupOf H := hVvF (Subgroup.mem_zpowers v)
    have hpπ : p ∈ primesOfOrder (generalizedFittingSubgroupOf H) := by
      show p ∈ (Nat.card (generalizedFittingSubgroupOf H)).primeFactors
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, Nat.card_pos.ne'⟩
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H p).exists_card_eq
      have h1 : orderOf v ∣ p ^ k := by
        rw [← hk]
        exact Subgroup.orderOf_dvd_natCard _ hv
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp h1
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hm
        exact hv1 hm
      exact (dvd_pow_self p hm0).trans (hm ▸ Subgroup.orderOf_dvd_natCard _ hvF)
    have hfin : (primesOfOrder (generalizedFittingSubgroupOf H)).Finite :=
      (Nat.card (generalizedFittingSubgroupOf H)).primeFactors.finite_toSet
    have hsub : primesOfOrder (generalizedFittingSubgroupOf H) ⊆ {p} := by
      intro r hr
      rw [Nat.card_coe_set_eq] at hlt
      exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one hfin).mp (by omega) r hr p hpπ)
    have hFp : IsPGroup p (generalizedFittingSubgroupOf H) :=
      isPGroup_of_primesOfOrder_subset hp hsub
    have hFn := generalizedFittingSubgroupOf_isNormalIn H
    apply htF
    refine (le_qCoreOf_of_normal_isPGroup H _ p hFn.1 ?_ hFp).trans htP
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFn.1).mpr (le_normalizer_of_isNormalIn hFn)
  exact (centralizer_singleton_le_normalizer_zpowers v).trans (hVvA.2.2.1 hπ)

theorem bender1970_3_7
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htP : qCoreOf H p ≤ Subgroup.centralizer ({t} : Set G)) {V : Subgroup G}
    (hVP : V ≤ qCoreOf H p) (hVel : CFSG.Open.IsElemAbelian p V) (hV3 : 3 ≤ rank V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : Subgroup.centralizer ({v} : Set G) ≤ H := by
  by_cases htF : generalizedFittingSubgroupOf H ≤ Subgroup.centralizer ({t} : Set G)
  · have hVp : IsPGroup p V := (qCoreOf_isPGroup H p).to_le hVP
    have hcard : p ^ 3 ≤ Nat.card V := by
      rw [rank_eq_pRank_of_isPGroup hp hVp] at hV3
      obtain ⟨E, hEV, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt V
      calc p ^ 3 ≤ p ^ CFSG.Open.pRank p V := Nat.pow_le_pow_right hp.pos hV3
        _ = Nat.card E := hE.symm
        _ ≤ Nat.card V := Subgroup.card_le_of_le hEV
    exact bender1970_3_7_of_le_centralizer hG ht (isCoatom_of_mem_benderM hH)
      (centralizer_le_of_mem_benderM hH) hp hp2 htP htF hVP hVel.1 hVel.2 hcard hv hv1
  · exact bender1970_3_7_of_not_le_centralizer hG ht hH hp htP htF (hVP hv) hv1

end CFSG.Walter
