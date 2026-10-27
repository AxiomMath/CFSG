module

public import CFSG.Walter.Bender1970.S3.CoreExchange
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_conj_le {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ A) : g ∈ Subgroup.normalizer (A : Set G) :=
  Bender35.mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]))

omit [Finite G] in
theorem isElemAbelian_zpowers {x : G} {p : ℕ} (hx : x ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem false_of_cores_swap (hG : BenderCounterexample G) {H M : Subgroup G} (hHco : IsCoatom H)
    (hMco : IsCoatom M) (hMH : M ≠ H) {p : ℕ} (hp : p.Prime)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (h1 : pResidualOf (generalizedFittingSubgroupOf M) p ≤ H) (h2 : qCoreOf H p ≤ M)
    (h3 : pResidualOf (generalizedFittingSubgroupOf H) p ≤ M) (h4 : qCoreOf M p ≤ H) : False := by
  have hFH : generalizedFittingSubgroupOf H ≤ M :=
    (generalizedFitting_le_qCoreOf_sup_pResidualOf H hp).trans (sup_le h2 h3)
  have hFM : generalizedFittingSubgroupOf M ≤ H :=
    (generalizedFitting_le_qCoreOf_sup_pResidualOf M hp).trans (sup_le h4 h1)
  obtain ⟨r, hr, hHr, -⟩ := bender1970_1_6_maximalSubgroups_pGroups hG.isSimpleGroup H M hHco
    hMco hMH.symm hFH hFM
  have := card_primesOfOrder_le_one_of_isPGroup hr hHr
  omega

theorem bender1970_3_9
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {V : Subgroup G} (hVP : V ≤ qCoreOf H p)
    {s : G} (hs : orderOf s = 2) (hsT : s ∈ (T : Subgroup G)) {M : Subgroup G}
    (hM : M ∈ benderM s) (hMH : M ≠ H)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) (hVM : V ≤ M)
    (habc : Bender39Conditions t H T V p) :
    pResidualOf (generalizedFittingSubgroupOf M) p ≤ H ∧ qCoreOf H p ≤ M ∧
      (V ≤ Subgroup.centralizer ({s} : Set G) →
        rank (qCoreOf H p) = 1 ∧ 1 < rank (qCoreOf M p)) := by
  obtain ⟨hKH, hPM, hKP⟩ :=
    bender1970_3_9_cores_aux hG ht hH T htT hp hp2 hVP hs hsT hM hπ hVM habc
  refine ⟨hKH, hPM, fun hVs => ?_⟩
  have := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set Q := qCoreOf M p with hQdef
  set K := pResidualOf (generalizedFittingSubgroupOf M) p with hKdef
  have hHco := isCoatom_of_mem_benderM hH
  have hMco := isCoatom_of_mem_benderM hM
  have hCH := centralizer_le_of_mem_benderM hH
  have hTM : (T : Subgroup G) ≤ M := hG.sylow_le_of_mem_benderM T hsT hM
  have htH : t ∈ H := mem_of_mem_benderM hH
  have htM : t ∈ M := hTM htT
  have hMA : IsAStar M := hG.isAStar_of_isCoatom hMco
  have hV1 : V ≠ ⊥ := habc.ne_bot hp.one_lt hHco.1
  have hCV : Subgroup.centralizer (V : Set G) ≤ H := habc.centralizer_le hp.one_lt
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hQp : IsPGroup p Q := qCoreOf_isPGroup M p
  have hPN : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hQN : M ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in M p)
  have hP1 : P ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVP))
  have hCPH : Subgroup.centralizer (P : Set G) ≤ H :=
    (Subgroup.centralizer_le_normalizer _).trans
      (hG.normalizer_eq_of_isNormalIn hHco (qCoreOf_normal_in H p) hP1).le
  have hrP1 : 1 ≤ rank P := one_le_rank_of_ne_bot hp hPp hP1
  have hswap : ∀ V' ≤ Q, V' ≤ H → Bender39Conditions s M T V' p → False := by
    intro V' hV'Q hV'H hc
    have hQ1 : Q ≠ ⊥ := fun h => hc.ne_bot hp.one_lt hMco.1 (le_bot_iff.mp (h ▸ hV'Q))
    have hπM := two_le_card_primes_of_benderM hG ht hH hs hM hp hp2 hπ hQ1
    obtain ⟨h3, h4⟩ := bender1970_3_9_cores hG hs hM T hsT hp hp2 hV'Q ht htT hH hπM hV'H hc
    exact false_of_cores_swap hG hHco hMco hMH hp hπ hKH hPM h3 h4
  by_cases hr : rank Q ≤ 2
  ·
    have hPQ : P ≤ Q := bender1970_1_4 hMA.1 hp hPM hPp hr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hKP))
    have hlt : rank P < rank Q := by
      by_contra hle
      push Not at hle
      have hΩP := omegaOneCenter_le_of_rank_le hp hQp hPQ hle
      have hQ1 : Q ≠ ⊥ := fun h => hP1 (le_bot_iff.mp (h ▸ hPQ))
      have hΩ1 := omegaOneCenter_ne_bot hp hQp hQ1
      have hΩn : IsNormalIn (omegaOneCenter Q p) M :=
        ⟨(omegaOneCenter_le Q p).trans (qCoreOf_normal_in M p).1, fun m hm z hz =>
          (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_omegaOneCenter (qCoreOf_normal_in M p) p hm) z).mp hz⟩
      have hCPM : Subgroup.centralizer (P : Set G) ≤ M :=
        (Subgroup.centralizer_le hΩP).trans ((Subgroup.centralizer_le_normalizer _).trans
          (hG.normalizer_eq_of_isNormalIn hMco hΩn hΩ1).le)
      obtain ⟨hPF, hPsn⟩ := Bender35.le_and_isSubnormal hp (le_refl P)
      have hEH : componentLayerOf H ≤ Subgroup.centralizer (P : Set G) :=
        (componentLayerOf_le_centralizer_fitting H).trans
          (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf H p hp))
      have hSM : subnormalHull H P ≤ M :=
        sup_le (sup_le hPM (hEH.trans hCPM)) (inf_le_right.trans hCPM)
      have hKF : K ≤ generalizedFittingSubgroupOf M := pResidualOf_le _ p
      have hEK : componentLayerOf M ≤ K :=
        perfect_le_pResidualOf_local _ _ p hp le_sup_right (componentLayerOf_isPerfect M)
      have hQKN : Q ≤ Subgroup.normalizer (K : Set G) :=
        (qCoreOf_normal_in M p).1.trans
          (le_normalizer_of_isNormalIn (pResidualOf_generalizedFitting_isNormalIn M p))
      have hS'F : (Q ⊓ H) ⊔ K ≤ generalizedFittingSubgroupOf M :=
        sup_le (inf_le_left.trans ((qCoreOf_le_fittingSubgroupOf M p hp).trans le_sup_left)) hKF
      have hS'C : generalizedFittingSubgroupOf M ⊓
          Subgroup.centralizer (((Q ⊓ H) ⊔ K : Subgroup G) : Set G) ≤ (Q ⊓ H) ⊔ K := by
        rintro x ⟨hxF, hxC⟩
        obtain ⟨a, ha, k, hk, rfl⟩ :=
          mem_sup_of_le_normalizer hQKN (generalizedFitting_le_qCoreOf_sup_pResidualOf M hp hxF)
        have haC : a ∈ Subgroup.centralizer (P : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hyS : y ∈ (Q ⊓ H) ⊔ K :=
            (le_sup_left : Q ⊓ H ≤ (Q ⊓ H) ⊔ K) ⟨hPQ hy, (qCoreOf_normal_in H p).1 hy⟩
          have h1 : y * (a * k) = (a * k) * y := (Subgroup.mem_centralizer_iff.mp hxC) y hyS
          have h2 : y * k = k * y := (Subgroup.mem_centralizer_iff.mp (hKP hk)) y hy
          calc y * a = y * (a * k) * k⁻¹ := by group
            _ = (a * k) * y * k⁻¹ := by rw [h1]
            _ = a * (k * y) * k⁻¹ := by group
            _ = a * (y * k) * k⁻¹ := by rw [h2]
            _ = a * y := by group
        exact Subgroup.mul_mem _ ((le_sup_left : Q ⊓ H ≤ _) ⟨ha, hCPH haC⟩)
          ((le_sup_right : K ≤ _) hk)
      exact hMH (bender1970_1_7_iii_equalityOfMaximal hG.isSimpleGroup H hHco (subnormalHull H P)
        (subnormalHull_le_generalizedFitting hPF) (isSubnormal_subnormalHull hPF hPsn)
        (generalizedFitting_inf_centralizer_subnormalHull_le H P) hSM hMco (Or.inl hπ)
        ⟨(Q ⊓ H) ⊔ K, sup_le inf_le_right hKH, hS'F,
          isSubnormal_of_componentLayerOf_le (hEK.trans le_sup_right) hS'F, hS'C⟩).symm
    exact ⟨le_antisymm (by omega) hrP1, by omega⟩
  push Not at hr
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have : rank Q ≤ 1 :=
      rank_le_one_of_card_le hp hQp (by rw [h, Subgroup.card_bot]; exact hp.one_lt.le)
    omega
  have hπM := two_le_card_primes_of_benderM hG ht hH hs hM hp hp2 hπ hQ1
  have hsM : s ∈ M := mem_of_mem_benderM hM
  have hcop2 : ∀ D ≤ Q, Nat.Coprime (Nat.card (Subgroup.zpowers s)) (Nat.card D) := by
    intro D hDQ
    obtain ⟨k, hk⟩ := (hQp.to_le hDQ).exists_card_eq
    rw [Nat.card_zpowers, hs, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hsQ : Q ≤ Subgroup.centralizer ({s} : Set G) := by
    by_contra hsQ
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
    have hsV : s ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hVs hv))
    set D := Pbar ⊓ Subgroup.centralizer (V : Set G) with hDdef
    have hsD : s ∈ Subgroup.normalizer (D : Set G) :=
      mem_normalizer_inf hsN (Subgroup.le_normalizer hsV)
    set Vb := ⁅D, Subgroup.zpowers s⁆ with hVbdef
    have hVb1 : Vb ≠ ⊥ := by
      intro h
      apply hPbart
      have hcopp : Nat.Coprime p (orderOf s) := by
        rw [hs]; exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      have hT := bender1970_1_1_thompson p hp V (Subgroup.zpowers s) Pbar (hPp.to_le hVP)
        (hQp.to_le hPbarQ) (Bender35.pResidualOf_zpowers_eq hp hcopp) (fun v hv => hPbarC (hVs hv))
        (Subgroup.zpowers_le.mpr hsN) (by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq']
          exact hVs) h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hT
    have hVbD : Vb ≤ D := commutator_zpowers_le_of_mem_normalizer hsD
    have hVbs : s ∈ Subgroup.normalizer (Vb : Set G) :=
      mem_normalizer_commutator hsD (Subgroup.le_normalizer (Subgroup.mem_zpowers s))
    have hVbA : Vb ∈ benderABar M := hPbarA Vb (hVbD.trans inf_le_left) hVb1 hVbs
    have hCVb : Subgroup.centralizer (Vb : Set G) ≤ M :=
      (Subgroup.centralizer_le_normalizer _).trans (hVbA.2.2.1 hπM)
    have hVbt : ⁅Vb, Subgroup.zpowers s⁆ = Vb :=
      le_antisymm (commutator_zpowers_le_of_mem_normalizer hVbs)
        (commutator_le_commutator_commutator D _ (Subgroup.zpowers_le.mpr hsD)
          (hcop2 D (inf_le_left.trans hPbarQ)))
    exact hswap Vb (hVbD.trans (inf_le_left.trans hPbarQ)) (hVbD.trans (inf_le_right.trans hCV))
      (Or.inl ⟨hCVb, hVbt⟩)
  obtain ⟨X, hXQ, hXcyc, hXexp, hXN⟩ :=
    exists_noncyclic_exponent_le hp hp2 hQp (not_isCyclic_of_two_le_rank hp hQp (by omega))
  set 𝔓 := P ⊔ Q with h𝔓def
  have hPQN : P ≤ Subgroup.normalizer (Q : Set G) := hPM.trans hQN
  have h𝔓 : IsPGroup p 𝔓 := hPp.to_sup_of_normal_right' hQp hPQN
  have hX𝔓 : X ≤ 𝔓 := hXQ.trans le_sup_right
  have h𝔓X : 𝔓 ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hPQN.trans hXN) (Subgroup.le_normalizer.trans hXN)
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht𝔓 : t ∈ Subgroup.normalizer (𝔓 : Set G) := mem_normalizer_sup (hPN htH) (hQN htM)
  have htX : t ∈ Subgroup.normalizer (X : Set G) := hXN (hQN htM)
  obtain ⟨z, hzX, x, hxX, hz1, hz𝔓, hxz, hx𝔓, htz, htx⟩ :=
    exists_typePP hp hp2 h𝔓 hX𝔓 h𝔓X hXexp hXcyc htt ht𝔓 htX
  set Vb := Subgroup.zpowers x ⊔ Subgroup.zpowers z with hVbdef
  have hzp : z ^ p = 1 := hXexp z hzX
  have hxp : x ^ p = 1 := hXexp x hxX
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ Subgroup.one_mem _)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzc : ∀ g ∈ 𝔓, g * z = z * g := fun g hg => (Subgroup.mem_centralizer_iff.mp hz𝔓) g hg
  have hxzc : Subgroup.zpowers x ≤
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq', Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hzc x (hX𝔓 hxX)
  have hVbel : CFSG.Open.IsElemAbelian p Vb :=
    isElemAbelian_sup (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hzp) hxzc
  have hdisj : Disjoint (Subgroup.zpowers z) (Subgroup.zpowers x) := by
    rw [disjoint_iff]
    set I := Subgroup.zpowers z ⊓ Subgroup.zpowers x with hI
    have hIz : I ≤ Subgroup.zpowers z := inf_le_left
    have hdvd : Nat.card I ∣ p := by
      rw [← hzo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hIz
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq I h
    · exfalso
      apply hxz
      have h1 : I = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge hIz (by rw [h, Nat.card_zpowers, hzo])
      have h2 : Subgroup.zpowers z ≤ Subgroup.zpowers x := h1 ▸ inf_le_right
      have h3 : Subgroup.zpowers z = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
      rw [h3]
      exact Subgroup.mem_zpowers x
  have hVbcard : Nat.card Vb = p ^ 2 := by
    rw [hVbdef, sup_comm, card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (hxzc.trans (Subgroup.centralizer_le_normalizer _)) hdisj, Nat.card_zpowers,
      Nat.card_zpowers, hzo, hxo, pow_two]
  have hVbQ : Vb ≤ Q :=
    sup_le (Subgroup.zpowers_le.mpr (hXQ hxX)) (Subgroup.zpowers_le.mpr (hXQ hzX))
  have hconj_mem : ∀ g, g * x * g⁻¹ ∈ Vb → g * z * g⁻¹ ∈ Vb →
      g ∈ Subgroup.normalizer (Vb : Set G) := by
    intro g hgx hgz
    refine mem_normalizer_of_map_conj_le ?_
    rw [hVbdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (Subgroup.zpowers_le.mpr hgx) (Subgroup.zpowers_le.mpr hgz)
  have hzVb : z ∈ Vb := (le_sup_right : Subgroup.zpowers z ≤ Vb) (Subgroup.mem_zpowers z)
  have hxVb : x ∈ Vb := (le_sup_left : Subgroup.zpowers x ≤ Vb) (Subgroup.mem_zpowers x)
  have h𝔓Vb : 𝔓 ≤ Subgroup.normalizer (Vb : Set G) := by
    intro g hg
    refine hconj_mem g ?_ ?_
    · have h1 : g * x * g⁻¹ = ⁅x, g⁆⁻¹ * x := by simp only [commutatorElement_def]; group
      rw [h1]
      exact Vb.mul_mem ((le_sup_right : Subgroup.zpowers z ≤ Vb)
        (Subgroup.inv_mem _ (hx𝔓 g hg))) hxVb
    · rw [hzc g hg, mul_inv_cancel_right]
      exact hzVb
  have htVb : t ∈ Subgroup.normalizer (Vb : Set G) := by
    refine hconj_mem t htx ?_
    exact (le_sup_right : Subgroup.zpowers z ≤ Vb)
      ((Subgroup.mem_normalizer_iff.mp htz z).mp (Subgroup.mem_zpowers z))
  have hCVb : ∀ y ∈ 𝔓, y ∈ Subgroup.centralizer ({x} : Set G) →
      y ∈ Subgroup.centralizer (Vb : Set G) := by
    intro y hy hyx
    have h1 : Vb ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hyx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzc y hy).symm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hv)
  obtain ⟨E, hEQ, hE, hEcard⟩ := exists_isElemAbelian_of_le_rank hp hQp (k := 3) hr
  have hE𝔓 : E ≤ 𝔓 := hEQ.trans le_sup_right
  have hhomE := card_le_and_commutator_le_of_commutator_mem hz𝔓 hx𝔓 hE𝔓
  set E₀ := E ⊓ Subgroup.centralizer ({x} : Set G) with hE₀def
  have hE₀V : E₀ ≤ Subgroup.centralizer (Vb : Set G) := fun y hy => hCVb y (hE𝔓 hy.1) hy.2
  have hE₀el : CFSG.Open.IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hE.2 y hy.1⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
    exact h
  have hE' := isElemAbelian_sup hE₀el hVbel hE₀V
  have hE'Q : E₀ ⊔ Vb ≤ Q := sup_le (inf_le_left.trans hEQ) hVbQ
  have hE'card : p ^ 3 ≤ Nat.card (E₀ ⊔ Vb : Subgroup G) := by
    by_cases hEx : E ≤ Subgroup.centralizer ({x} : Set G)
    · have : E ≤ E₀ ⊔ Vb := (le_inf le_rfl hEx).trans le_sup_left
      exact hEcard.trans (Subgroup.card_le_of_le this)
    · have hVbE₀ : ¬ Vb ≤ E₀ := by
        intro h
        apply hEx
        intro e he
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨x, (h hxVb).1⟩)
      have hlt : E₀ < E₀ ⊔ Vb :=
        lt_of_le_of_ne le_sup_left fun h => hVbE₀ (h ▸ le_sup_right)
      have h1 := card_ge_of_lt' hp (hQp.to_le hE'Q) hlt
      have h2 := hhomE.1
      rw [Nat.card_zpowers, hzo] at h2
      exact hEcard.trans (h2.trans h1)
  have hE'3 : 3 ≤ rank (E₀ ⊔ Vb) := by
    obtain ⟨k, hk⟩ := (hQp.to_le hE'Q).exists_card_eq
    have hk3 : 3 ≤ k := by
      rw [hk] at hE'card
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hE'card
    exact hk3.trans (le_rank hp le_rfl hE' hk)
  have hCv : ∀ v ∈ Vb, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ M := fun v hv hv1 =>
    bender1970_3_7 hG hs hM hp hp2 hsQ hE'Q hE' hE'3 ((le_sup_right : Vb ≤ E₀ ⊔ Vb) hv) hv1
  have hVbH : ¬ Vb ≤ H := by
    intro h
    refine hswap Vb hVbQ h (Or.inr (Or.inl ⟨fun v hv hv1 => ⟨?_, hCv v hv hv1⟩, hVbel, hVbcard⟩))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hsQ (hVbQ hv))).symm
  have hhomP := card_le_and_commutator_le_of_commutator_mem hz𝔓 hx𝔓 (le_sup_left : P ≤ 𝔓)
  rcases habc with ⟨-, hVt⟩ | ⟨hVv, -, hVcard⟩ | ⟨-, -, W, hWT, hW, hWC⟩
  ·
    have hP'C : ⁅P, P⁆ ≤ Subgroup.centralizer (Vb : Set G) := fun y hy =>
      hCVb y ((le_sup_left : P ≤ 𝔓) (Bender35.commutator_self_le P hy)) (hhomP.2 hy)
    have hP' : ⁅P, P⁆ = ⊥ := by
      by_contra hP'1
      obtain ⟨hP'F, hP'sn⟩ := Bender35.le_and_isSubnormal hp (Bender35.commutator_self_le P)
      have hP'A := bender1970_3_1_i hG ht hH hP'1 hP'F hP'sn fun c hc =>
        mem_normalizer_commutator (hPN (hCH hc)) (hPN (hCH hc))
      exact hVbH ((Subgroup.le_centralizer_iff.mp hP'C).trans
        ((Subgroup.centralizer_le_normalizer _).trans (hP'A.2.2.1 hπ)))
    have hPab : P ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hP'
    have htPN := hPN htH
    set U := ⁅P, Subgroup.zpowers t⁆ with hUdef
    have hUP : U ≤ P := commutator_zpowers_le_of_mem_normalizer htPN
    have hU1 : U ≠ ⊥ := by
      intro h
      apply hV1
      rw [← hVt]
      exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono hVP le_rfl)
    have hUC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
      intro c hc
      refine mem_normalizer_commutator (hPN (hCH hc)) (Subgroup.centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq']
      exact hc
    obtain ⟨hUF, hUsn⟩ := Bender35.le_and_isSubnormal hp hUP
    have hUA := bender1970_3_1_i hG ht hH hU1 hUF hUsn hUC
    have hcopP : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card P) := by
      obtain ⟨k, hk⟩ := hPp.exists_card_eq
      rw [Nat.card_zpowers, ht, hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hUt : ⁅U, Subgroup.zpowers t⁆ = U :=
      le_antisymm (commutator_zpowers_le_of_mem_normalizer (hUC htC))
        (commutator_le_commutator_commutator P _ (Subgroup.zpowers_le.mpr htPN) hcopP)
    have hCP : P ⊓ Subgroup.centralizer (Vb : Set G) = ⊥ := by
      by_contra hCP1
      have htCP : t ∈ Subgroup.normalizer
          ((P ⊓ Subgroup.centralizer (Vb : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf htPN (Bender35.mem_normalizer_centralizer htVb)
      obtain ⟨hF, hsn⟩ := Bender35.le_and_isSubnormal hp (inf_le_left :
        P ⊓ Subgroup.centralizer (Vb : Set G) ≤ P)
      have hA := bender1970_3_1_ii hG ht hH hCP1 hF hsn htCP hUA
        (hUP.trans (hPab.trans (Subgroup.centralizer_le inf_le_left))) hUt
      exact hVbH ((Subgroup.le_centralizer_iff.mp inf_le_right).trans
        ((Subgroup.centralizer_le_normalizer _).trans (hA.2.2.1 hπ)))
    have hPcard : Nat.card P ≤ p := by
      have h1 := hhomP.1
      have h2 : P ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
        le_bot_iff.mp (hCP ▸ le_inf inf_le_left fun y hy =>
          hCVb y ((le_sup_left : P ≤ 𝔓) hy.1) hy.2)
      rw [h2, Subgroup.card_bot, Nat.card_zpowers, hzo, mul_one] at h1
      exact h1
    exact ⟨le_antisymm (rank_le_one_of_card_le hp hPp hPcard) hrP1, by omega⟩
  ·
    exfalso
    have hhomV := card_le_and_commutator_le_of_commutator_mem hz𝔓 hx𝔓
      (hVP.trans (le_sup_left : P ≤ 𝔓))
    have h1 : V ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      intro h
      have h2 := hhomV.1
      rw [h, Subgroup.card_bot, Nat.card_zpowers, hzo, hVcard, mul_one] at h2
      have := hp.one_lt
      nlinarith
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
    have hvC := hCVb v ((hVP.trans (le_sup_left : P ≤ 𝔓)) v.2.1) v.2.2
    apply hVbH
    have h2 : Vb ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hvC) w hw
    exact h2.trans (hVv v v.2.1 fun h => hv1 (Subtype.ext h)).2
  ·
    exfalso
    have hWcomm : IsMulCommutative W :=
      ⟨⟨fun a b => mul_comm_of_exponent_two hW.exponent_two a b⟩⟩
    have hWexp : ∀ x ∈ W, x ^ 2 = 1 := fun x hx => by
      have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : W)
      rw [hW.exponent_two] at h
      exact congrArg Subtype.val h
    have hWcard : 2 ^ 2 ≤ Nat.card W := by rw [hW.card_four]; norm_num
    have hQ2 : ¬ 2 ∣ Nat.card Q := by
      intro h
      obtain ⟨k, hk⟩ := hQp.exists_card_eq
      rw [hk] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm
    apply hVbH
    refine hVbQ.trans ((le_iSup_inf_centralizer Nat.prime_two hWcomm hWexp hWcard
      ((hWT.trans hTM).trans hQN) hQ2).trans ?_)
    exact iSup₂_le fun w hw => iSup_le fun hw1 => inf_le_right.trans (hWC w hw hw1)

end CFSG.Walter
