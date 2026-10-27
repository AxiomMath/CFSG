module

public import CFSG.Walter.Bender1970.S3.Transitivity

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pResidualOf_generalizedFitting_le (A : Subgroup G) {p : ℕ} (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      sSup {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf A q} ⊔ componentLayerOf A := by
  set F := generalizedFittingSubgroupOf A with hFdef
  set N₁ := sSup {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf A q} with hN₁
  set N := N₁ ⊔ componentLayerOf A with hNdef
  have hFA : F ≤ A := (generalizedFittingSubgroupOf_isNormalIn A).1
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    intro a ha
    refine mem_normalizer_sup (mem_normalizer_sSup
      (𝒦 := {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf A q}) ?_)
      (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn A) ha)
    rintro _ ⟨q, -, -, rfl⟩
    exact le_normalizer_of_isNormalIn (qCoreOf_normal_in A q) ha
  have hNF : N ≤ F := by
    refine sup_le (sSup_le ?_) le_sup_right
    rintro _ ⟨q, hq, -, rfl⟩
    exact (qCoreOf_le_fittingSubgroupOf A q hq).trans le_sup_left
  have hFle : F ≤ qCoreOf A p ⊔ N := by
    refine sup_le ?_ (le_sup_right.trans le_sup_right)
    rw [fittingSubgroupOf_eq_iSup_qCoreOf A]
    refine iSup_le fun q => ?_
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact le_sup_left
    · exact (le_sSup (s := {R | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ R = qCoreOf A q})
        ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2, hqp, rfl⟩).trans
        (le_sup_left.trans le_sup_right)
  have hNn : (N.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNF).mpr (hFA.trans hAN)
  refine pResidualOf_le_of_quotient_isPGroup F N p hp hNF hNn fun g => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  have hON : qCoreOf A p ≤ Subgroup.normalizer (N : Set G) := (qCoreOf_normal_in A p).1.trans hAN
  obtain ⟨a, ha, n, hn, hx⟩ := mem_sup_of_le_normalizer hON (hFle x.2)
  have haF : a ∈ F := (qCoreOf_le_fittingSubgroupOf A p hp).trans le_sup_left ha
  have hnF : n ∈ F := hNF hn
  obtain ⟨k, hk⟩ := (qCoreOf_isPGroup A p) ⟨a, ha⟩
  refine ⟨k, ?_⟩
  have hxeq : x = ⟨a, haF⟩ * ⟨n, hnF⟩ := Subtype.ext hx.symm
  have hn1 : (QuotientGroup.mk (⟨n, hnF⟩ : F) : F ⧸ N.subgroupOf F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
  have hak : (⟨a, haF⟩ : F) ^ p ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  rw [hxeq, QuotientGroup.mk_mul, hn1, mul_one, ← QuotientGroup.mk_pow, hak, QuotientGroup.mk_one]

theorem pResidualOf_generalizedFitting_le_centralizer (A : Subgroup G) {p : ℕ} (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      Subgroup.centralizer (qCoreOf A p : Set G) := by
  refine (pResidualOf_generalizedFitting_le A hp).trans (sup_le (sSup_le ?_) ?_)
  · rintro _ ⟨q, hq, hqp, rfl⟩
    exact qCoreOf_centralizer_of_ne A hp hq (Ne.symm hqp)
  · exact (componentLayerOf_le_centralizer_fitting A).trans
      (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf A p hp))

theorem commutator_eq_bot_of_pResidual {K A B : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hK : pResidualOf K p = K) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) (hAB : A ≤ B)
    (hKBp : IsPGroup p (K ⊓ B : Subgroup G))
    (hKBc : K ⊓ B ≤ Subgroup.centralizer (K : Set G)) : ⁅K, A⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro k hk a ha
  have hmem : ∀ k ∈ K, ⁅k, a⁆ ∈ K ⊓ B := by
    intro k hk
    refine ⟨?_, ?_⟩
    · have h1 : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [h1]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hAK ha) k⁻¹).mp (K.inv_mem hk))
    · rw [commutatorElement_def]
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKB hk) a).mp (hAB ha)) (B.inv_mem (hAB ha))
  let φ : K →* G :=
    { toFun := fun k => ⁅(k : G), a⁆
      map_one' := by simp
      map_mul' := fun k₁ k₂ => by
        have h₂ := hmem _ k₂.2
        have h₁ := hmem _ k₁.2
        have hc₂ : (k₁ : G) * ⁅(k₂ : G), a⁆ = ⁅(k₂ : G), a⁆ * k₁ :=
          ((Subgroup.mem_centralizer_iff.mp (hKBc h₂)) k₁ k₁.2)
        have hc₁₂ : ⁅(k₁ : G), a⁆ * ⁅(k₂ : G), a⁆ = ⁅(k₂ : G), a⁆ * ⁅(k₁ : G), a⁆ :=
          ((Subgroup.mem_centralizer_iff.mp (hKBc h₂)) _ h₁.1)
        show ⁅(k₁ : G) * k₂, a⁆ = ⁅(k₁ : G), a⁆ * ⁅(k₂ : G), a⁆
        calc ⁅(k₁ : G) * k₂, a⁆ = (k₁ : G) * ⁅(k₂ : G), a⁆ * (k₁ : G)⁻¹ * ⁅(k₁ : G), a⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅(k₂ : G), a⁆ * ⁅(k₁ : G), a⁆ := by rw [hc₂]; group
          _ = ⁅(k₁ : G), a⁆ * ⁅(k₂ : G), a⁆ := hc₁₂.symm }
  have hrange : φ.range ≤ K ⊓ B := by
    rintro _ ⟨k, rfl⟩
    exact hmem _ k.2
  have hidx : ∃ n : ℕ, φ.ker.index = p ^ n := by
    rw [Subgroup.index_ker]
    have hrp : IsPGroup p φ.range := hKBp.to_le hrange
    exact hrp.exists_card_eq
  have h1 := pResidualOf_le_of_normal_index K p φ.ker inferInstance hidx
  rw [hK] at h1
  obtain ⟨k', hk', hk'eq⟩ := h1 hk
  have hk'' : k' ∈ φ.ker := hk'
  rw [MonoidHom.mem_ker] at hk''
  rw [Subgroup.mem_bot, ← hk'eq]
  exact hk''

theorem inf_centralizer_ne_bot_of_isPGroup {A B : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hB1 : B ≠ ⊥) : B ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set X := A ⊔ B with hX
  have hXp : IsPGroup p X := hA.to_sup_of_normal_right' hB hAB
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (B : Set G) := sup_le hAB Subgroup.le_normalizer
  have hBn : (B.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr hXN
  have : Group.IsNilpotent X := hXp.isNilpotent
  have hB1' : B.subgroupOf X ≠ ⊥ := by
    intro h
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have : (⟨b, hBX hb⟩ : X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hB1'
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  obtain ⟨hyB, hyZ⟩ := y.2
  intro h'
  apply hy1
  have hyZ' : (y : X) ∈ Subgroup.center X := hyZ
  have hmem : ((y : X) : G) ∈ B ⊓ Subgroup.centralizer (A : Set G) := by
    refine ⟨Subgroup.mem_subgroupOf.mp hyB, ?_⟩
    show ((y : X) : G) ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyZ')
      ⟨a, (le_sup_left : A ≤ A ⊔ B) ha⟩)
  rw [h', Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

omit [Finite G] in
theorem isElemAbelian_sup {A B : Subgroup G} {p : ℕ} (hA : CFSG.Open.IsElemAbelian p A)
    (hB : CFSG.Open.IsElemAbelian p B) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    CFSG.Open.IsElemAbelian p (A ⊔ B) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hBB : B ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hC : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hAA (Subgroup.le_centralizer_iff.mp hAB)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hAB hBB
  refine ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hC b.2)) a a.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    mem_sup_of_le_normalizer (hAB.trans (Subgroup.centralizer_le_normalizer _)) hx
  have hcomm : Commute a b := ((Subgroup.mem_centralizer_iff.mp (hAB ha)) b hb).symm
  rw [hcomm.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem one_le_rank_of_ne_bot {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPp : IsPGroup p P)
    (hP1 : P ≠ ⊥) : 1 ≤ rank P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hPp).mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p
    (by rw [hcard]; exact dvd_pow_self p hn.ne')
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  refine le_rank hp (E := Subgroup.zpowers (x : G)) (Subgroup.zpowers_le.mpr x.2) ⟨?_, ?_⟩
    (k := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  · exact ⟨⟨fun a b => Subtype.ext (by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self (x : G) i j).eq)⟩⟩
  · intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]

theorem rank_le_one_of_card_le {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hPp : IsPGroup p P)
    (hcard : Nat.card P ≤ p) : rank P ≤ 1 := by
  rw [rank_eq_pRank_of_isPGroup hp hPp]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEP _ => ?_
  rw [pow_one]
  exact (Subgroup.card_le_of_le hEP).trans hcard

theorem exists_isElemAbelian_of_le_rank {Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQp : IsPGroup p Q) {k : ℕ} (hk : k ≤ rank Q) :
    ∃ E ≤ Q, CFSG.Open.IsElemAbelian p E ∧ p ^ k ≤ Nat.card E := by
  rw [rank_eq_pRank_of_isPGroup hp hQp] at hk
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Q
  exact ⟨E, hEQ, hE, hcard ▸ Nat.pow_le_pow_right hp.pos hk⟩

theorem not_isCyclic_of_two_le_rank {Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hQp : IsPGroup p Q)
    (h2 : 2 ≤ rank Q) : ¬ IsCyclic Q := by
  obtain ⟨E, hEQ, hE, hcard⟩ := exists_isElemAbelian_of_le_rank hp hQp h2
  intro hcyc
  have hEcyc : IsCyclic E := by
    have : IsCyclic (E.subgroupOf Q) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe hEQ).isCyclic.mp this
  have h1 : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE.2 x x.2)
  rw [IsCyclic.exponent_eq_card] at h1
  have h3 := Nat.le_of_dvd hp.pos h1
  have := hp.one_lt
  nlinarith

theorem omegaOneCenter_le_of_rank_le {P Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQp : IsPGroup p Q) (hPQ : P ≤ Q) (hrank : rank Q ≤ rank P) : omegaOneCenter Q p ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  intro z hz
  by_contra hzP
  have hPp : IsPGroup p P := hQp.to_le hPQ
  rw [rank_eq_pRank_of_isPGroup hp hPp, rank_eq_pRank_of_isPGroup hp hQp] at hrank
  obtain ⟨E, hEP, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt P
  have hzE : z ∉ E := fun h => hzP (hEP h)
  have hZ : CFSG.Open.IsElemAbelian p (Subgroup.zpowers z) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self z i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        pow_eq_one_of_mem_omegaOneCenter hz, one_zpow]
  have hEz : E ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq']
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer Q p hz)) e
      (hPQ (hEP he)))
  have hE' := isElemAbelian_sup hE hZ hEz
  have hlt : E < E ⊔ Subgroup.zpowers z :=
    lt_of_le_of_ne le_sup_left fun h => hzE (h ▸ (le_sup_right : Subgroup.zpowers z ≤ _)
      (Subgroup.mem_zpowers z))
  have hE'Q : E ⊔ Subgroup.zpowers z ≤ Q :=
    sup_le (hEP.trans hPQ) (Subgroup.zpowers_le.mpr (omegaOneCenter_le Q p hz))
  have hge := card_ge_of_lt' hp (hQp.to_le hE'Q) hlt
  obtain ⟨k, hk⟩ := (hQp.to_le hE'Q).exists_card_eq
  have hkr := le_rank hp hE'Q hE' hk
  rw [rank_eq_pRank_of_isPGroup hp hQp] at hkr
  rw [hcard, hk, ← pow_succ'] at hge
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hge
  omega

theorem exists_noncyclic_exponent_le {Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQp : IsPGroup p Q) (hQ : ¬ IsCyclic Q) :
    ∃ X ≤ Q, ¬ IsCyclic X ∧ (∀ x ∈ X, x ^ p = 1) ∧
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p Q) := ⟨hQp⟩
  obtain ⟨hcyc, hexp⟩ := CFSG.lemma_4_5_c (R := Q) (p := p) hp2 hQ
  set Z2 := Subgroup.upperCentralSeries Q 2 with hZ2
  set Ω := CFSG.omega₁ (G := Z2) (p := p) with hΩ
  set D : Subgroup Q := Ω.map Z2.subtype with hD
  have : Ω.Characteristic := CFSG.omega₁_characteristic Z2
  have : D.Characteristic := CFSG.characteristic_map_subtype_of_characteristic Z2 Ω
  refine ⟨D.map Q.subtype, Subgroup.map_subtype_le _, fun h => hcyc ?_, ?_, fun g hg => ?_⟩
  · have e1 : Ω ≃* D := Subgroup.equivMapOfInjective Ω Z2.subtype Z2.subtype_injective
    have e2 : D ≃* D.map Q.subtype :=
      Subgroup.equivMapOfInjective D Q.subtype Q.subtype_injective
    exact (e1.trans e2).isCyclic.mpr h
  · rintro _ ⟨d, ⟨ω, hω, rfl⟩, rfl⟩
    have h1 : (⟨ω, hω⟩ : Ω) ^ p = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one _
    have h2 := congrArg (fun w : Ω => (((w : Z2) : Q) : G)) h1
    simpa using h2
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_map_of_characteristic hg hy, fun hy => ?_⟩
    have := conj_mem_map_of_characteristic (Subgroup.inv_mem _ hg) hy
    simpa [mul_assoc] using this

theorem exists_commutator_mem_zpowers {𝔓 X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h𝔓 : IsPGroup p 𝔓) (hX𝔓 : X ≤ 𝔓) (hN : 𝔓 ≤ Subgroup.normalizer (X : Set G)) {z : G}
    (hz : z ∈ Subgroup.centralizer (𝔓 : Set G)) (hXz : ¬ X ≤ Subgroup.zpowers z) :
    ∃ y ∈ X, y ∉ Subgroup.zpowers z ∧ ∀ g ∈ 𝔓, ⁅y, g⁆ ∈ Subgroup.zpowers z := by
  have : Fact p.Prime := ⟨hp⟩
  set Zs : Subgroup 𝔓 := (Subgroup.zpowers z).subgroupOf 𝔓 with hZs
  have hZsn : Zs.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hn
    have hcomm : ∀ w ∈ Subgroup.zpowers z, (g : G) * w * (g : G)⁻¹ = w := by
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : (g : G) * z = z * g := (Subgroup.mem_centralizer_iff.mp hz) g g.2
      have h2 : Commute (g : G) (z ^ i) := (Commute.zpow_right h1 i)
      rw [h2.eq, mul_inv_cancel_right]
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hcomm _ hn']
    exact hn'
  have : Group.IsNilpotent (𝔓 ⧸ Zs) := (h𝔓.to_quotient Zs).isNilpotent
  set q := QuotientGroup.mk' Zs with hq
  set Xb := (X.subgroupOf 𝔓).map q with hXb
  have hXn : (X.subgroupOf 𝔓).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX𝔓).mpr hN
  have hXbn : Xb.Normal := hXn.map q (QuotientGroup.mk'_surjective Zs)
  have hXb1 : Xb ≠ ⊥ := by
    intro h
    apply hXz
    intro x hx
    have hmem : q ⟨x, hX𝔓 hx⟩ ∈ Xb := ⟨⟨x, hX𝔓 hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hmem
  obtain ⟨yb, hyb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hXb1)
  obtain ⟨⟨y, hyX, hyq⟩, hyZ⟩ := yb.2
  have hyZ' : (yb : 𝔓 ⧸ Zs) ∈ Subgroup.center (𝔓 ⧸ Zs) := hyZ
  refine ⟨y, Subgroup.mem_subgroupOf.mp hyX, fun h => hyb1 ?_, fun g hg => ?_⟩
  · apply Subtype.ext
    rw [← hyq, hq, QuotientGroup.mk'_apply, Subgroup.coe_one, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact h
  · have h1 : q ⁅y, ⟨g, hg⟩⁆ = 1 := by
      rw [map_commutatorElement, hyq, commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_center_iff.mp hyZ') (q ⟨g, hg⟩)).symm
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have hcoe : ((⁅y, ⟨g, hg⟩⁆ : 𝔓) : G) = ⁅(y : G), g⁆ := by
      simp [commutatorElement_def]
    rwa [hcoe] at h1

theorem card_le_and_commutator_le_of_commutator_mem {𝔓 Y : Subgroup G} {z x : G}
    (hz : z ∈ Subgroup.centralizer (𝔓 : Set G))
    (hx : ∀ g ∈ 𝔓, ⁅x, g⁆ ∈ Subgroup.zpowers z) (hY : Y ≤ 𝔓) :
    Nat.card Y ≤ Nat.card (Subgroup.zpowers z) *
        Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ∧
      ⁅Y, Y⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
  have hzc : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ 𝔓, g * w = w * g := by
    intro w hw g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right ((Subgroup.mem_centralizer_iff.mp hz) g hg) i).eq
  have hmem : ∀ g ∈ 𝔓, ⁅g, x⁆ ∈ Subgroup.zpowers z := by
    intro g hg
    have h := Subgroup.inv_mem _ (hx g hg)
    rwa [commutatorElement_inv] at h
  let φ : Y →* Subgroup.zpowers z :=
    { toFun := fun g => ⟨⁅(g : G), x⁆, hmem _ (hY g.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g₁ g₂ => Subtype.ext (by
        show ⁅(g₁ : G) * g₂, x⁆ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆
        have h₂ := hmem _ (hY g₂.2)
        have h₁ := hmem _ (hY g₁.2)
        have hc : (g₁ : G) * ⁅(g₂ : G), x⁆ = ⁅(g₂ : G), x⁆ * g₁ := hzc _ h₂ _ (hY g₁.2)
        have hab : ⁅(g₂ : G), x⁆ * ⁅(g₁ : G), x⁆ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆ := by
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h₁
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h₂
          rw [← hi, ← hj]
          exact (Commute.zpow_zpow_self z j i).eq
        calc ⁅(g₁ : G) * g₂, x⁆ = (g₁ : G) * ⁅(g₂ : G), x⁆ * (g₁ : G)⁻¹ * ⁅(g₁ : G), x⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅(g₂ : G), x⁆ * ⁅(g₁ : G), x⁆ := by rw [hc]; group
          _ = ⁅(g₁ : G), x⁆ * ⁅(g₂ : G), x⁆ := hab) }
  have hker : ∀ g : Y, g ∈ φ.ker ↔ (g : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    intro g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : ⁅(g : G), x⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h'
      exact h'
    · intro h
      apply Subtype.ext
      show ⁅(g : G), x⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h
  refine ⟨?_, ?_⟩
  · have h1 : Nat.card Y = Nat.card φ.ker * Nat.card φ.range := by
      rw [← φ.ker.card_mul_index, Subgroup.index_ker]
    have h2 : Nat.card φ.range ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_card_group _
    have h3 : Nat.card φ.ker = Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
      have heq : φ.ker = (Subgroup.centralizer ({x} : Set G)).subgroupOf Y := by
        ext g
        rw [hker, Subgroup.mem_subgroupOf]
      rw [heq, ← Subgroup.card_map_of_injective Y.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [h1, h3, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : φ ⁅(⟨g₁, hg₁⟩ : Y), (⟨g₂, hg₂⟩ : Y)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      apply Subtype.ext
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (φ (⟨g₁, hg₁⟩ : Y)).2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (φ (⟨g₂, hg₂⟩ : Y)).2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self z i j).eq
    have h2 := (hker _).mp h1
    have hcoe : ((⁅(⟨g₁, hg₁⟩ : Y), (⟨g₂, hg₂⟩ : Y)⁆ : Y) : G) = ⁅g₁, g₂⁆ := by
      simp [commutatorElement_def]
    rwa [hcoe] at h2

theorem exists_typePP {𝔓 X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h𝔓 : IsPGroup p 𝔓) (hX𝔓 : X ≤ 𝔓) (hN : 𝔓 ≤ Subgroup.normalizer (X : Set G))
    (hXexp : ∀ x ∈ X, x ^ p = 1) (hXcyc : ¬ IsCyclic X) {t : G} (ht : t * t = 1)
    (ht𝔓 : t ∈ Subgroup.normalizer (𝔓 : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G)) :
    ∃ z ∈ X, ∃ x ∈ X, z ≠ 1 ∧ z ∈ Subgroup.centralizer (𝔓 : Set G) ∧
      x ∉ Subgroup.zpowers z ∧ (∀ g ∈ 𝔓, ⁅x, g⁆ ∈ Subgroup.zpowers z) ∧
      t ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ∧
      t * x * t⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htt : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    rw [htinv]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group
  have hX1 : X ≠ ⊥ := fun h => hXcyc (h ▸ (inferInstance : IsCyclic (⊥ : Subgroup G)))
  set Z₁ := X ⊓ Subgroup.centralizer (𝔓 : Set G) with hZ₁
  have hZ₁1 : Z₁ ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hp h𝔓 (h𝔓.to_le hX𝔓) hN hX1
  have htZ₁ : ∀ y ∈ Z₁, t * y * t⁻¹ ∈ Z₁ := fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp htX y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp (Bender35.mem_normalizer_centralizer ht𝔓) y).mp hy.2⟩
  have hZ₁comm : ∀ a ∈ Z₁, ∀ b ∈ Z₁, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp hb.2) a (hX𝔓 ha.1))
  obtain ⟨w₀, hw₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ₁1
  have hwZ : (w₀ : G) ∈ Z₁ := w₀.2
  have hw1 : (w₀ : G) ≠ 1 := fun h => hw₀ (Subtype.ext h)
  set w := (w₀ : G) with hwdef
  obtain ⟨z, hzZ, hz1, hzt⟩ : ∃ z ∈ Z₁, z ≠ 1 ∧
      (t * z * t⁻¹ = z ∨ t * z * t⁻¹ = z⁻¹) := by
    have hw' := htZ₁ w hwZ
    by_cases hplus : w * (t * w * t⁻¹) = 1
    · by_cases hminus : w⁻¹ * (t * w * t⁻¹) = 1
      · exfalso
        have h1 : t * w * t⁻¹ = w⁻¹ := by
          calc t * w * t⁻¹ = w⁻¹ * (w * (t * w * t⁻¹)) := by group
            _ = w⁻¹ := by rw [hplus, mul_one]
        have h2 : t * w * t⁻¹ = w := by
          calc t * w * t⁻¹ = w * (w⁻¹ * (t * w * t⁻¹)) := by group
            _ = w := by rw [hminus, mul_one]
        have h3 : w * w = 1 := by
          calc w * w = w * (t * w * t⁻¹) := by rw [h2]
            _ = 1 := hplus
        exact hw1 (eq_one_of_sq_eq_one hp hp2 hXexp hwZ.1 h3)
      · refine ⟨w⁻¹ * (t * w * t⁻¹), Z₁.mul_mem (Z₁.inv_mem hwZ) hw', hminus, Or.inr ?_⟩
        calc t * (w⁻¹ * (t * w * t⁻¹)) * t⁻¹ = (t * w * t⁻¹)⁻¹ * (t * (t * w * t⁻¹) * t⁻¹) := by
              group
          _ = (t * w * t⁻¹)⁻¹ * w := by rw [htt]
          _ = (w⁻¹ * (t * w * t⁻¹))⁻¹ := by group
    · refine ⟨w * (t * w * t⁻¹), Z₁.mul_mem hwZ hw', hplus, Or.inl ?_⟩
      calc t * (w * (t * w * t⁻¹)) * t⁻¹ = (t * w * t⁻¹) * (t * (t * w * t⁻¹) * t⁻¹) := by group
        _ = (t * w * t⁻¹) * w := by rw [htt]
        _ = w * (t * w * t⁻¹) := (hZ₁comm _ hw' _ hwZ)
  have hzX : z ∈ X := hzZ.1
  have hz𝔓 : z ∈ Subgroup.centralizer (𝔓 : Set G) := hzZ.2
  have htz : t ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    have hfwd : ∀ u ∈ Subgroup.zpowers z, t * u * t⁻¹ ∈ Subgroup.zpowers z := by
      intro u hu
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rcases hzt with h | h
      · rw [h]; exact Subgroup.zpow_mem_zpowers z i
      · rw [h, inv_zpow']; exact Subgroup.zpow_mem_zpowers z (-i)
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hfwd u, fun hu => ?_⟩
    have := hfwd _ hu
    rwa [htt] at this
  have hXz : ¬ X ≤ Subgroup.zpowers z := by
    intro h
    apply hXcyc
    have : IsCyclic ((X.subgroupOf (Subgroup.zpowers z))) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe h).isCyclic.mp this
  obtain ⟨y, hyX, hyz, hy𝔓⟩ := exists_commutator_mem_zpowers hp h𝔓 hX𝔓 hN hz𝔓 hXz
  have hzc : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ 𝔓, g * w = w * g := by
    intro w hw g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right ((Subgroup.mem_centralizer_iff.mp hz𝔓) g hg) i).eq
  have hRmul : ∀ a ∈ 𝔓, ∀ b ∈ 𝔓, (∀ g ∈ 𝔓, ⁅a, g⁆ ∈ Subgroup.zpowers z) →
      (∀ g ∈ 𝔓, ⁅b, g⁆ ∈ Subgroup.zpowers z) → ∀ g ∈ 𝔓, ⁅a * b, g⁆ ∈ Subgroup.zpowers z := by
    intro a ha b hb hA hB g hg
    have h1 : ⁅a * b, g⁆ = a * ⁅b, g⁆ * a⁻¹ * ⁅a, g⁆ := by simp only [commutatorElement_def]; group
    rw [h1, hzc _ (hB g hg) a ha, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (hB g hg) (hA g hg)
  have hRinv : ∀ a ∈ 𝔓, (∀ g ∈ 𝔓, ⁅a, g⁆ ∈ Subgroup.zpowers z) →
      ∀ g ∈ 𝔓, ⁅a⁻¹, g⁆ ∈ Subgroup.zpowers z := by
    intro a ha hA g hg
    have h1 : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a := by simp only [commutatorElement_def]; group
    have h2 := hzc _ (Subgroup.inv_mem _ (hA g hg)) a⁻¹ (𝔓.inv_mem ha)
    rw [h1, h2, inv_mul_cancel_right]
    exact Subgroup.inv_mem _ (hA g hg)
  set y' := t * y * t⁻¹ with hy'
  have hy'X : y' ∈ X := (Subgroup.mem_normalizer_iff.mp htX y).mp hyX
  have hy'𝔓 : ∀ g ∈ 𝔓, ⁅y', g⁆ ∈ Subgroup.zpowers z := by
    intro g hg
    have hg' : t⁻¹ * g * t ∈ 𝔓 := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht𝔓) g).mp hg
      simpa using this
    have h1 : ⁅y', g⁆ = t * ⁅y, t⁻¹ * g * t⁆ * t⁻¹ := by
      rw [hy']; simp only [commutatorElement_def]; group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp htz _).mp (hy𝔓 _ hg')
  have hy𝔓' : y ∈ 𝔓 := hX𝔓 hyX
  have hy'𝔓' : y' ∈ 𝔓 := hX𝔓 hy'X
  by_cases hplus : y * y' ∈ Subgroup.zpowers z
  · by_cases hminus : y⁻¹ * y' ∈ Subgroup.zpowers z
    · exfalso
      apply hyz
      have h2 : y ^ 2 ∈ Subgroup.zpowers z := by
        have : y ^ 2 = (y * y') * (y⁻¹ * y')⁻¹ := by rw [pow_two]; group
        rw [this]
        exact Subgroup.mul_mem _ hplus (Subgroup.inv_mem _ hminus)
      exact mem_of_sq_mem hp hp2 hXexp hyX h2
    · refine ⟨z, hzX, y⁻¹ * y', X.mul_mem (X.inv_mem hyX) hy'X, hz1, hz𝔓, hminus,
        hRmul _ (𝔓.inv_mem hy𝔓') _ hy'𝔓' (hRinv _ hy𝔓' hy𝔓) hy'𝔓, htz, ?_⟩
      have : t * (y⁻¹ * y') * t⁻¹ = (y⁻¹ * y')⁻¹ := by
        rw [hy']
        calc t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹ = (t * y * t⁻¹)⁻¹ * (t * (t * y * t⁻¹) * t⁻¹) := by
              group
          _ = (t * y * t⁻¹)⁻¹ * y := by rw [htt]
          _ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by group
      rw [this]
      exact (le_sup_left : Subgroup.zpowers _ ≤ _) (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  · refine ⟨z, hzX, y * y', X.mul_mem hyX hy'X, hz1, hz𝔓, hplus,
      hRmul _ hy𝔓' _ hy'𝔓' hy𝔓 hy'𝔓, htz, ?_⟩
    have hc : ⁅y'⁻¹, y⁻¹⁆ ∈ Subgroup.zpowers z :=
      hRinv _ hy'𝔓' hy'𝔓 _ (𝔓.inv_mem hy𝔓')
    have : t * (y * y') * t⁻¹ = (y * y') * ⁅y'⁻¹, y⁻¹⁆ := by
      rw [hy']
      calc t * (y * (t * y * t⁻¹)) * t⁻¹ = (t * y * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹) := by group
        _ = (t * y * t⁻¹) * y := by rw [htt]
        _ = (y * (t * y * t⁻¹)) * ⁅(t * y * t⁻¹)⁻¹, y⁻¹⁆ := by
            simp only [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ ((le_sup_left : Subgroup.zpowers _ ≤ _) (Subgroup.mem_zpowers _))
      ((le_sup_right : Subgroup.zpowers z ≤ _) hc)

end CFSG.Walter
