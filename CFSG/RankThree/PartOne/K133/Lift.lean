module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.HNB.Tools

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G]

section Theta

variable (p : ℕ) (I : Subgroup G)

noncomputable abbrev thetaMk : ↥I →* ↥I ⧸ aschbacherSolvableCore p ↥I :=
  QuotientGroup.mk' _

theorem mem_theta_iff {y : G} :
    y ∈ inSubgroup (aschbacherSolvableCore p) I ↔
      ∃ hy : y ∈ I, (⟨y, hy⟩ : ↥I) ∈ aschbacherSolvableCore p ↥I := by
  unfold inSubgroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem thetaMk_eq_one_iff {y : G} (hy : y ∈ I) :
    thetaMk p I ⟨y, hy⟩ = 1 ↔ y ∈ inSubgroup (aschbacherSolvableCore p) I := by
  rw [mem_theta_iff]
  constructor
  · intro h
    exact ⟨hy, (QuotientGroup.eq_one_iff _).1 h⟩
  · rintro ⟨_, h⟩
    exact (QuotientGroup.eq_one_iff _).2 h

theorem theta_conj_mem {h n : G} (hh : h ∈ I)
    (hn : n ∈ inSubgroup (aschbacherSolvableCore p) I) :
    h * n * h⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I := by
  have hnor := (theta_le_and_normal p I).2
  have hn' : (⟨n, (theta_le_and_normal p I).1 hn⟩ : ↥I) ∈
      (inSubgroup (aschbacherSolvableCore p) I).subgroupOf I := Subgroup.mem_subgroupOf.2 hn
  exact Subgroup.mem_subgroupOf.1 (hnor.conj_mem _ hn' ⟨h, hh⟩)

theorem act_mk {g : G} (hg : g ∈ Subgroup.normalizer (I : Set G)) {y : G} (hy : y ∈ I)
    (hgy : g * y * g⁻¹ ∈ I) :
    thetaQuotientConj p I ⟨g, hg⟩ (thetaMk p I ⟨y, hy⟩) = thetaMk p I ⟨g * y * g⁻¹, hgy⟩ := by
  show thetaQuotientConj p I ⟨g, hg⟩
      ((⟨y, hy⟩ : ↥I) : ↥I ⧸ aschbacherSolvableCore p ↥I) = _
  rw [thetaQuotientConj_mk]
  rfl

theorem theta_conj_mem_of_normalizer {g n : G} (hg : g ∈ Subgroup.normalizer (I : Set G))
    (hn : n ∈ inSubgroup (aschbacherSolvableCore p) I) :
    g * n * g⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I := by
  obtain ⟨hnI, -⟩ := (mem_theta_iff p I).1 hn
  have hgn : g * n * g⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 hg n).1 hnI
  rw [← thetaMk_eq_one_iff p I hgn, ← act_mk p I hg hnI hgn, (thetaMk_eq_one_iff p I hnI).2 hn,
    map_one]

@[expose] noncomputable def hatSub (Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)) :
    Subgroup G :=
  (Sq.comap (thetaMk p I)).map I.subtype

variable {p I}

theorem mem_hatSub {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)} {y : G} :
    y ∈ hatSub p I Sq ↔ ∃ hy : y ∈ I, thetaMk p I ⟨y, hy⟩ ∈ Sq := by
  unfold hatSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem hatSub_le {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)} : hatSub p I Sq ≤ I :=
  fun _ hy => (mem_hatSub.1 hy).1

theorem theta_le_hatSub {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)} :
    inSubgroup (aschbacherSolvableCore p) I ≤ hatSub p I Sq := by
  intro y hy
  obtain ⟨hyI, -⟩ := (mem_theta_iff p I).1 hy
  refine mem_hatSub.2 ⟨hyI, ?_⟩
  rw [(thetaMk_eq_one_iff p I hyI).2 hy]
  exact Sq.one_mem

theorem mem_normalizer_hatSub {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)} {g : G}
    (hg : g ∈ Subgroup.normalizer (I : Set G))
    (hS : ∀ x, thetaQuotientConj p I ⟨g, hg⟩ x ∈ Sq ↔ x ∈ Sq) :
    g ∈ Subgroup.normalizer (hatSub p I Sq : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hI : y ∈ I ↔ g * y * g⁻¹ ∈ I := Subgroup.mem_normalizer_iff.1 hg y
  constructor
  · intro hy
    obtain ⟨hyI, hyS⟩ := mem_hatSub.1 hy
    have hgy : g * y * g⁻¹ ∈ I := hI.1 hyI
    refine mem_hatSub.2 ⟨hgy, ?_⟩
    rw [← act_mk p I hg hyI hgy]
    exact (hS _).2 hyS
  · intro hy
    obtain ⟨hgy, hyS⟩ := mem_hatSub.1 hy
    have hyI : y ∈ I := hI.2 hgy
    refine mem_hatSub.2 ⟨hyI, ?_⟩
    refine (hS _).1 ?_
    rw [act_mk p I hg hyI hgy]
    exact hyS

end Theta

section Lift

variable [Finite G] {p : ℕ} {I : Subgroup G}

theorem not_dvd_card_hatSub (hp : p.Prime) (hp2 : p ≠ 2)
    {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)} (hS2 : IsPGroup 2 Sq) :
    ¬ p ∣ Nat.card (hatSub p I Sq) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨hxI, hxS⟩ := mem_hatSub.1 x.2
  have hxp : (x : G) ^ p = 1 := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hx] at h1
    exact congrArg Subtype.val h1
  set z : ↥Sq := ⟨thetaMk p I ⟨x, hxI⟩, hxS⟩ with hz
  have hzp : z ^ p = 1 := by
    apply Subtype.ext
    show thetaMk p I ⟨x, hxI⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x, hxI⟩ : ↥I) ^ p = 1 := Subtype.ext hxp
    rw [this, map_one]
  obtain ⟨k, hk⟩ := hS2 z
  have hz1 : z = 1 := by
    have hd1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have : orderOf z = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
    exact orderOf_eq_one_iff.1 this
  have hxθ : (x : G) ∈ inSubgroup (aschbacherSolvableCore p) I := by
    rw [← thetaMk_eq_one_iff p I hxI]
    exact congrArg Subtype.val hz1
  apply (theta_solvable_and_not_dvd hp I).2
  have hord : orderOf (⟨x, hxθ⟩ : ↥(inSubgroup (aschbacherSolvableCore p) I)) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
  have := orderOf_dvd_natCard (⟨x, hxθ⟩ : ↥(inSubgroup (aschbacherSolvableCore p) I))
  rwa [hord] at this

theorem exists_mul_of_sylow {Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I)}
    (hS2 : IsPGroup 2 Sq) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (hatSub p I Sq)) :
    ∀ y ∈ hatSub p I Sq, ∃ r ∈ R, ∃ n ∈ inSubgroup (aschbacherSolvableCore p) I, y = r * n := by
  classical
  set H := hatSub p I Sq with hH
  set θ := inSubgroup (aschbacherSolvableCore p) I with hθ
  obtain ⟨Q, rfl⟩ := hR
  have hNnormal : (θ.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using theta_conj_mem p I (hatSub_le g.2) hn⟩
  have hQ2 : IsPGroup 2 (↥H ⧸ θ.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨hyI, hyS⟩ := mem_hatSub.1 y.2
      obtain ⟨k, hk⟩ := hS2 (⟨thetaMk p I ⟨y, hyI⟩, hyS⟩ : ↥Sq)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have h1 : thetaMk p I ⟨y, hyI⟩ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [← map_pow] at h1
      have h3 := (thetaMk_eq_one_iff p I (I.pow_mem hyI (2 ^ k))).1 h1
      simpa using h3
  have hf : Function.Surjective (QuotientGroup.mk' (θ.subgroupOf H)) :=
    QuotientGroup.mk'_surjective _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := (Q.mapSurjective hf).is_maximal' (Q := ⊤)
    (hQ2.to_subgroup ⊤) le_top
  intro y hy
  have hyq : (QuotientGroup.mk' (θ.subgroupOf H)) ⟨y, hy⟩ ∈
      ((Q.mapSurjective hf : Sylow 2 (↥H ⧸ θ.subgroupOf H)) : Subgroup (↥H ⧸ θ.subgroupOf H)) := by
    rw [← hmax]
    exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hyq
  obtain ⟨r, hrQ, hr⟩ := Subgroup.mem_map.1 hyq
  have hrn := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hr)
  refine ⟨(r : G), Subgroup.mem_map.2 ⟨r, hrQ, rfl⟩, (r : G)⁻¹ * y, ?_, by group⟩
  simpa using hrn

omit [Finite G] in
theorem le_normalizer_commutator' (H P Q : Subgroup G)
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh)]

omit [Finite G] in
theorem thetaMk_mul_theta {r n : G} (hr : r ∈ I)
    (hn : n ∈ inSubgroup (aschbacherSolvableCore p) I) (hrn : r * n ∈ I) :
    thetaMk p I ⟨r * n, hrn⟩ = thetaMk p I ⟨r, hr⟩ := by
  obtain ⟨hnI, -⟩ := (mem_theta_iff p I).1 hn
  have : (⟨r * n, hrn⟩ : ↥I) = ⟨r, hr⟩ * ⟨n, hnI⟩ := rfl
  rw [this, map_mul, (thetaMk_eq_one_iff p I hnI).2 hn, mul_one]

variable (p I) in
@[expose] def MovesTwoQuot (g : G) : Prop :=
  ∃ hg : g ∈ Subgroup.normalizer (I : Set G),
    ∃ Sq : Subgroup (↥I ⧸ aschbacherSolvableCore p ↥I), IsPGroup 2 Sq ∧
      (∀ x, thetaQuotientConj p I ⟨g, hg⟩ x ∈ Sq ↔ x ∈ Sq) ∧
      ∃ x ∈ Sq, thetaQuotientConj p I ⟨g, hg⟩ x ≠ x

theorem exists_invariant_two_subgroup (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) {b : G} (hbE : b ∈ E) (hmov : MovesTwoQuot p I b) :
    ∃ T : Subgroup G, T ≤ I ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      Subgroup.zpowers b ⊔ thetaQuotientCentralizer p E I ≤ Subgroup.normalizer (T : Set G) ∧
      ⁅T, Subgroup.zpowers b⁆ = T := by
  classical
  obtain ⟨hbN, Sq, hS2, hSstab, x, hxS, hxmov⟩ := hmov
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbp : b ^ p = 1 := by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian b hbE
  set D := thetaQuotientCentralizer p E I with hD
  have hDE : D ≤ E := fun d hd => (mem_thetaQuotientCentralizer_iff.1 hd).1
  have hPE : Subgroup.zpowers b ⊔ D ≤ E := sup_le (Subgroup.zpowers_le.2 hbE) hDE
  have hPp : IsPGroup p (Subgroup.zpowers b ⊔ D : Subgroup G) :=
    (IsElementaryAbelian.isPGroup p E).to_le hPE
  have hbH : b ∈ Subgroup.normalizer (hatSub p I Sq : Set G) :=
    mem_normalizer_hatSub hbN hSstab
  have hDH : D ≤ Subgroup.normalizer (hatSub p I Sq : Set G) := fun d hd => by
    obtain ⟨-, hdN, hdθ⟩ := mem_thetaQuotientCentralizer_iff.1 hd
    have hone : thetaQuotientConj p I ⟨d, hdN⟩ = 1 :=
      (thetaQuotientConj_eq_one_iff p I ⟨d, hdN⟩).2 hdθ
    exact mem_normalizer_hatSub hdN (fun y => by rw [hone, MulAut.one_apply])
  have hPH : Subgroup.zpowers b ⊔ D ≤ Subgroup.normalizer (hatSub p I Sq : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hbH) hDH
  have hbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  obtain ⟨R, hRsyl, -, hPR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime hp
    Nat.prime_two hPp hPH (not_dvd_card_hatSub hp hp2 hS2) bot_le
    (IsPGroup.of_card (n := 0) (by simp)) (by rw [hbot]; exact le_top)
  obtain ⟨hRle, hRp⟩ : R ≤ hatSub p I Sq ∧ IsPGroup 2 R := by
    obtain ⟨Q, rfl⟩ := hRsyl
    exact ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _⟩
  have hbR : Subgroup.zpowers b ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hPR
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hPR
  have hTR : ⁅R, Subgroup.zpowers b⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.1 hbR
  refine ⟨⁅R, Subgroup.zpowers b⁆, hTR.trans (hRle.trans hatSub_le), ?_, hRp.to_le hTR, ?_, ?_⟩
  · intro hT
    have hcent : R ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hT
    have hbr : ∀ r ∈ R, b * r = r * b := fun r hr =>
      Subgroup.mem_centralizer_iff.1 (hcent hr) b (Subgroup.mem_zpowers b)
    obtain ⟨z, hzx⟩ := QuotientGroup.mk_surjective x
    have hzS : thetaMk p I z ∈ Sq := by
      have : thetaMk p I z = x := hzx
      rw [this]
      exact hxS
    have hy : (z : G) ∈ hatSub p I Sq := mem_hatSub.2 ⟨z.2, by simpa using hzS⟩
    obtain ⟨r, hr, n, hn, hrn⟩ := exists_mul_of_sylow hS2 hRsyl _ hy
    have hrI : r ∈ I := hatSub_le (hRle hr)
    have hbn : b * n * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I :=
      theta_conj_mem_of_normalizer p I hbN hn
    have hnI : n ∈ I := ((mem_theta_iff p I).1 hn).1
    have hbnI : b * n * b⁻¹ ∈ I := ((mem_theta_iff p I).1 hbn).1
    have hgz : b * (z : G) * b⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 hbN _).1 z.2
    have hreq : b * (z : G) * b⁻¹ = r * (b * n * b⁻¹) := by
      rw [hrn]
      calc b * (r * n) * b⁻¹ = (b * r * b⁻¹) * (b * n * b⁻¹) := by group
        _ = r * (b * n * b⁻¹) := by rw [hbr r hr]; group
    apply hxmov
    rw [← hzx]
    have hact := act_mk p I hbN z.2 hgz
    have e1 : (⟨b * (z : G) * b⁻¹, hgz⟩ : ↥I) = ⟨r * (b * n * b⁻¹), hreq ▸ hgz⟩ :=
      Subtype.ext hreq
    have e2 : z = ⟨r * n, hrn ▸ z.2⟩ := Subtype.ext hrn
    show thetaQuotientConj p I ⟨b, hbN⟩ (thetaMk p I z) = thetaMk p I z
    have hz' : thetaMk p I ⟨(z : G), z.2⟩ = thetaMk p I z := rfl
    rw [← hz', hact, e1, thetaMk_mul_theta hrI hbn, hz']
    conv_rhs => rw [e2]
    exact (thetaMk_mul_theta hrI hn _).symm
  · exact sup_le (Subgroup.normalizer_commutator_ge_right R (Subgroup.zpowers b))
      (le_normalizer_commutator' D R (Subgroup.zpowers b) hDR (fun d hd =>
        HNB.mem_normalizer_zpowers_of_commute
          (congrArg Subtype.val (hE.is_comm.comm ⟨d, hDE hd⟩ ⟨b, hbE⟩))))
  · have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers b)) (Nat.card R) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hRp
      rw [Nat.card_zpowers, hm]
      have hord : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hbp
      exact Nat.Coprime.pow_right m (Nat.Coprime.coprime_dvd_left hord
        ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
    have : Group.IsNilpotent R := hRp.isNilpotent
    exact HNB.commutator_double_eq_self_of_coprime_solvable (Subgroup.zpowers b) R hbR hcop
      inferInstance

end Lift

end CFSG.RankThree.PartOne.K133
